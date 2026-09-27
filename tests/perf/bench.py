#!/usr/bin/env python3
"""Compile-performance harness for the KRS definition pipeline.

Measures `krs check|emit-k|build` and isolated Cargo stages
over the KWasm, KMIR, and KEVM semantics ports, in a matrix of stages and
scenarios, and writes one versioned receipt per measured run.

    python3 tests/perf/bench.py --list
    python3 tests/perf/bench.py --dry-run [--port P] [--stage S] [--scenario C]
    python3 tests/perf/bench.py [--port P ...] [--stage S ...] [--scenario C ...] [--runs N]
    python3 tests/perf/bench.py summary RECEIPTS...
    python3 tests/perf/bench.py compare A B

See `tests/perf/README.md` for the stages, scenarios, receipt schema, and the
comparison rule.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Callable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.pins import load_toml  # noqa: E402
from perf import compare, measure, receipts  # noqa: E402
from perf import sample  # noqa: E402
from perf import rustc_profile  # noqa: E402


HERE = Path(__file__).resolve().parent
MATRIX = HERE / "matrix.toml"
SELF = Path(__file__).resolve()


@dataclass(frozen=True)
class Stage:
    name: str
    description: str
    krs_command: str | None = None
    """The `krs` subcommand, or None for an isolated Cargo stage."""
    output: bool = False


STAGES: dict[str, Stage] = {
    stage.name: stage
    for stage in (
        Stage("krs-check", "`krs check`: collector build and run, lowering, checks",
              krs_command="check"),
        Stage("krs-emit-k", "`krs emit-k`: collector build and run, lowering, K and JSON emission",
              krs_command="emit-k", output=True),
        Stage("krs-build", "`krs build`: collector build and run, lowering, k-rust native frontend",
              krs_command="build", output=True),
        Stage("cargo-check", "isolated host-target `cargo check` of the semantics crate"),
        Stage("collector-build", "isolated `cargo build --timings` of the generated collector package"),
    )
}

SCENARIOS: dict[str, str] = {
    "cold": "empty Cargo target per repetition",
    "warm": "dependencies built; the semantics crate cleaned (`cargo clean -p`) before each repetition",
    "no-op": "fully built target, no source change",
    "touch": "fully built target, semantics `lib.rs` mtime updated",
    "edit-rule": "fully built target, one rule-body token changed (alternately applied and reverted)",
    "edit-enum": "fully built target, one constructor-enum token changed (alternately applied and reverted)",
}

# Environment variables that change what Cargo or rustc does. They are removed
# from every measured and preparatory command so that ambient shell state
# cannot leak into a receipt; `--env KEY=VALUE` sets one back explicitly and
# is recorded in every receipt as an override.
STRIPPED_VARIABLES = re.compile(
    r"^(RUSTC_WRAPPER|RUSTC_WORKSPACE_WRAPPER|RUSTC_BOOTSTRAP|RUSTFLAGS|RUSTDOCFLAGS|"
    r"CARGO_ENCODED_RUSTFLAGS|CARGO_INCREMENTAL|CARGO_TARGET_DIR|CARGO_BUILD_.*|CARGO_PROFILE_.*|"
    r"CARGO_LOG|RUSTUP_TOOLCHAIN|CARGO_UNSTABLE_.*)$"
)


@dataclass(frozen=True)
class Profile:
    """A profiling mode: the only place `RUSTC_BOOTSTRAP` may enter a command.

    A profile supplies extra environment for its stages and marks its
    receipts `profiling = true`, which `compare` never sets against
    unprofiled receipts. The rustc profiling mode registers itself here.
    """

    name: str
    stages: tuple[str, ...]
    environment: Callable[["Context"], dict[str, str]]
    wrap: Callable[["Context", list[str], str], list[str]] | None = None
    """Rewrites a measured command (given the receipt name), e.g. to run it under a sampler."""
    collect: Callable[["Context", str], dict[str, Any]] | None = None
    """Called after a measured run; its value is the receipt's `receipt_field`."""
    receipt_field: str = "sampled_profile"


PROFILES: dict[str, Profile] = {}
PROFILES[sample.NAME] = Profile(sample.NAME, sample.STAGES, sample.environment, sample.wrap, sample.collect)
for _name, _keep_trace in (("rustc", False), ("rustc-trace", True)):
    PROFILES[_name] = Profile(_name, rustc_profile.STAGES, rustc_profile.environment_for, rustc_profile.wrap,
                              rustc_profile.make_collect(_keep_trace), "rustc_profile")


@dataclass
class Port:
    key: str
    label: str
    source: str
    edits: dict[str, dict[str, str]]

    @property
    def package(self) -> str:
        return f"krs-{self.key}-semantics"


def load_ports() -> dict[str, Port]:
    matrix = load_toml(MATRIX)
    if matrix.get("schema") != 1:
        raise GateError(f"{MATRIX.name}: unsupported schema {matrix.get('schema')!r}")
    ports = {}
    for entry in matrix.get("port", []):
        port = Port(str(entry["key"]), str(entry["label"]), str(entry["source"]), dict(entry.get("edits", {})))
        for scenario in ("edit-rule", "edit-enum"):
            if scenario not in port.edits:
                raise GateError(f"{MATRIX.name}: port {port.key} lacks the {scenario} edit")
        ports[port.key] = port
    return ports


def apply_edit(text: str, old: str, new: str, *, label: str) -> str:
    if text.count(old) != 1:
        raise GateError(f"{label}: edit anchor occurs {text.count(old)} times, expected once: {old!r}")
    return text.replace(old, new, 1)


# --- the scratch workspace ------------------------------------------------------


@dataclass
class Context:
    arguments: argparse.Namespace
    run_id: str
    work: Path
    receipts_dir: Path
    environment: dict[str, str]
    overrides: dict[str, str]
    stripped: list[str]
    host_triple: str
    krs: Path | None
    krs_flags: dict[str, bool]
    meter: measure.Meter
    base: dict[str, Any]
    collectors: dict[str, Path] = field(default_factory=dict)
    failures: list[str] = field(default_factory=list)
    written: int = 0

    @property
    def semantics(self) -> Path:
        return self.work / "semantics"

    def manifest(self) -> Path:
        return self.semantics / "Cargo.toml"

    def source(self, port: Port) -> Path:
        return self.semantics / port.key / port.source


def copy_semantics(destination: Path) -> None:
    """Copy the semantics workspace sources (no targets) with absolute KRS crate paths."""

    source = ROOT / "semantics"
    destination.mkdir(parents=True)
    for name in ("Cargo.toml", "Cargo.lock"):
        shutil.copy2(source / name, destination / name)
    members = load_toml(source / "Cargo.toml")["workspace"]["members"]
    for member in members:
        shutil.copytree(source / member, destination / member, ignore=shutil.ignore_patterns("target"))
        manifest = destination / member / "Cargo.toml"
        text = manifest.read_text(encoding="utf-8")
        manifest.write_text(text.replace('path = "../../crates/', f'path = "{ROOT / "crates"}/'), encoding="utf-8")


def base_environment(overrides: Mapping[str, str]) -> tuple[dict[str, str], list[str]]:
    from support.tools import z3_environment

    environment = {key: value for key, value in os.environ.items() if not STRIPPED_VARIABLES.match(key)}
    stripped = sorted(key for key in os.environ if STRIPPED_VARIABLES.match(key))
    environment.pop(measure.SCOPE_VARIABLE, None)
    environment.update(z3_environment())
    environment.update({"CARGO_NET_OFFLINE": "true", "RUSTUP_TOOLCHAIN": "stable", "LC_ALL": "C"})
    environment.update(overrides)
    return environment, stripped


def build_krs(environment: Mapping[str, str]) -> Path:
    """Build the release `krs` from this checkout into a persistent scratch target."""

    from support.tools import checkout_scratch

    target = Path(os.environ.get("KRS_PERF_KRS_TARGET", os.fspath(checkout_scratch() / "perf-krs-target")))
    print(f"building release krs into {target}", flush=True)
    completed = subprocess.run(
        ["cargo", "+stable", "build", "--release", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        cwd=ROOT,
        env={**environment, "CARGO_TARGET_DIR": os.fspath(target)},
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise GateError(f"building krs failed:\n{completed.stderr[-4000:]}")
    return target / "release/krs"


def krs_flags(krs: Path, environment: Mapping[str, str]) -> dict[str, bool]:
    """Which optional measurement flags this `krs` accepts, from its usage text."""

    completed = subprocess.run([krs, "--help"], env=dict(environment), capture_output=True, text=True, check=False)
    usage = completed.stdout + completed.stderr
    return {"timings": "--timings" in usage, "counters": "--counters" in usage}


def generate_collector(context: Context, port: Port) -> Path:
    """Generate the port's collector package without building it.

    `krs expand` writes the generated collector and then builds it with
    `cargo build`; a `cargo` shim ahead on PATH forwards every other Cargo
    command and stops at `build`, so the package is written in seconds.
    """

    if port.key in context.collectors:
        return context.collectors[port.key]
    assert context.krs is not None
    shim = context.work / "cargo-shim"
    shim.mkdir(exist_ok=True)
    real = shutil.which("cargo", path=context.environment.get("PATH"))
    if real is None:
        raise GateError("cargo is not on PATH")
    script = shim / "cargo"
    script.write_text(
        "#!/bin/sh\n"
        'if [ "$1" = build ]; then echo "krs-perf: collector generated; not building it" >&2; exit 97; fi\n'
        f'exec "{real}" "$@"\n',
        encoding="utf-8",
    )
    script.chmod(0o755)
    target = context.work / "targets" / f"{port.key}-generate"
    environment = {
        **context.environment,
        "CARGO_TARGET_DIR": os.fspath(target),
        "PATH": os.pathsep.join([os.fspath(shim), context.environment.get("PATH", "")]),
    }
    completed = subprocess.run(
        [context.krs, "expand", "--manifest-path", context.manifest(), "--package", port.package,
         "--definition", "main"],
        cwd=ROOT, env=environment, capture_output=True, text=True, check=False, timeout=600,
    )
    generated = sorted((target / "krs/collectors").glob("*/Cargo.toml"))
    if len(generated) != 1:
        raise GateError(
            f"collector generation for {port.key} produced {len(generated)} packages "
            f"(krs exit {completed.returncode}): {completed.stderr[-2000:]}"
        )
    destination = context.work / f"collector-{port.key}"
    shutil.copytree(generated[0].parent, destination)
    shutil.rmtree(target, ignore_errors=True)
    context.collectors[port.key] = destination
    return destination


def stage_command(
    context: Context, port: Port, stage: Stage, *, output: Path | None, timings: Path | None,
) -> tuple[list[str], Path]:
    if stage.krs_command is not None:
        assert context.krs is not None
        argv = [os.fspath(context.krs), stage.krs_command, "--manifest-path", os.fspath(context.manifest()),
                "--package", port.package, "--definition", "main"]
        if stage.output:
            assert output is not None
            argv += ["--output", os.fspath(output)]
        if timings is not None and context.krs_flags.get("timings"):
            argv += ["--timings", os.fspath(timings)]
        if timings is not None and context.krs_flags.get("counters"):
            argv += ["--counters", os.fspath(counters_path(timings))]
        return argv, ROOT
    if stage.name == "cargo-check":
        return [
            "cargo", "+stable", "check", "--manifest-path", os.fspath(context.manifest()), "-p", port.package,
            "--target", context.host_triple, "--message-format", "json", "--offline", "--timings",
        ], ROOT
    collector = generate_collector(context, port)
    return ["cargo", "+stable", "build", "--manifest-path", os.fspath(collector / "Cargo.toml"),
            "--timings", "--offline"], collector


def counters_path(timings: Path) -> Path:
    return timings.with_name(timings.name.replace(".krs-timings.json", ".krs-counters.json"))


def clean_semantics(context: Context, port: Port, stage: Stage, target: Path, environment: Mapping[str, str]) -> None:
    """Remove the semantics crate's artifacts only, for the warm scenario."""

    if stage.name == "collector-build":
        manifest = generate_collector(context, port) / "Cargo.toml"
    else:
        manifest = context.manifest()
    variants: list[list[str]] = [["--target", context.host_triple]]
    if stage.krs_command is not None:
        variants.append([])
    for extra in variants:
        subprocess.run(
            ["cargo", "+stable", "clean", "--offline", "-p", port.package, "--manifest-path", os.fspath(manifest), *extra],
            cwd=ROOT, env={**environment, "CARGO_TARGET_DIR": os.fspath(target)},
            capture_output=True, check=True, timeout=600,
        )


# --- one cell -----------------------------------------------------------------------


@dataclass
class CellState:
    built: bool = False
    stale: bool = False
    edited: str | None = None
    finished_at: float = 0.0


def run_cell(context: Context, port: Port, stage: Stage, scenarios: Sequence[str]) -> None:
    arguments = context.arguments
    target = context.work / "targets" / f"{port.key}-{stage.name}"
    source = context.source(port)
    original = source.read_text(encoding="utf-8")
    state = CellState()
    environment = {**context.environment, "CARGO_TARGET_DIR": os.fspath(target)}
    profile = PROFILES.get(arguments.profile)
    if profile is not None:
        environment.update(profile.environment(context))

    def unmeasured(label: str) -> None:
        output = context.work / "out" / "settle"
        shutil.rmtree(output, ignore_errors=True)
        argv, cwd = stage_command(context, port, stage, output=output, timings=None)
        log = context.receipts_dir / "logs" / f"{port.key}.{stage.name}.{label}.log"
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("wb") as handle:
            completed = subprocess.run(argv, cwd=cwd, env=environment, stdout=handle, stderr=subprocess.STDOUT,
                                       timeout=arguments.timeout, check=False)
        shutil.rmtree(output, ignore_errors=True)
        if completed.returncode != 0:
            raise GateError(f"{port.key}/{stage.name}: preparatory {label} run failed ({completed.returncode}); see {log}")
        state.built, state.stale, state.finished_at = True, False, time.monotonic()

    def ensure_built() -> None:
        if not state.built or state.stale:
            unmeasured("settle")

    def set_edit(scenario: str | None) -> None:
        text = original
        if scenario is not None:
            edit = port.edits[scenario]
            text = apply_edit(original, edit["old"], edit["new"], label=f"{port.key} {scenario}")
        source.write_text(text, encoding="utf-8")
        state.edited = scenario

    def measured(scenario: str, repetition: int, detail: dict[str, Any]) -> None:
        name = f"{port.key}.{stage.name}.{scenario}.{repetition}"
        output = context.work / "out" / name
        timings = context.receipts_dir / "timings" / f"{name}.krs-timings.json"
        timings.parent.mkdir(parents=True, exist_ok=True)
        argv, cwd = stage_command(context, port, stage, output=output, timings=timings)
        if profile is not None and profile.wrap is not None:
            argv = profile.wrap(context, argv, name)
        shutil.rmtree(target / "cargo-timings", ignore_errors=True)
        load_before = receipts.load_average()
        started = receipts.utc_now()
        result = context.meter.run(argv, cwd=cwd, environment=environment,
                                   log=context.receipts_dir / "logs" / f"{name}.log", timeout=arguments.timeout)
        state.finished_at = time.monotonic()
        shutil.rmtree(output, ignore_errors=True)
        if stage.krs_command is not None and context.krs_flags.get("timings"):
            timings_status, timings_doc = receipts.ingest_timings(timings)
        else:
            timings_status, timings_doc = "unsupported" if stage.krs_command else "not-applicable", None
        if stage.krs_command is not None and context.krs_flags.get("counters"):
            counters_status, counters_doc = receipts.ingest_counters(counters_path(timings))
        else:
            counters_status, counters_doc = "unsupported" if stage.krs_command else "not-applicable", None
        cargo = None
        if stage.krs_command is None:
            cargo = receipts.collect_cargo_timings(
                target, context.receipts_dir / "cargo" / f"{name}.cargo-timing.html", [port.package])
        receipt = {
            **context.base,
            "created": started,
            "port": port.key,
            "package": port.package,
            "stage": stage.name,
            "scenario": scenario,
            "repetition": repetition,
            "scenario_detail": detail,
            "command": {"argv": argv, "cwd": os.fspath(cwd), "target": os.fspath(target)},
            "exit_status": result.exit_status,
            "timed_out": result.timed_out,
            "wall_seconds": round(result.wall_seconds, 6),
            "user_seconds": None if result.user_seconds is None else round(result.user_seconds, 6),
            "sys_seconds": None if result.sys_seconds is None else round(result.sys_seconds, 6),
            "peak_memory_bytes": result.peak_memory_bytes,
            "measurement_method": result.method,
            "load_average": {"before": load_before, "after": receipts.load_average()},
            "krs_timings_status": timings_status,
            "krs_timings": timings_doc,
            "krs_counters_status": counters_status,
            "krs_counters": counters_doc,
            "cargo_timings": cargo,
            "log": f"logs/{name}.log",
        }
        if profile is not None and profile.collect is not None:
            receipt[profile.receipt_field] = profile.collect(context, name)
        receipts.write(receipt, context.receipts_dir / f"{name}.json")
        context.written += 1
        peak = "n/a" if result.peak_memory_bytes is None else f"{result.peak_memory_bytes / 2**30:.2f}GiB"
        print(f"  {name}: exit={result.exit_status} wall={result.wall_seconds:.2f}s "
              f"cpu={(result.user_seconds or 0) + (result.sys_seconds or 0):.2f}s peak={peak} "
              f"timings={timings_status} counters={counters_status}", flush=True)
        if result.exit_status != 0:
            context.failures.append(f"{name} exited {result.exit_status}")
        else:
            state.built, state.stale = True, False

    runs = arguments.runs
    try:
        for scenario in scenarios:
            count = arguments.cold_runs if scenario == "cold" and arguments.cold_runs else runs
            if scenario == "cold":
                for repetition in range(1, count + 1):
                    shutil.rmtree(target, ignore_errors=True)
                    measured(scenario, repetition, {"target": "empty"})
                continue
            ensure_built()
            for repetition in range(1, count + 1):
                detail: dict[str, Any] = {}
                if scenario == "touch":
                    # Cargo compares source mtimes with its dep-info; keep them apart.
                    time.sleep(max(0.0, 1.1 - (time.monotonic() - state.finished_at)))
                    os.utime(source)
                elif scenario in ("edit-rule", "edit-enum"):
                    time.sleep(max(0.0, 1.1 - (time.monotonic() - state.finished_at)))
                    applying = state.edited != scenario
                    set_edit(scenario if applying else None)
                    detail = {"edit": scenario, "direction": "apply" if applying else "revert",
                              "description": port.edits[scenario].get("description")}
                elif scenario == "warm":
                    clean_semantics(context, port, stage, target, environment)
                    detail = {"cleaned": port.package}
                measured(scenario, repetition, detail)
            if state.edited is not None:
                set_edit(None)
                state.stale = True
    finally:
        if source.read_text(encoding="utf-8") != original:
            source.write_text(original, encoding="utf-8")
        if not arguments.keep:
            shutil.rmtree(target, ignore_errors=True)


# --- selection, listing, dry run -------------------------------------------------------


def selection(arguments: argparse.Namespace, ports: Mapping[str, Port]) -> list[tuple[Port, Stage, list[str]]]:
    chosen_ports = arguments.port or list(ports)
    chosen_stages = arguments.stage or list(STAGES)
    chosen_scenarios = [s for s in SCENARIOS if s in (arguments.scenario or list(SCENARIOS))]
    for name in chosen_ports:
        if name not in ports:
            raise GateError(f"unknown port {name!r}; known: {', '.join(ports)}")
    profile = PROFILES.get(arguments.profile)
    cells = []
    for port_name in chosen_ports:
        for stage_name in chosen_stages:
            if profile is not None and stage_name not in profile.stages:
                continue
            cells.append((ports[port_name], STAGES[stage_name], chosen_scenarios))
    return cells


def list_matrix(ports: Mapping[str, Port]) -> None:
    print("ports:")
    for port in ports.values():
        print(f"  {port.key:<16} {port.label} ({port.package})")
    print("stages:")
    for stage in STAGES.values():
        print(f"  {stage.name:<16} {stage.description}")
    print("scenarios:")
    for name, description in SCENARIOS.items():
        print(f"  {name:<16} {description}")
    print("profiles:")
    print("  none             unprofiled measurement (default)")
    for name in PROFILES:
        print(f"  {name}")


def dry_run(arguments: argparse.Namespace, ports: Mapping[str, Port]) -> None:
    for port in ports.values():
        text = (ROOT / "semantics" / port.key / port.source).read_text(encoding="utf-8")
        for scenario, edit in port.edits.items():
            apply_edit(text, edit["old"], edit["new"], label=f"{port.key} {scenario}")
    cells = selection(arguments, ports)
    rows = 0
    total_runs = 0
    print(f"matrix ({len(cells)} port/stage cells); scratch copies under <checkout-scratch>/perf-work/<run-id>")
    for port, stage, scenarios in cells:
        for scenario in scenarios:
            count = arguments.cold_runs if scenario == "cold" and arguments.cold_runs else arguments.runs
            if stage.krs_command:
                command = (f"krs {stage.krs_command} --manifest-path <work>/semantics/Cargo.toml "
                           f"--package {port.package} --definition main"
                           + (" --output <out>" if stage.output else "") + " [--timings <file>]")
            elif stage.name == "cargo-check":
                command = (f"cargo +stable check --manifest-path <work>/semantics/Cargo.toml -p {port.package} "
                           "--target <host> --message-format json --offline --timings")
            else:
                command = "cargo +stable build --manifest-path <work>/collector-<port>/Cargo.toml --timings --offline"
            prep = SCENARIOS[scenario]
            if scenario.startswith("edit-"):
                prep += f"; {port.edits[scenario].get('description')}"
            print(f"  {port.key:<5} {stage.name:<16} {scenario:<10} runs={count}  {command}")
            print(f"        prepare: {prep}")
            rows += 1
            total_runs += count
    print(f"{rows} matrix rows, {total_runs} measured runs; edit anchors verified against semantics/")
    print("environment: CARGO_NET_OFFLINE=true RUSTUP_TOOLCHAIN=stable, Z3 library paths from tests/support; "
          "ambient Cargo/rustc build variables stripped; overrides: "
          + (" ".join(arguments.env) if arguments.env else "none"))


# --- concurrency guard ------------------------------------------------------------------


def ancestors() -> set[int]:
    pids = set()
    pid = os.getpid()
    while pid > 1 and pid not in pids:
        pids.add(pid)
        try:
            stat = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
            pid = int(stat.rsplit(")", 1)[1].split()[1])
        except (OSError, ValueError, IndexError):
            break
    return pids


BUSY = re.compile(r"tests/(?!repo-hygiene/)[A-Za-z0-9_.-]+/verify\.py|tests/perf/bench\.py")


def busy_processes() -> list[str]:
    mine = ancestors()
    found = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit() or int(entry.name) in mine:
            continue
        try:
            command = (entry / "cmdline").read_bytes().replace(b"\0", b" ").decode("utf-8", "replace").strip()
        except OSError:
            continue
        if BUSY.search(command) and "--dry-run" not in command and " summary " not in f" {command} " \
                and " compare " not in f" {command} ":
            found.append(f"{entry.name}: {command[:160]}")
    return found


def acquire_lock() -> Any:
    from support.tools import scratch_root

    path = Path(os.environ.get("KRS_PERF_LOCK", os.fspath(scratch_root() / "krs-perf.lock")))
    handle = path.open("a+")
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise GateError(f"another harness run holds {path}; runs must be strictly serial") from None
    return handle


# --- entry points -------------------------------------------------------------------------


def run_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--port", action="append", help="port key (repeatable; default: all)")
    parser.add_argument("--stage", action="append", choices=list(STAGES), help="stage (repeatable; default: all)")
    parser.add_argument("--scenario", action="append", choices=list(SCENARIOS),
                        help="scenario (repeatable; default: all)")
    parser.add_argument("--runs", type=int, default=3, help="repetitions per scenario (default 3)")
    parser.add_argument("--cold-runs", type=int, help="repetitions for the cold scenario (default: --runs)")
    parser.add_argument("--list", action="store_true", help="list ports, stages, scenarios, and profiles")
    parser.add_argument("--dry-run", action="store_true", help="print the selected matrix and verify edit anchors")
    parser.add_argument("--env", action="append", default=[], metavar="KEY=VALUE",
                        help="set a build variable for every command of the run; recorded in receipts")
    parser.add_argument("--label", help="free-form label stored in every receipt")
    parser.add_argument("--krs", type=Path, help="use this krs executable instead of building one")
    parser.add_argument("--receipts", type=Path, help="receipt directory (default: under the checkout scratch)")
    parser.add_argument("--keep", action="store_true", help="keep the scratch workspace and Cargo targets")
    parser.add_argument("--timeout", type=float, default=3600, help="per-command timeout in seconds")
    parser.add_argument("--memory-method", choices=["auto", "rusage"], default="auto",
                        help="auto: per-run cgroup in a delegated systemd scope; rusage: wall and wait4 CPU only")
    parser.add_argument("--allow-busy", action="store_true",
                        help="start even when a gate verifier or another harness run is active")
    parser.add_argument("--profile", choices=["none", *PROFILES], default="none",
                        help="profiling mode; profiled receipts never compare with unprofiled ones")
    return parser


def parse_overrides(pairs: Sequence[str], profile: Profile | None) -> dict[str, str]:
    overrides = {}
    for pair in pairs:
        key, separator, value = pair.partition("=")
        if not separator or not key:
            raise GateError(f"--env expects KEY=VALUE: {pair!r}")
        if key == "RUSTC_BOOTSTRAP" and profile is None:
            raise GateError("RUSTC_BOOTSTRAP is reserved for profiling modes")
        overrides[key] = value
    return overrides


def enter_scope_if_possible(argv: Sequence[str]) -> str | None:
    """Re-execute inside a delegated scope; returns why not when it cannot."""

    if os.environ.get(measure.SCOPE_VARIABLE) == "1":
        return None
    if shutil.which("systemd-run") is None or measure.current_cgroup() is None:
        return "systemd-run or cgroup v2 is unavailable"
    probe = subprocess.run(measure.scope_command(["true"]), capture_output=True, text=True, check=False)
    if probe.returncode != 0:
        return f"systemd-run cannot create a delegated user scope: {probe.stderr.strip()[:200]}"
    os.environ[measure.SCOPE_VARIABLE] = "1"
    sys.stdout.flush()
    os.execvp("systemd-run", measure.scope_command([sys.executable, os.fspath(SELF), *argv]))
    return None  # unreachable


def main_run(argv: Sequence[str]) -> int:
    parser = run_parser()
    arguments = parser.parse_args(argv)
    if arguments.runs < 1 or (arguments.cold_runs is not None and arguments.cold_runs < 1):
        parser.error("--runs and --cold-runs must be at least 1")
    ports = load_ports()
    if arguments.list:
        list_matrix(ports)
        return 0
    profile = PROFILES.get(arguments.profile)
    overrides = parse_overrides(arguments.env, profile)
    if arguments.dry_run:
        dry_run(arguments, ports)
        return 0

    scope_note = None
    if arguments.memory_method == "auto":
        scope_note = enter_scope_if_possible(argv)
    busy = busy_processes()
    if busy and not arguments.allow_busy:
        raise GateError("refusing to measure while other gate or harness processes run "
                        "(--allow-busy overrides):\n  " + "\n  ".join(busy))
    lock = acquire_lock()  # noqa: F841 - held for the life of the process
    meter = measure.Meter.open() if arguments.memory_method == "auto" else measure.Meter(None, "--memory-method rusage")
    if meter.scope is None:
        print(f"warning: peak memory unavailable ({scope_note or meter.note}); recording wall and wait4 CPU only",
              file=sys.stderr)

    from support.tools import checkout_scratch

    cells = selection(arguments, ports)
    environment, stripped = base_environment(overrides)
    revision = receipts.revision()
    run_id = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + f"-{os.getpid()}"
    receipts_root = checkout_scratch() / "perf-receipts"
    receipts_dir = arguments.receipts or receipts_root / receipts.revision_key(revision) / run_id
    receipts_dir.mkdir(parents=True, exist_ok=True)
    work = checkout_scratch() / "perf-work" / run_id
    rustc = receipts.parse_rustc_verbose(
        subprocess.run(["rustc", "-vV"], env=environment, capture_output=True, text=True, check=True).stdout)
    needs_krs = any(stage.krs_command or stage.name == "collector-build" for _, stage, _ in cells)
    krs = None
    flags = {"timings": False, "counters": False}
    if needs_krs:
        krs = arguments.krs.resolve() if arguments.krs else build_krs(environment)
        flags = krs_flags(krs, environment)
        if not flags["timings"]:
            print("note: this krs does not accept --timings; phase timings are not collected", file=sys.stderr)
    base = {
        "schema": receipts.SCHEMA,
        "run_id": run_id,
        "label": arguments.label,
        "revision": revision,
        "pins": receipts.pins(),
        "toolchain": receipts.toolchain(environment),
        "host": receipts.host(),
        "environment": {"overrides": overrides, "stripped": stripped, "fixed": {
            "CARGO_NET_OFFLINE": "true", "RUSTUP_TOOLCHAIN": "stable"}},
        "flags": list(argv),
        "profiling": profile is not None,
        "profile": None if profile is None else profile.name,
        "krs_binary": None if krs is None else {"path": os.fspath(krs), "sha256": sha256_file(krs), **{
            f"accepts_{name}": value for name, value in flags.items()}},
    }
    context = Context(arguments, run_id, work, receipts_dir, environment, overrides, stripped,
                      rustc.get("host", ""), krs, flags, meter, base)
    receipts.append_index(receipts_root, {"run_id": run_id, "revision": revision["commit"],
                                          "dirty": revision["dirty"], "created": receipts.utc_now(),
                                          "label": arguments.label, "path": os.fspath(receipts_dir),
                                          "argv": list(argv)})
    print(f"run {run_id}: receipts in {receipts_dir}; measurement {meter.method}; "
          f"load average {receipts.load_average()}", flush=True)
    try:
        copy_semantics(context.semantics)
        for port, stage, scenarios in cells:
            print(f"{port.key} {stage.name}: {', '.join(scenarios)}", flush=True)
            try:
                run_cell(context, port, stage, scenarios)
            except (GateError, subprocess.SubprocessError, OSError) as error:
                context.failures.append(f"{port.key}/{stage.name}: {error}")
                print(f"  FAILED {port.key}/{stage.name}: {error}", file=sys.stderr, flush=True)
    finally:
        if not arguments.keep:
            shutil.rmtree(work, ignore_errors=True)
    print()
    print(compare.render_summary(receipts.load([receipts_dir])))
    print(f"\n{context.written} receipts in {receipts_dir}")
    if context.failures:
        print("failures:\n  " + "\n  ".join(context.failures), file=sys.stderr)
        return 1
    return 0


def main_summary(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="bench.py summary", description="print one table per port")
    parser.add_argument("paths", nargs="+", type=Path, help="receipt files or directories")
    arguments = parser.parse_args(argv)
    found = receipts.load(arguments.paths)
    if not found:
        raise GateError("no krs-perf-receipt/1 receipts found")
    print(compare.render_summary(found))
    return 0


def main_compare(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="bench.py compare", description=compare.__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("before", type=Path, help="receipt directory or file (side A)")
    parser.add_argument("after", type=Path, help="receipt directory or file (side B)")
    parser.add_argument("--json", action="store_true", help="print the rows as JSON")
    arguments = parser.parse_args(argv)
    before, after = receipts.load([arguments.before]), receipts.load([arguments.after])
    if not before or not after:
        raise GateError("both sides need at least one krs-perf-receipt/1 receipt")
    rows, warnings = compare.compare(before, after)
    if arguments.json:
        print(json.dumps({"warnings": warnings, "rows": [{**row, "key": list(row["key"])} for row in rows]}, indent=2))
    else:
        print(compare.render_compare(rows, warnings))
    return 0


def main(argv: Sequence[str]) -> int:
    if argv and argv[0] == "summary":
        return main_summary(argv[1:])
    if argv and argv[0] == "compare":
        return main_compare(argv[1:])
    return main_run(argv)


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as error:
        print(f"FAIL compile-performance harness: {error}", file=sys.stderr)
        raise SystemExit(1)
