#!/usr/bin/env python3
"""Size and shape ladders with growth fits for the KRS definition pipeline.

Measures one `krs` stage over ascending values of a size parameter, for the
real ports truncated to fractions of their rules and equations and for
shape-isolated synthetic definitions, then fits each metric's growth
exponent (least squares on ln(metric) against ln(size), with R² and the top
slope) and flags every slope above 1.2.

    python3 tests/perf/ladder.py --list
    python3 tests/perf/ladder.py --dry-run [--ladder NAME ...]
    python3 tests/perf/ladder.py --ladder sorts-deep [--values 8,16,32] [--runs 2] [--llvm-lines]
    python3 tests/perf/ladder.py generate --ladder NAME --value V --out DIR
    python3 tests/perf/ladder.py report RECEIPTS... [--all-metrics] [--json]

Ladders are defined in `tests/perf/ladders.toml`; see `tests/perf/README.md`.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402
from support.hashing import sha256_file  # noqa: E402
from support.pins import load_toml  # noqa: E402
from perf import bench, growth, measure, receipts, synth, truncate  # noqa: E402

HERE = Path(__file__).resolve().parent
LADDERS = HERE / "ladders.toml"
SELF = Path(__file__).resolve()
KRS_STAGES = ("krs-build", "krs-emit-k", "krs-check")
LLVM_FUNCTIONS_KEPT = 200


@dataclass(frozen=True)
class Ladder:
    name: str
    kind: str
    param: str
    values: tuple[int, ...]
    stop_seconds: float
    description: str
    port: str | None = None
    shape: str | None = None
    denominator: int = 8

    @property
    def family(self) -> str:
        """Ladders of one family share a Cargo target, so dependencies build once per invocation."""

        return "semantics" if self.kind == "truncate" else "synth"

    @property
    def receipt_port(self) -> str:
        return self.port if self.kind == "truncate" else "synth"

    @property
    def package(self) -> str:
        return f"krs-{self.port}-semantics" if self.kind == "truncate" else synth.PACKAGE

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "kind": self.kind, "param": self.param, "values": list(self.values),
                "stop_seconds": self.stop_seconds, "description": self.description, "port": self.port,
                "shape": self.shape, "denominator": self.denominator if self.kind == "truncate" else None}


def load_ladders(path: Path = LADDERS) -> dict[str, Ladder]:
    document = load_toml(path)
    if document.get("schema") != 1:
        raise GateError(f"{path.name}: unsupported schema {document.get('schema')!r}")
    ladders = {}
    for entry in document.get("ladder", []):
        ladder = Ladder(
            name=str(entry["name"]), kind=str(entry["kind"]), param=str(entry["param"]),
            values=tuple(int(value) for value in entry["values"]), stop_seconds=float(entry["stop_seconds"]),
            description=str(entry.get("description", "")), port=entry.get("port"), shape=entry.get("shape"),
            denominator=int(entry.get("denominator", 8)),
        )
        if ladder.kind not in ("truncate", "synthetic"):
            raise GateError(f"{path.name}: ladder {ladder.name}: unknown kind {ladder.kind!r}")
        if ladder.kind == "synthetic" and ladder.shape not in synth.SHAPES:
            raise GateError(f"{path.name}: ladder {ladder.name}: unknown shape {ladder.shape!r}")
        if ladder.kind == "truncate" and not (ROOT / "semantics" / str(ladder.port) / "src/lib.rs").is_file():
            raise GateError(f"{path.name}: ladder {ladder.name}: unknown port {ladder.port!r}")
        if list(ladder.values) != sorted(set(ladder.values)) or ladder.values[0] < 1:
            raise GateError(f"{path.name}: ladder {ladder.name}: values must be ascending, distinct, and positive")
        if ladder.kind == "truncate" and ladder.values[-1] > ladder.denominator:
            raise GateError(f"{path.name}: ladder {ladder.name}: a value exceeds the denominator")
        ladders[ladder.name] = ladder
    return ladders


# --- rung sources --------------------------------------------------------------------


@dataclass
class Rung:
    source: str
    detail: dict[str, Any] = field(default_factory=dict)


def rung_source(ladder: Ladder, value: int) -> Rung:
    if ladder.kind == "synthetic":
        assert ladder.shape is not None
        return Rung(synth.generate(ladder.shape, value), {"shape": ladder.shape, "n": value})
    original = (ROOT / "semantics" / str(ladder.port) / "src/lib.rs").read_text(encoding="utf-8")
    cut = truncate.truncate(original, value, ladder.denominator)
    return Rung(cut.source, {
        "fraction": f"{value}/{ladder.denominator}", "rules_total": cut.rules_total, "rules_kept": cut.rules_kept,
        "equations_total": cut.equations_total, "equations_kept": cut.equations_kept,
        "rule_blocks_dropped": cut.rule_blocks_dropped,
    })


def relax_lints(manifest: Path) -> None:
    """Scratch copies only: `warnings = "deny"` becomes "warn", since removed rules can leave unused imports."""

    text = manifest.read_text(encoding="utf-8")
    manifest.write_text(text.replace('warnings = "deny"', 'warnings = "warn"'), encoding="utf-8")


@dataclass
class Workspace:
    manifest: Path
    source: Path


def prepare_workspace(ladder: Ladder, directory: Path) -> Workspace:
    """A scratch crate or semantics workspace for `ladder` under `directory` (created once)."""

    if ladder.kind == "synthetic":
        manifest = directory / "crate" / "Cargo.toml"
        if not manifest.is_file():
            synth.write_crate(directory / "crate", "")
        return Workspace(manifest, directory / "crate" / "src" / "lib.rs")
    semantics = directory / "semantics"
    if not semantics.is_dir():
        bench.copy_semantics(semantics)
        relax_lints(semantics / "Cargo.toml")
        relax_lints(semantics / str(ladder.port) / "Cargo.toml")
    return Workspace(semantics / "Cargo.toml", semantics / str(ladder.port) / "src/lib.rs")


def write_if_changed(path: Path, text: str) -> None:
    if not path.is_file() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")


# --- cargo llvm-lines ------------------------------------------------------------------


_LLVM_ROW = re.compile(r"^\s*(\d+)\s+\([^)]*\)\s+(\d+)\s+\([^)]*\)\s+(.+?)\s*$")
_LLVM_TOTAL = re.compile(r"^\s*(\d+)\s+(\d+)\s+\(TOTAL\)\s*$")


def parse_llvm_lines(text: str, keep: int = LLVM_FUNCTIONS_KEPT) -> dict[str, Any] | None:
    """`cargo llvm-lines` output as `{total, copies, functions [{name, lines, copies}]}` (largest first)."""

    total = copies = None
    functions = []
    for line in text.splitlines():
        match = _LLVM_TOTAL.match(line)
        if match:
            total, copies = int(match.group(1)), int(match.group(2))
            continue
        match = _LLVM_ROW.match(line)
        if match:
            functions.append({"name": match.group(3), "lines": int(match.group(1)), "copies": int(match.group(2))})
    if total is None:
        return None
    return {"total": total, "copies": copies, "functions": functions[:keep], "functions_listed": len(functions)}


# --- running ----------------------------------------------------------------------------


@dataclass
class Session:
    arguments: argparse.Namespace
    run_id: str
    work: Path
    receipts_dir: Path
    environment: dict[str, str]
    host_triple: str
    krs: Path
    krs_flags: dict[str, bool]
    meter: measure.Meter
    base: dict[str, Any]
    failures: list[str] = field(default_factory=list)
    written: int = 0
    settled: set[str] = field(default_factory=set)


def krs_argv(session: Session, ladder: Ladder, workspace: Workspace, *, output: Path | None,
             timings: Path | None) -> list[str]:
    stage = bench.STAGES[session.arguments.stage]
    argv = [os.fspath(session.krs), str(stage.krs_command), "--manifest-path", os.fspath(workspace.manifest),
            "--package", ladder.package, "--definition", "main"]
    if stage.output:
        assert output is not None
        argv += ["--output", os.fspath(output)]
    if timings is not None and session.krs_flags.get("timings"):
        argv += ["--timings", os.fspath(timings)]
    if timings is not None and session.krs_flags.get("counters"):
        argv += ["--counters", os.fspath(bench.counters_path(timings))]
    return argv


def clean_rung(session: Session, ladder: Ladder, workspace: Workspace, environment: Mapping[str, str]) -> None:
    """Remove the definition crate's and the generated collectors' artifacts; dependencies stay built."""

    target = Path(environment["CARGO_TARGET_DIR"])
    jobs = [(workspace.manifest, ladder.package)]
    for manifest in sorted((target / "krs" / "collectors").glob("*/Cargo.toml")):
        match = re.search(r'^name = "([^"]+)"', manifest.read_text(encoding="utf-8"), re.MULTILINE)
        if match:
            jobs.append((manifest, match.group(1)))
    for manifest, package in jobs:
        for extra in ([], ["--target", session.host_triple]):
            subprocess.run(["cargo", "+stable", "clean", "--offline", "-p", package, "--manifest-path",
                            os.fspath(manifest), *extra],
                           cwd=ROOT, env=dict(environment), capture_output=True, check=False, timeout=600)


def llvm_lines(session: Session, ladder: Ladder, workspace: Workspace, environment: Mapping[str, str],
               log: Path) -> dict[str, Any] | None:
    started = time.monotonic()
    completed = subprocess.run(
        ["cargo", "+stable", "llvm-lines", "--manifest-path", os.fspath(workspace.manifest), "-p", ladder.package,
         "--lib", "--offline"],
        cwd=ROOT, env=dict(environment), capture_output=True, text=True, check=False,
        timeout=session.arguments.timeout,
    )
    log.write_text(completed.stdout + completed.stderr, encoding="utf-8")
    parsed = parse_llvm_lines(completed.stdout) if completed.returncode == 0 else None
    if parsed is None:
        print(f"    llvm-lines failed ({completed.returncode}); see {log}", file=sys.stderr, flush=True)
        return None
    return {**parsed, "wall_seconds": round(time.monotonic() - started, 3)}


def run_ladder(session: Session, ladder: Ladder, values: Sequence[int]) -> dict[str, Any]:
    arguments = session.arguments
    directory = session.work / ladder.name
    workspace = prepare_workspace(ladder, directory)
    target = session.work / "targets" / ladder.family
    environment = {**session.environment, "CARGO_TARGET_DIR": os.fspath(target)}
    logs = session.receipts_dir / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    stop_seconds = arguments.stop_seconds or ladder.stop_seconds
    outcome: dict[str, Any] = {"ladder": ladder.to_json(), "measured": [], "stopped": None,
                               "stop_seconds": stop_seconds}

    if ladder.family not in session.settled or not target.is_dir():
        first = rung_source(ladder, values[0])
        write_if_changed(workspace.source, first.source)
        log = logs / f"{ladder.name}.settle.log"
        output = session.work / "out" / "settle"
        with log.open("wb") as handle:
            completed = subprocess.run(krs_argv(session, ladder, workspace, output=output, timings=None),
                                       cwd=ROOT, env=environment, stdout=handle, stderr=subprocess.STDOUT,
                                       timeout=arguments.timeout, check=False)
        shutil.rmtree(output, ignore_errors=True)
        print(f"  settle ({ladder.family} dependencies): exit {completed.returncode}", flush=True)
        session.settled.add(ladder.family)

    for value in values:
        rung = rung_source(ladder, value)
        write_if_changed(workspace.source, rung.source)
        walls = []
        failures = 0
        llvm = None
        for repetition in range(1, arguments.runs + 1):
            clean_rung(session, ladder, workspace, environment)
            name = f"{ladder.name}.{value}.{repetition}"
            output = session.work / "out" / name
            timings = session.receipts_dir / "timings" / f"{name}.krs-timings.json"
            timings.parent.mkdir(parents=True, exist_ok=True)
            argv = krs_argv(session, ladder, workspace, output=output, timings=timings)
            load_before = receipts.load_average()
            started = receipts.utc_now()
            result = session.meter.run(argv, cwd=ROOT, environment=environment, log=logs / f"{name}.log",
                                       timeout=arguments.timeout)
            shutil.rmtree(output, ignore_errors=True)
            timings_status, timings_doc = (receipts.ingest_timings(timings) if session.krs_flags.get("timings")
                                           else ("unsupported", None))
            counters_status, counters_doc = (receipts.ingest_counters(bench.counters_path(timings))
                                             if session.krs_flags.get("counters") else ("unsupported", None))
            if repetition == arguments.runs and arguments.llvm_lines and result.exit_status == 0:
                llvm = llvm_lines(session, ladder, workspace, environment, logs / f"{ladder.name}.{value}.llvm-lines.log")
            receipt = {
                **session.base,
                "created": started,
                "port": ladder.receipt_port,
                "package": ladder.package,
                "stage": arguments.stage,
                "scenario": f"ladder:{ladder.name}:{value}",
                "repetition": repetition,
                "scenario_detail": {"ladder": ladder.name, "value": value, "target": "dependencies built; "
                                    "definition crate and collectors cleaned"},
                "command": {"argv": argv, "cwd": os.fspath(ROOT), "target": os.fspath(target)},
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
                "cargo_timings": None,
                "log": f"logs/{name}.log",
                "ladder": {
                    **ladder.to_json(), "value": value,
                    "source_bytes": len(rung.source.encode("utf-8")), "source_lines": rung.source.count("\n"),
                    "rung": rung.detail, "llvm_lines": llvm,
                },
            }
            receipts.write(receipt, session.receipts_dir / f"{name}.json")
            session.written += 1
            peak = "n/a" if result.peak_memory_bytes is None else f"{result.peak_memory_bytes / 2**30:.2f}GiB"
            print(f"  {name}: exit={result.exit_status} wall={result.wall_seconds:.2f}s "
                  f"cpu={(result.user_seconds or 0) + (result.sys_seconds or 0):.2f}s peak={peak} "
                  f"load={load_before[0] if load_before else '?'}"
                  + (f" llvm-lines={llvm['total']}" if llvm else ""), flush=True)
            if result.exit_status != 0:
                failures += 1
                session.failures.append(f"{name} exited {result.exit_status}")
            else:
                walls.append(result.wall_seconds)
        outcome["measured"].append(value)
        if failures == arguments.runs:
            outcome["stopped"] = f"every repetition at {value} failed"
            break
        median = sorted(walls)[len(walls) // 2]
        if median > stop_seconds:
            outcome["stopped"] = f"wall {median:.1f}s at {value} exceeds stop_seconds {stop_seconds:g}"
            break
    return outcome


def attribute(analysis: dict[str, Any], ladder_receipts: Sequence[Mapping[str, Any]]) -> None:
    """Name the llvm-lines function group that grew most between the two largest rungs with data."""

    by_value: dict[float, list[Mapping[str, Any]]] = {}
    for receipt in ladder_receipts:
        llvm = (receipt.get("ladder") or {}).get("llvm_lines")
        if llvm and receipt.get("exit_status") == 0:
            by_value[float(receipt["ladder"]["value"])] = llvm["functions"]
    responsible = None
    if len(by_value) >= 2:
        small, large = sorted(by_value)[-2:]
        found = growth.largest_growth_group(by_value[small], by_value[large])
        if found:
            responsible = (f"`{found[0]}` (+{found[1]:.0f} LLVM IR lines from {small:g} to {large:g}; "
                           "cargo llvm-lines function group; no per-macro attribution in this harness)")
    llvm_fit = next((row for row in analysis["by_param"] if row["metric"] == "llvm_lines.total"), None)
    llvm_superlinear = bool(llvm_fit and ((llvm_fit["fit"] and llvm_fit["fit"]["slope"] > analysis["threshold"])
                                          or (llvm_fit["top_slope"] or 0) > analysis["threshold"]))
    if responsible and not llvm_superlinear and llvm_fit and llvm_fit["fit"]:
        # Codegen volume is not what grows superlinearly; a function group would mislead.
        responsible = (f"none in codegen volume: LLVM IR lines grow with slope {llvm_fit['fit']['slope']:.2f} "
                       f"(top {llvm_fit['top_slope']:.2f}), so the superlinear cost is elsewhere in the stage "
                       f"(largest LLVM IR growth was {responsible})")
    analysis["responsible"] = responsible
    for item in analysis["flagged"]:
        item["responsible"] = responsible


def ladder_reports(found: Sequence[Mapping[str, Any]], threshold: float) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    by_ladder: dict[str, list[Mapping[str, Any]]] = {}
    for receipt in found:
        if isinstance(receipt.get("ladder"), Mapping):
            by_ladder.setdefault(str(receipt["ladder"]["name"]), []).append(receipt)
    reports = []
    for name, group in by_ladder.items():
        definition = {key: value for key, value in group[0]["ladder"].items()
                      if key not in ("value", "source_bytes", "source_lines", "rung", "llvm_lines")}
        notes = []
        loads = [receipt["load_average"]["before"][0] for receipt in group
                 if (receipt.get("load_average") or {}).get("before")]
        if loads:
            notes.append(f"1-minute load average before runs: {min(loads):g}..{max(loads):g} "
                         f"on {group[0].get('host', {}).get('logical_cpus', '?')} logical CPUs; "
                         "wall is inflated under load, prefer counters, CPU, and memory")
        failed = sorted({receipt["ladder"]["value"] for receipt in group if receipt.get("exit_status") != 0})
        if failed:
            notes.append(f"failed rungs (excluded from fits): {', '.join(str(value) for value in failed)}")
        runs = {}
        for receipt in group:
            runs.setdefault(receipt["ladder"]["value"], 0)
            runs[receipt["ladder"]["value"]] += 1
        notes.append("repetitions per value: " + ", ".join(f"{value}: {count}" for value, count in sorted(runs.items())))
        if definition.get("kind") == "truncate":
            details = {receipt["ladder"]["value"]: receipt["ladder"].get("rung") or {} for receipt in group}
            notes.append("kept rules/equations: " + ", ".join(
                f"{value}/{definition.get('denominator')}: {detail.get('rules_kept')}/{detail.get('equations_kept')}"
                for value, detail in sorted(details.items())))
        definition["notes"] = notes
        analysis = growth.analyse(group, threshold)
        attribute(analysis, group)
        reports.append((definition, analysis))
    reports.sort(key=lambda pair: pair[0]["name"])
    return reports


def write_reports(directory: Path, reports: Sequence[tuple[dict[str, Any], dict[str, Any]]],
                  outcomes: Mapping[str, Mapping[str, Any]] | None = None) -> Path:
    sections = ["# Ladder report", ""]
    summary = []
    for definition, analysis in reports:
        outcome = (outcomes or {}).get(definition["name"])
        if outcome and outcome.get("stopped"):
            definition["notes"].append(f"stopped: {outcome['stopped']}")
        sections.append(growth.render(definition, analysis))
        summary.append({"ladder": definition, "analysis": analysis, "outcome": outcome})
    report = directory / "ladder-report.md"
    report.write_text("\n".join(sections), encoding="utf-8")
    (directory / "ladder-report.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n",
                                                  encoding="utf-8")
    return report


# --- listing, dry run, generate ------------------------------------------------------------


def selected(arguments: argparse.Namespace, ladders: Mapping[str, Ladder]) -> list[tuple[Ladder, list[int]]]:
    names = arguments.ladder or list(ladders)
    chosen = []
    for name in names:
        if name not in ladders:
            raise GateError(f"unknown ladder {name!r}; known: {', '.join(ladders)}")
        ladder = ladders[name]
        values = list(ladder.values)
        if arguments.values:
            values = sorted({int(value) for value in arguments.values.split(",")})
            if ladder.kind == "truncate" and values[-1] > ladder.denominator:
                raise GateError(f"{name}: a value exceeds the denominator {ladder.denominator}")
        if arguments.max_rungs:
            values = values[:arguments.max_rungs]
        chosen.append((ladder, values))
    return chosen


def list_ladders(ladders: Mapping[str, Ladder]) -> None:
    for ladder in ladders.values():
        subject = f"port {ladder.port}" if ladder.kind == "truncate" else f"shape {ladder.shape}"
        print(f"{ladder.name:<18} {ladder.kind:<9} {subject:<24} values={list(ladder.values)} "
              f"stop_seconds={ladder.stop_seconds:g}")
        print(f"{'':<18} {ladder.description}")


def dry_run(arguments: argparse.Namespace, ladders: Mapping[str, Ladder]) -> None:
    rows = 0
    for ladder, values in selected(arguments, ladders):
        print(f"{ladder.name} ({ladder.kind}; package {ladder.package}; stage {arguments.stage}; "
              f"stop_seconds {arguments.stop_seconds or ladder.stop_seconds:g})")
        for value in values:
            rung = rung_source(ladder, value)
            detail = " ".join(f"{key}={item}" for key, item in rung.detail.items())
            print(f"  {value:>6}: {len(rung.source.encode('utf-8')):>9} bytes {rung.source.count(chr(10)):>7} lines  "
                  f"{detail}")
            rows += 1
    print(f"{rows} rungs x {arguments.runs} runs; every rung source generated in memory; "
          f"command: krs {bench.STAGES[arguments.stage].krs_command} --manifest-path <scratch> --package <package> "
          "--definition main [--output <out>] --timings <file> --counters <file>"
          + ("; plus cargo llvm-lines per rung" if arguments.llvm_lines else ""))


def main_generate(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="ladder.py generate", description="write one rung's crate or workspace")
    parser.add_argument("--ladder", required=True)
    parser.add_argument("--value", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True, help="directory to create")
    arguments = parser.parse_args(argv)
    ladders = load_ladders()
    if arguments.ladder not in ladders:
        raise GateError(f"unknown ladder {arguments.ladder!r}")
    ladder = ladders[arguments.ladder]
    if arguments.out.exists():
        raise GateError(f"{arguments.out} exists")
    workspace = prepare_workspace(ladder, arguments.out)
    workspace.source.write_text(rung_source(ladder, arguments.value).source, encoding="utf-8")
    print(f"wrote {workspace.manifest} (package {ladder.package})")
    return 0


def main_report(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="ladder.py report", description="fit and report ladder receipts")
    parser.add_argument("paths", nargs="+", type=Path, help="receipt files or directories")
    parser.add_argument("--threshold", type=float, default=growth.THRESHOLD)
    parser.add_argument("--all-metrics", action="store_true", help="print every metric, not only the core ones")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--write", type=Path, help="also write ladder-report.md and .json into this directory")
    arguments = parser.parse_args(argv)
    reports = ladder_reports(receipts.load(arguments.paths), arguments.threshold)
    if not reports:
        raise GateError("no ladder receipts found")
    if arguments.write:
        arguments.write.mkdir(parents=True, exist_ok=True)
        outcomes = {}
        previous = arguments.write / "ladder-report.json"
        if previous.is_file():
            # Keep the stop reasons the measuring run recorded.
            for entry in json.loads(previous.read_text(encoding="utf-8")):
                if entry.get("outcome"):
                    outcomes[entry["ladder"]["name"]] = entry["outcome"]
        write_reports(arguments.write, reports, outcomes)
    if arguments.json:
        print(json.dumps([{"ladder": d, "analysis": a} for d, a in reports], indent=2, sort_keys=True))
    else:
        for definition, analysis in reports:
            print(growth.render(definition, analysis, all_metrics=arguments.all_metrics))
    return 0


# --- entry points ------------------------------------------------------------------------------


def run_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ladder", action="append", help="ladder name (repeatable; default: all)")
    parser.add_argument("--values", help="comma-separated values replacing each selected ladder's values")
    parser.add_argument("--max-rungs", type=int, help="measure at most this many of the smallest values")
    parser.add_argument("--runs", type=int, default=1, help="repetitions per rung (default 1)")
    parser.add_argument("--stage", choices=KRS_STAGES, default="krs-build", help="measured krs stage")
    parser.add_argument("--stop-seconds", type=float, help="override every ladder's stop_seconds")
    parser.add_argument("--llvm-lines", action="store_true",
                        help="after each rung, count the definition crate's LLVM IR lines with cargo llvm-lines")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--dry-run", action="store_true", help="generate every selected rung in memory and list it")
    parser.add_argument("--label")
    parser.add_argument("--krs", type=Path, help="use this krs executable instead of building one")
    parser.add_argument("--receipts", type=Path, help="receipt directory (default: under the checkout scratch)")
    parser.add_argument("--keep", action="store_true", help="keep the scratch workspaces and Cargo targets")
    parser.add_argument("--timeout", type=float, default=3600)
    parser.add_argument("--threshold", type=float, default=growth.THRESHOLD)
    parser.add_argument("--memory-method", choices=["auto", "rusage"], default="auto")
    parser.add_argument("--allow-busy", action="store_true")
    return parser


def enter_scope_if_possible(argv: Sequence[str]) -> str | None:
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
    if arguments.runs < 1:
        parser.error("--runs must be at least 1")
    ladders = load_ladders()
    if arguments.list:
        list_ladders(ladders)
        return 0
    if arguments.dry_run:
        dry_run(arguments, ladders)
        return 0
    chosen = selected(arguments, ladders)

    scope_note = enter_scope_if_possible(argv) if arguments.memory_method == "auto" else None
    busy = bench.busy_processes()
    if busy and not arguments.allow_busy:
        raise GateError("refusing to measure while other gate or harness processes run "
                        "(--allow-busy overrides):\n  " + "\n  ".join(busy))
    lock = bench.acquire_lock()  # noqa: F841 - held for the life of the process
    meter = measure.Meter.open() if arguments.memory_method == "auto" else measure.Meter(None, "--memory-method rusage")
    if meter.scope is None:
        print(f"warning: peak memory unavailable ({scope_note or meter.note}); recording wall and wait4 CPU only",
              file=sys.stderr)

    from support.tools import checkout_scratch

    environment, stripped = bench.base_environment({})
    revision = receipts.revision()
    run_id = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + f"-{os.getpid()}"
    receipts_root = checkout_scratch() / "perf-receipts"
    receipts_dir = arguments.receipts or receipts_root / receipts.revision_key(revision) / f"ladder-{run_id}"
    receipts_dir.mkdir(parents=True, exist_ok=True)
    work = checkout_scratch() / "perf-work" / f"ladder-{run_id}"
    rustc = receipts.parse_rustc_verbose(
        subprocess.run(["rustc", "-vV"], env=environment, capture_output=True, text=True, check=True).stdout)
    krs = arguments.krs.resolve() if arguments.krs else bench.build_krs(environment)
    flags = bench.krs_flags(krs, environment)
    base = {
        "schema": receipts.SCHEMA,
        "run_id": run_id,
        "label": arguments.label,
        "revision": revision,
        "pins": receipts.pins(),
        "toolchain": receipts.toolchain(environment),
        "host": receipts.host(),
        "environment": {"overrides": {}, "stripped": stripped, "fixed": {
            "CARGO_NET_OFFLINE": "true", "RUSTUP_TOOLCHAIN": "stable"}},
        "flags": ["ladder", *argv],
        "profiling": False,
        "profile": None,
        "krs_binary": {"path": os.fspath(krs), "sha256": sha256_file(krs),
                       **{f"accepts_{name}": value for name, value in flags.items()}},
    }
    session = Session(arguments, run_id, work, receipts_dir, environment, rustc.get("host", ""), krs, flags,
                      meter, base)
    receipts.append_index(receipts_root, {"run_id": run_id, "revision": revision["commit"],
                                          "dirty": revision["dirty"], "created": receipts.utc_now(),
                                          "label": arguments.label, "path": os.fspath(receipts_dir),
                                          "argv": ["ladder", *argv]})
    print(f"ladder run {run_id}: receipts in {receipts_dir}; measurement {meter.method}; "
          f"load average {receipts.load_average()}", flush=True)
    outcomes: dict[str, dict[str, Any]] = {}
    try:
        for ladder, values in chosen:
            print(f"{ladder.name}: values {values}", flush=True)
            try:
                outcomes[ladder.name] = run_ladder(session, ladder, values)
            except (GateError, subprocess.SubprocessError, OSError, ValueError) as error:
                session.failures.append(f"{ladder.name}: {error}")
                print(f"  FAILED {ladder.name}: {error}", file=sys.stderr, flush=True)
    finally:
        if not arguments.keep:
            shutil.rmtree(work, ignore_errors=True)
    reports = ladder_reports(receipts.load([receipts_dir]), arguments.threshold)
    report = write_reports(receipts_dir, reports, outcomes)
    print()
    print(report.read_text(encoding="utf-8"))
    print(f"{session.written} receipts and the ladder report in {receipts_dir}")
    if session.failures:
        print("failures:\n  " + "\n  ".join(session.failures), file=sys.stderr)
        return 1
    return 0


def main(argv: Sequence[str]) -> int:
    if argv and argv[0] == "report":
        return main_report(argv[1:])
    if argv and argv[0] == "generate":
        return main_generate(argv[1:])
    return main_run(argv)


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as error:
        print(f"FAIL ladder harness: {error}", file=sys.stderr)
        raise SystemExit(1)
