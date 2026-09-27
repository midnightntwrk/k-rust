#!/usr/bin/env python3
"""Sampled CPU profiles of `krs` and its generated collector (samply).

The `samply` profiling mode of `bench.py` runs each measured `krs` command
under `taskset -c 0-15 samply record`, which follows child processes, so one
profile holds `krs`, Cargo, and the collector executable. After the run the
profile is folded, per process, into a summary of the top self and inclusive
functions grouped by crate, stored beside the receipt:

    <receipts>/profiles/<cell>.samply.json.gz          samply's profile (`samply load` opens it)
    <receipts>/profiles/<cell>.samply.json.syms.json.gz its symbol sidecar
    <receipts>/profiles/<cell>.folded.gz                folded stacks, `process;outer;...;inner count`
    <receipts>/profiles/<cell>.summary.json             the per-process summary

The numbers to quote come from an unprofiled companion run of the same
cell with the same `krs` executable; `run` performs both:

    python3 tests/perf/sample.py run --port kevm --stage krs-build --scenario no-op --runs 1
    python3 tests/perf/sample.py run ... --collector optimized   # opt-level 3 collector with line tables
    python3 tests/perf/sample.py fold PROFILE.json.gz [--binary PATH ...]
    python3 tests/perf/sample.py show SUMMARY.json

See `tests/perf/README.md`, "Sampled profiles".
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass, field
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any, Iterable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, GateError  # noqa: E402


NAME = "samply"
STAGES = ("krs-check", "krs-emit-k", "krs-build")
SUMMARY_SCHEMA = "krs-perf-sampled-profile/1"
BENCH = Path(__file__).resolve().parent / "bench.py"

# samply's perf ring buffers exhaust the host's lock budget on all 32 CPUs
# (`mmap failed`); k-rust's scripts/profile.sh uses the same mask.
DEFAULT_CPUS = "0-15"
DEFAULT_RATE = 1000

# The collector variants of `run --collector`, as Cargo profile overrides of
# the collector's `dev` build (they reach `cargo build` through the environment).
COLLECTOR_VARIANTS: dict[str, dict[str, str]] = {
    "as-is": {},
    "line-tables": {"CARGO_PROFILE_DEV_DEBUG": "line-tables-only"},
    "optimized": {"CARGO_PROFILE_DEV_OPT_LEVEL": "3", "CARGO_PROFILE_DEV_DEBUG": "line-tables-only"},
}

# The `krs` profiling build: the release profile with line tables and symbols,
# the same settings as k-rust's `[profile.profiling]`.
PROFILING_KRS_ENVIRONMENT = {"CARGO_PROFILE_RELEASE_DEBUG": "line-tables-only", "CARGO_PROFILE_RELEASE_STRIP": "none"}

# Functions that implement a `--timings` span, matched against demangled names,
# so a summary can set the sampled inclusive share beside the span's wall share.
SPAN_FUNCTIONS: tuple[tuple[str, str], ...] = (
    ("collector.resolve", r"::collect_host_descriptors_with_builtins_timed$"),
    ("collector.resolve.provenance", r"::materialize_descriptor_provenance$"),
    ("collector.resolve.payload", r"::resolve_payload$"),
    ("collector.serialize", r"DescriptorBundle>?::to_collector_protocol_measured_in_place$"),
    ("collector.run", r"^krs_cli::command::run_collector$"),
    ("protocol.decode", r"DescriptorBundle as serde(_core)?::de::Deserialize>::deserialize$"),
    ("semantic.lower", r"^krs_cli::command::lower_semantic$"),
    ("definition.lower", r"^krs_cli::command::lower_definition$"),
    ("native.adapt", r"::adapt_definition_for$"),
    ("native.prepare", r"::prepare_definition$"),
    ("native.compile", r"::compile_loaded_definition_timed$"),
    ("native.reparse", r"::parse_kore_definition$"),
    ("native.provenance", r"::join_sentence_provenance$"),
)

TOP_SELF = 30
TOP_INCLUSIVE = 40
TOP_CRATES = 20
DETAILED_MIN_SAMPLES = 50


def cpus() -> str:
    return os.environ.get("KRS_PERF_SAMPLY_CPUS", DEFAULT_CPUS)


def rate() -> int:
    return int(os.environ.get("KRS_PERF_SAMPLY_RATE", str(DEFAULT_RATE)))


def samply() -> str:
    found = os.environ.get("KRS_PERF_SAMPLY") or shutil.which("samply")
    if not found:
        raise GateError("samply is not on PATH (KRS_PERF_SAMPLY overrides)")
    return found


def samply_version() -> str | None:
    try:
        return subprocess.run([samply(), "--version"], capture_output=True, text=True, check=False).stdout.strip()
    except (OSError, GateError):
        return None


# --- the bench.py profiling-mode hooks ---------------------------------------------------


def environment(context: Any) -> dict[str, str]:
    """The mode adds no build environment; the collector variant is an `--env` override."""

    return {}


def profile_path(receipts_dir: Path, name: str) -> Path:
    return receipts_dir / "profiles" / f"{name}.samply.json.gz"


def wrap(context: Any, argv: Sequence[str], name: str) -> list[str]:
    """Run `argv` under `samply record`, pinned to the profiling CPU set."""

    output = profile_path(context.receipts_dir, name)
    output.parent.mkdir(parents=True, exist_ok=True)
    wrapped = [samply(), "record", "--save-only", "--unstable-presymbolicate", "--rate", str(rate()),
               "--output", os.fspath(output), "--", *argv]
    taskset = shutil.which("taskset")
    return [taskset, "-c", cpus(), *wrapped] if taskset and cpus() else wrapped


def collect(context: Any, name: str) -> dict[str, Any]:
    """Fold the cell's profile beside its receipt and return the receipt's `sampled_profile`."""

    directory = context.receipts_dir / "profiles"
    profile = profile_path(context.receipts_dir, name)
    if not profile.is_file():
        return {"status": "missing", "profile": None}
    try:
        summary, folded = fold(profile)
    except (OSError, ValueError, KeyError, GateError) as error:
        return {"status": "invalid", "profile": _relative(profile, context.receipts_dir), "error": str(error)}
    summary["rate_hz"] = rate()
    summary["cpus"] = cpus()
    summary["samply_version"] = samply_version()
    summary_path = directory / f"{name}.summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with gzip.open(directory / f"{name}.folded.gz", "wt", encoding="utf-8") as handle:
        handle.writelines(folded)
    sidecar = sidecar_path(profile)
    if sidecar.is_file():
        with sidecar.open("rb") as source, gzip.open(f"{sidecar}.gz", "wb") as target:
            shutil.copyfileobj(source, target)
        sidecar.unlink()
    return {
        "status": "collected",
        "tool": "samply record",
        "samply_version": summary["samply_version"],
        "rate_hz": summary["rate_hz"],
        "cpus": summary["cpus"],
        "profile": _relative(profile, context.receipts_dir),
        "summary": _relative(summary_path, context.receipts_dir),
        "folded": _relative(directory / f"{name}.folded.gz", context.receipts_dir),
        "processes": [
            {key: process[key] for key in ("process", "binary", "samples", "cpu_seconds", "named_fraction",
                                            "binary_fraction", "attributed_fraction")}
            | {"top_self": process.get("top_self", [])[:5], "spans": process.get("spans", {})}
            for process in summary["processes"]
        ],
        "note": "profiled: wall and CPU include samply; quote the unprofiled companion run",
    }


def _relative(path: Path, base: Path) -> str:
    try:
        return os.fspath(path.relative_to(base))
    except ValueError:
        return os.fspath(path)


# --- folding --------------------------------------------------------------------------------


def sidecar_path(profile: Path) -> Path:
    text = os.fspath(profile)
    return Path((text[:-3] if text.endswith(".gz") else text) + ".syms.json")


def _read_json(path: Path) -> Any:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as handle:
        return json.load(handle)


HASH_SUFFIX = re.compile(r"::h[0-9a-f]{16}$")


def clean_name(name: str) -> str:
    """Drop the legacy-mangling hash and every `::<...>` generic argument list.

    Monomorphic instances of one generic function aggregate as one function;
    the receiver type of `<Type>::method` is kept.
    """

    name = HASH_SUFFIX.sub("", name)
    output: list[str] = []
    index, depth = 0, 0
    while index < len(name):
        if depth == 0 and name.startswith("::<", index):
            depth, index = 1, index + 3
            continue
        character = name[index]
        if depth:
            if character == "<":
                depth += 1
            elif character == ">" and name[index - 1] != "-":
                depth -= 1
        else:
            output.append(character)
        index += 1
    return "".join(output)


def crate_of(function: str, library: str) -> str:
    """The crate a demangled Rust function belongs to, or the library of a foreign symbol."""

    if function.startswith("["):
        return f"({library})"
    text = function
    while True:
        stripped = text.lstrip("<&*(")
        for prefix in ("mut ", "dyn ", "const ", "impl "):
            if stripped.startswith(prefix):
                stripped = stripped[len(prefix):]
        if stripped == text:
            break
        text = stripped
    match = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text)
    if match is None:
        # `<*const [u8]>::as_ptr`, `<(A, B) as Ord>::cmp`: a method of a built-in type.
        return "std" if text[:1] in "[(" and text[:1] and "::" in function else f"({library})"
    crate, rest = match.group(0), text[match.end():]
    if crate in PRIMITIVES or re.fullmatch(r"[A-Z]", crate):
        # `<usize as core::convert::From<u8>>::from`: the trait's crate.
        return crate_of(rest.split(" as ", 1)[1], library) if " as " in rest else "std"
    if not rest.startswith("::"):
        return f"({library})"  # a C or C++ symbol, or an unqualified name
    return "std" if crate in ("core", "alloc", "std") else crate


PRIMITIVES = frozenset(
    "bool char str fn u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize f32 f64".split())


def crate_of_file(path: str) -> str | None:
    """The crate of a source file: a registry package, the standard library, or `crates/<crate>/src`."""

    if "/rustlib/src/rust/library/" in path or path.startswith("/rustc/"):
        return "std"
    registry = re.search(r"/registry/src/[^/]+/([A-Za-z0-9_-]+?)-\d+\.\d+\.\d+[^/]*/", path)
    if registry:
        return registry.group(1).replace("-", "_")
    local = re.search(r"/crates/([A-Za-z0-9_-]+)/src/", path)
    return local.group(1).replace("-", "_") if local else None


class Symbols:
    """Resolve (library, relative address) to frames, outermost first.

    Names come from samply's presymbolication sidecar; for an executable
    with line tables, `addr2line -i` also restores inlined calls.
    """

    def __init__(self, profile: Mapping[str, Any], sidecar: Mapping[str, Any] | None,
                 inline_binaries: Iterable[Path] = ()) -> None:
        self.libs = profile["libs"]
        strings = sidecar.get("string_table", []) if sidecar else []
        by_code: dict[str, dict[int, str]] = {}
        by_name: dict[str, dict[int, str]] = {}
        for entry in (sidecar or {}).get("data", []):
            table = entry.get("symbol_table", [])
            known = {int(address): clean_name(strings[table[index]["symbol"]])
                     for address, index in entry.get("known_addresses", []) if 0 <= index < len(table)}
            if entry.get("code_id"):
                by_code[entry["code_id"]] = known
            by_name.setdefault(entry.get("debug_name", ""), known)
        self.known = [by_code.get(lib.get("codeId") or "") or by_name.get(lib.get("debugName") or lib["name"]) or {}
                      for lib in self.libs]
        self.inline_paths = {os.fspath(Path(path).resolve()) for path in inline_binaries}
        self.inlined: dict[int, dict[int, list[str]]] = {}
        self.inline_expanded: list[str] = []

    def expand_inlines(self, wanted: Mapping[int, set[int]]) -> None:
        addr2line = shutil.which("addr2line")
        if addr2line is None:
            return
        for lib, addresses in wanted.items():
            path = self.libs[lib].get("path") or ""
            if not path or os.fspath(Path(path).resolve()) not in self.inline_paths or not Path(path).is_file():
                continue
            ordered = sorted(addresses)
            completed = subprocess.run(
                [addr2line, "-a", "-f", "-i", "-C", "-e", path],
                input="".join(f"0x{address:x}\n" for address in ordered),
                capture_output=True, text=True, check=False, timeout=1800,
            )
            if completed.returncode != 0:
                continue
            self.inlined[lib] = parse_addr2line(completed.stdout)
            self.inline_expanded.append(self.libs[lib]["name"])

    def frames(self, lib: int | None, address: int) -> list[tuple[str, str]]:
        library = self.libs[lib]["name"] if lib is not None else "(unknown)"
        outer = self.known[lib].get(address) if lib is not None else None
        chain = self.inlined.get(lib, {}).get(address) if lib is not None else None
        if chain:
            return [(name, library) for name in chain]
        if outer and not re.fullmatch(r"fun_[0-9a-f]+|UNKNOWN", outer):
            return [(outer, library)]
        return [(f"[{library}+0x{address:x}]", library)]


def parse_addr2line(text: str) -> dict[int, list[str]]:
    """`addr2line -a -f -i -C` output to {address: functions outermost first}.

    An inlined call whose DWARF entry has no linkage name comes out
    unqualified (`clone`); it is qualified as `<crate>::…::<name>` from the
    crate of its call-site file where that is known.
    """

    result: dict[int, list[str]] = {}
    current: int | None = None
    entries: list[tuple[str, str]] = []

    def finish() -> None:
        if current is None:
            return
        if not entries or any(name == "??" for name, _ in entries):
            result[current] = []
            return
        names = []
        for name, location in entries:
            name = clean_name(name)
            crate = crate_of_file(location)
            if crate is not None and not name.startswith("<") and "::" not in name.split("<", 1)[0]:
                name = f"{crate}::…::{name.split('<', 1)[0]}"
            names.append(name)
        result[current] = list(reversed(names))

    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        if re.fullmatch(r"0x[0-9a-f]+", line):
            finish()
            current, entries = int(line, 16), []
            index += 1
            continue
        entries.append((line, lines[index + 1] if index + 1 < len(lines) else ""))
        index += 2  # the function line, then its file:line
    finish()
    return result


@dataclass
class ProcessFold:
    pid: str
    process: str
    samples: int = 0
    cpu_microseconds: float = 0.0
    stacks: Counter = field(default_factory=Counter)
    roots: Counter = field(default_factory=Counter)


def fold(profile_file: Path, inline_binaries: Iterable[Path] | None = None) -> tuple[dict[str, Any], list[str]]:
    """Fold a samply profile into a per-process summary and folded stack lines.

    Only on-CPU samples count (samply also emits samples for sleeping threads,
    with a zero CPU delta). With `inline_binaries` omitted, every executable
    (non-`.so`) library of the profile whose path still exists is expanded.
    """

    profile = _read_json(profile_file)
    sidecar_file = sidecar_path(profile_file)
    if not sidecar_file.is_file() and Path(f"{sidecar_file}.gz").is_file():
        sidecar_file = Path(f"{sidecar_file}.gz")
    sidecar = _read_json(sidecar_file) if sidecar_file.is_file() else None
    if inline_binaries is None:
        inline_binaries = [Path(lib["path"]) for lib in profile["libs"]
                           if lib.get("path") and ".so" not in lib["name"] and Path(lib["path"]).is_file()]
    symbols = Symbols(profile, sidecar, inline_binaries)

    def lib_of(thread: Mapping[str, Any], frame: int) -> int | None:
        func = thread["frameTable"]["func"][frame]
        resource = thread["funcTable"]["resource"][func]
        return None if resource is None or resource < 0 else thread["resourceTable"]["lib"][resource]

    def on_cpu(thread: Mapping[str, Any]) -> list[tuple[int, float]]:
        samples = thread["samples"]
        deltas = samples.get("threadCPUDelta") or [None] * len(samples["stack"])
        interval_us = float(profile["meta"].get("interval", 1.0)) * 1000.0
        chosen = []
        for stack, delta in zip(samples["stack"], deltas):
            if stack is None or delta == 0:
                continue
            chosen.append((stack, interval_us if delta is None else float(delta)))
        return chosen

    wanted: dict[int, set[int]] = defaultdict(set)
    for thread in profile["threads"]:
        frames = thread["frameTable"]
        for frame in range(frames["length"]):
            lib = lib_of(thread, frame)
            if lib is not None and frames["address"][frame] is not None:
                wanted[lib].add(int(frames["address"][frame]))
    symbols.expand_inlines(wanted)

    processes: dict[str, ProcessFold] = {}
    for thread in profile["threads"]:
        pid = str(thread.get("pid"))
        process = processes.setdefault(pid, ProcessFold(pid, thread.get("processName") or thread.get("name") or pid))
        stack_table, frame_table = thread["stackTable"], thread["frameTable"]
        memo: dict[int, tuple[tuple[str, str], ...]] = {}

        def resolve(stack: int) -> tuple[tuple[str, str], ...]:
            if stack in memo:
                return memo[stack]
            chain = []
            cursor: int | None = stack
            while cursor is not None:
                chain.append(stack_table["frame"][cursor])
                cursor = stack_table["prefix"][cursor]
            chain.reverse()
            resolved: list[tuple[str, str]] = []
            for frame in chain:
                address = frame_table["address"][frame]
                resolved.extend(symbols.frames(lib_of(thread, frame), -1 if address is None else int(address)))
            memo[stack] = tuple(resolved)
            return memo[stack]

        for stack, cpu in on_cpu(thread):
            frames = resolve(stack)
            if not frames:
                continue
            process.samples += 1
            process.cpu_microseconds += cpu
            process.stacks[frames] += 1
            if thread.get("isMainThread", True):
                process.roots[frames[0][1]] += 1

    summaries = []
    folded: list[str] = []
    for process in sorted(processes.values(), key=lambda item: -item.samples):
        if process.samples == 0:
            continue
        summaries.append(summarize(process))
        label = process.process.replace(";", "_").replace(" ", "_")
        for frames, count in sorted(process.stacks.items(), key=lambda item: -item[1]):
            folded.append(f"{label};" + ";".join(name.replace(";", ",") for name, _ in frames) + f" {count}\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "profile": os.fspath(profile_file),
        "interval_ms": profile["meta"].get("interval"),
        "weight": "on-CPU samples (threadCPUDelta > 0); cpu_seconds sums their CPU deltas",
        "inline_expanded": symbols.inline_expanded,
        "processes": summaries,
    }
    return summary, folded


FIRST_PARTY = re.compile(r"^(krs|k_rust)")
"""Crates whose innermost frame a sample is charged to in `top_first_party` (KRS, k-rust, the collector)."""


def is_first_party(crate: str) -> bool:
    return bool(FIRST_PARTY.match(crate))


def summarize(process: ProcessFold) -> dict[str, Any]:
    total = process.samples
    binary = process.roots.most_common(1)[0][0] if process.roots else None
    self_counts: Counter = Counter()
    inclusive: Counter = Counter()
    crate_self: Counter = Counter()
    crate_inclusive: Counter = Counter()
    first_party: Counter = Counter()
    named = in_binary = attributed = 0
    span_counts: Counter = Counter()
    patterns = [(span, re.compile(pattern)) for span, pattern in SPAN_FUNCTIONS]
    for frames, count in process.stacks.items():
        leaf_name, leaf_lib = frames[-1]
        self_counts[(leaf_name, leaf_lib)] += count
        crate_self[crate_of(leaf_name, leaf_lib)] += count
        if not leaf_name.startswith("["):
            named += count
        if any(lib == binary for _, lib in frames):
            in_binary += count
        if any(lib == binary and not name.startswith("[") for name, lib in frames):
            attributed += count
        for key in set(frames):
            inclusive[key] += count
        innermost = next((frame for frame in reversed(frames) if is_first_party(crate_of(*frame))), None)
        first_party[innermost or ("(no first-party frame)", "")] += count
        for crate in {crate_of(name, lib) for name, lib in frames}:
            crate_inclusive[crate] += count
        names = {name for name, _ in frames}
        for span, pattern in patterns:
            if any(pattern.search(name) for name in names):
                span_counts[span] += count

    def rows(counter: Counter, limit: int) -> list[dict[str, Any]]:
        return [{"function": name, "crate": crate_of(name, lib), "samples": count,
                 "fraction": round(count / total, 4)} for (name, lib), count in counter.most_common(limit)]

    def crate_rows(counter: Counter) -> list[dict[str, Any]]:
        return [{"crate": crate, "samples": count, "fraction": round(count / total, 4)}
                for crate, count in counter.most_common(TOP_CRATES)]

    summary: dict[str, Any] = {
        "process": process.process,
        "pid": process.pid,
        "binary": binary,
        "samples": total,
        "cpu_seconds": round(process.cpu_microseconds / 1e6, 3),
        "named_fraction": round(named / total, 4),
        "binary_fraction": round(in_binary / total, 4),
        "attributed_fraction": round(attributed / total, 4),
        "spans": {span: {"samples": span_counts[span], "fraction": round(span_counts[span] / total, 4)}
                  for span, _ in SPAN_FUNCTIONS if span_counts[span]},
    }
    if total >= DETAILED_MIN_SAMPLES:
        summary |= {
            "top_self": rows(self_counts, TOP_SELF),
            "top_inclusive": rows(inclusive, TOP_INCLUSIVE),
            "top_first_party": rows(first_party, TOP_SELF),
            "crates_self": crate_rows(crate_self),
            "crates_inclusive": crate_rows(crate_inclusive),
        }
    return summary


def render(summary: Mapping[str, Any], limit: int = 15) -> str:
    lines = [f"profile {summary.get('profile')} (inline expansion: {', '.join(summary.get('inline_expanded') or []) or 'none'})"]
    for process in summary["processes"]:
        lines.append(f"\n== {process['process']} (pid {process['pid']}, binary {process['binary']}): "
                     f"{process['samples']} samples, {process['cpu_seconds']} s CPU, "
                     f"leaf named {process['named_fraction']:.1%}, "
                     f"attributed {process.get('attributed_fraction', 0):.1%}")
        for span, value in process.get("spans", {}).items():
            lines.append(f"   span {span:<30} {value['fraction']:7.1%} inclusive")
        for title, key in (("self", "top_self"), ("innermost first-party", "top_first_party"),
                           ("inclusive", "top_inclusive")):
            if key not in process:
                continue
            lines.append(f"  top {title}:")
            for row in process[key][:limit]:
                lines.append(f"   {row['fraction']:7.1%} {row['samples']:>7}  [{row['crate']}] {row['function'][:150]}")
        for title, key in (("crates self", "crates_self"), ("crates inclusive", "crates_inclusive")):
            if key in process:
                lines.append(f"  {title}: " + ", ".join(
                    f"{row['crate']} {row['fraction']:.1%}" for row in process[key][:10]))
    return "\n".join(lines)


# --- the driver: an unprofiled companion, then the profiled run ------------------------------


def build_profiling_krs() -> Path:
    """Build the release `krs` with line tables and symbols into its own scratch target."""

    from support.tools import checkout_scratch, z3_environment

    target = Path(os.environ.get("KRS_PERF_PROFILING_KRS_TARGET",
                                 os.fspath(checkout_scratch() / "perf-krs-profiling-target")))
    print(f"building profiling krs into {target}", flush=True)
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith(("CARGO_PROFILE_", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER"))}
    environment.update(z3_environment())
    environment.update({**PROFILING_KRS_ENVIRONMENT, "CARGO_TARGET_DIR": os.fspath(target)})
    completed = subprocess.run(
        ["cargo", "+stable", "build", "--release", "--locked", "--offline", "-p", "krs-cli", "--bin", "krs"],
        cwd=ROOT, env=environment, capture_output=True, text=True, check=False)
    if completed.returncode != 0:
        raise GateError(f"building the profiling krs failed:\n{completed.stderr[-4000:]}")
    return target / "release/krs"


def main_run(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="sample.py run", description=(
        "Run a bench.py selection twice with one profiling krs: unprofiled (the companion whose numbers "
        "are quoted), then under `--profile samply`. Other arguments pass through to bench.py."))
    parser.add_argument("--collector", choices=list(COLLECTOR_VARIANTS), default="as-is",
                        help="collector build: as-is (dev, opt-level 0, full debuginfo), line-tables, or "
                             "optimized (opt-level 3, line tables)")
    parser.add_argument("--krs", type=Path, help="profile this krs instead of building the profiling krs")
    parser.add_argument("--label", default="samply")
    parser.add_argument("--no-companion", action="store_true", help="skip the unprofiled companion run")
    parser.add_argument("--dry-run", action="store_true", help="print the two bench.py commands")
    arguments, rest = parser.parse_known_args(argv)
    if "--profile" in rest:
        parser.error("--profile is set by sample.py")
    variant = [f"--env={key}={value}" for key, value in COLLECTOR_VARIANTS[arguments.collector].items()]
    label = f"{arguments.label}-{arguments.collector}"
    krs = os.fspath(arguments.krs) if arguments.krs else "<profiling krs>"
    common = [sys.executable, os.fspath(BENCH), *rest, *variant, "--krs", krs]
    commands = []
    if not arguments.no_companion:
        commands.append([*common, "--label", f"{label}-companion"])
    commands.append([*common, "--profile", NAME, "--label", label])
    if arguments.dry_run:
        for command in commands:
            print(" ".join(command))
        return 0
    if arguments.krs is None:
        krs = os.fspath(build_profiling_krs())
        commands = [[krs if part == "<profiling krs>" else part for part in command] for command in commands]
    status = 0
    for command in commands:
        print("+ " + " ".join(command), flush=True)
        status = max(status, subprocess.run(command, cwd=ROOT, check=False).returncode)
    return status


def main_fold(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="sample.py fold", description="fold a samply profile and print it")
    parser.add_argument("profile", type=Path)
    parser.add_argument("--binary", type=Path, action="append",
                        help="executable whose inlined calls to expand (default: every executable still present)")
    parser.add_argument("--json", type=Path, help="also write the summary here")
    parser.add_argument("--folded", type=Path, help="also write folded stacks here (gzip when it ends in .gz)")
    arguments = parser.parse_args(argv)
    summary, folded = fold(arguments.profile, arguments.binary)
    if arguments.json:
        arguments.json.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    if arguments.folded:
        opener = gzip.open if arguments.folded.suffix == ".gz" else open
        with opener(arguments.folded, "wt", encoding="utf-8") as handle:
            handle.writelines(folded)
    print(render(summary))
    return 0


def main_show(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(prog="sample.py show", description="print a stored summary")
    parser.add_argument("summary", type=Path)
    parser.add_argument("--limit", type=int, default=15)
    arguments = parser.parse_args(argv)
    print(render(_read_json(arguments.summary), arguments.limit))
    return 0


def main(argv: Sequence[str]) -> int:
    commands = {"run": main_run, "fold": main_fold, "show": main_show}
    if not argv or argv[0] not in commands:
        print(__doc__, file=sys.stderr)
        return 2
    return commands[argv[0]](argv[1:])


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except GateError as error:
        print(f"FAIL sampled profile: {error}", file=sys.stderr)
        raise SystemExit(1)
