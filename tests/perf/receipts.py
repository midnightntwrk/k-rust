"""The versioned per-run receipt and the evidence it collects.

A receipt (`krs-perf-receipt/1`) is one JSON object per measured run. It is
self-contained: every receipt repeats the revision, pins, toolchain, host, and
environment context of the harness invocation that wrote it, so a receipt
copied out of its set still says what it measured. Receipts are written under
the harness scratch root, indexed by revision, and are never committed.
"""

from __future__ import annotations

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
from typing import Any, Iterable, Mapping

from support import ROOT
from support.hashing import sha256_file
from support.process import BASE_ENVIRONMENT


SCHEMA = "krs-perf-receipt/1"
TIMINGS_SCHEMA_PREFIX = "krs-timings/"


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _output(command: list[str], environment: Mapping[str, str] | None = None) -> str | None:
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            env={**os.environ, **BASE_ENVIRONMENT, **(environment or {})},
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if completed.returncode != 0:
        return None
    return completed.stdout


def revision() -> dict[str, Any]:
    head = (_output(["git", "-C", os.fspath(ROOT), "rev-parse", "HEAD"]) or "").strip() or None
    status = _output(["git", "-C", os.fspath(ROOT), "status", "--porcelain", "--untracked-files=no"])
    dirty_paths = [line[3:] for line in (status or "").splitlines() if line.strip()]
    return {"commit": head, "dirty": bool(dirty_paths), "dirty_paths": dirty_paths[:50]}


def revision_key(rev: Mapping[str, Any]) -> str:
    commit = str(rev.get("commit") or "unknown")[:12]
    return f"{commit}-dirty" if rev.get("dirty") else commit


def parse_rustc_verbose(text: str) -> dict[str, str]:
    """`rustc -vV` as a table: `release`, `host`, `commit-hash`, `LLVM version`, ..."""

    lines = text.strip().splitlines()
    parsed = {"version": lines[0]} if lines else {}
    for line in lines[1:]:
        key, separator, value = line.partition(": ")
        if separator:
            parsed[key.strip()] = value.strip()
    return parsed


def toolchain(environment: Mapping[str, str]) -> dict[str, Any]:
    rustc = _output(["rustc", "-vV"], environment) or ""
    cargo = (_output(["cargo", "-V"], environment) or "").strip() or None
    first = lambda text: (text or "").strip().splitlines()[0] if (text or "").strip() else None  # noqa: E731
    linker_variable = "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER"
    cargo_home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
    cargo_config = next(
        (path for path in (cargo_home / "config.toml", cargo_home / "config") if path.is_file()), None
    )
    return {
        "rustc_vv": parse_rustc_verbose(rustc),
        "cargo_version": cargo,
        "rustup_toolchain": environment.get("RUSTUP_TOOLCHAIN"),
        "linker": {
            "configured": os.environ.get(linker_variable),
            "cc": first(_output(["cc", "--version"])),
            "ld": first(_output(["ld", "--version"])),
        },
        "cargo_home_config": (
            {"path": os.fspath(cargo_config), "sha256": sha256_file(cargo_config)} if cargo_config else None
        ),
    }


def host() -> dict[str, Any]:
    model = None
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("model name"):
                model = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    memory = None
    try:
        for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("MemTotal:"):
                memory = int(line.split()[1]) * 1024
                break
    except OSError:
        pass
    affinity = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    return {
        "cpu_model": model,
        "logical_cpus": os.cpu_count(),
        "usable_cpus": affinity,
        "memory_bytes": memory,
        "kernel": platform.release(),
        "machine": platform.machine(),
        "python": platform.python_version(),
    }


def load_average() -> list[float] | None:
    try:
        return [round(value, 2) for value in os.getloadavg()]
    except OSError:
        return None


def pins() -> dict[str, Any]:
    from support.lock import krs_lock

    return json.loads(json.dumps(krs_lock()))


# --- krs --timings ----------------------------------------------------------


def ingest_timings(path: Path) -> tuple[str, dict[str, Any] | None]:
    """Read a `krs --timings` document: (status, normalized document or None).

    The status is `collected`, `missing` (the flag was passed but no file was
    written), or `invalid`. Normalization keeps the whole original document
    and adds `spans` as `[{id, seconds, depth}]` whatever the source calls
    them (`spans` or k-rust's `phases` with `name`), plus `counters` as a flat
    name-to-number table when the document carries any.
    """

    if not path.is_file():
        return "missing", None
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return "invalid", None
    if not isinstance(document, dict):
        return "invalid", None
    return "collected", normalize_timings(document)


def ingest_counters(path: Path) -> tuple[str, dict[str, Any] | None]:
    """Read a `krs --counters` document (`krs-counters/1`): (status, {schema, counters, document})."""

    if not path.is_file():
        return "missing", None
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return "invalid", None
    if not isinstance(document, dict):
        return "invalid", None
    return "collected", {
        "schema": document.get("schema"),
        "counters": flatten_counters(document.get("counters")) or {},
        "document": dict(document),
    }


def normalize_timings(document: Mapping[str, Any]) -> dict[str, Any]:
    raw = document.get("spans", document.get("phases", []))
    spans = []
    for item in raw if isinstance(raw, list) else []:
        if not isinstance(item, Mapping):
            continue
        identifier = item.get("id", item.get("name"))
        seconds = item.get("seconds")
        if isinstance(identifier, str) and isinstance(seconds, (int, float)):
            spans.append({"id": identifier, "seconds": float(seconds), "depth": int(item.get("depth", 0))})
    return {
        "schema": document.get("schema"),
        "total_wall_seconds": _number(document.get("total_wall_seconds")),
        "unattributed_seconds": _number(document.get("unattributed_seconds")),
        "spans": spans,
        "counters": flatten_counters(document.get("counters")),
        "document": dict(document),
    }


def flatten_counters(value: Any, prefix: str = "") -> dict[str, float] | None:
    """Counters as dotted-name to number; nested tables and `{id, value}` lists flatten."""

    if value is None:
        return None
    flat: dict[str, float] = {}

    def visit(item: Any, name: str) -> None:
        if isinstance(item, bool):
            return
        if isinstance(item, (int, float)):
            flat[name] = item
        elif isinstance(item, Mapping):
            for key, child in item.items():
                visit(child, f"{name}.{key}" if name else str(key))
        elif isinstance(item, list):
            for child in item:
                if isinstance(child, Mapping) and ("id" in child or "name" in child) and "value" in child:
                    key = str(child.get("id", child.get("name")))
                    visit(child["value"], f"{name}.{key}" if name else key)

    visit(value, prefix)
    return flat


def _number(value: Any) -> float | None:
    return float(value) if isinstance(value, (int, float)) and not isinstance(value, bool) else None


# --- cargo --timings --------------------------------------------------------


_UNIT_DATA = re.compile(r"const UNIT_DATA = (\[.*?\n\]);", re.DOTALL)
_DURATION = re.compile(r"^DURATION = ([0-9.]+);", re.MULTILINE)


def cargo_units(html: str, names: Iterable[str]) -> dict[str, Any] | None:
    """The per-unit rows Cargo's timing report embeds, for the named packages.

    Returns `{total_seconds, units: [{name, target, mode, start, duration}]}`
    for units whose package name is in `names` or starts with
    `krs-generated-collector-`, or None when the report has no unit table.
    """

    match = _UNIT_DATA.search(html)
    if match is None:
        return None
    try:
        rows = json.loads(match.group(1))
    except ValueError:
        return None
    wanted = set(names)
    units = [
        {
            "name": row.get("name"),
            "target": str(row.get("target", "")).strip(),
            "mode": row.get("mode"),
            "start": row.get("start"),
            "duration": row.get("duration"),
        }
        for row in rows
        if isinstance(row, Mapping)
        and (row.get("name") in wanted or str(row.get("name", "")).startswith("krs-generated-collector-"))
    ]
    total = _DURATION.search(html)
    return {"total_seconds": float(total.group(1)) if total else None, "units": units}


def collect_cargo_timings(target: Path, destination: Path, names: Iterable[str]) -> dict[str, Any] | None:
    report = target / "cargo-timings" / "cargo-timing.html"
    if not report.is_file():
        return None
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(report, destination)
    parsed = cargo_units(report.read_text(encoding="utf-8", errors="replace"), names)
    return {"html": destination.name, **(parsed or {"total_seconds": None, "units": []})}


# --- receipts on disk ---------------------------------------------------------


def write(receipt: Mapping[str, Any], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load(paths: Iterable[Path]) -> list[dict[str, Any]]:
    """Every receipt under the given files or directories, recursively."""

    found: list[dict[str, Any]] = []
    for path in paths:
        files = sorted(path.rglob("*.json")) if path.is_dir() else [path]
        for file in files:
            try:
                data = json.loads(file.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                continue
            if isinstance(data, dict) and data.get("schema") == SCHEMA:
                data["_path"] = os.fspath(file)
                found.append(data)
    return found


def append_index(root: Path, entry: Mapping[str, Any]) -> None:
    root.mkdir(parents=True, exist_ok=True)
    with (root / "index.jsonl").open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry, sort_keys=True) + "\n")
