"""`Krs.lock`: the single source of the toolchain and schema pins every gate uses.

A gate reads versions from here instead of repeating them in its own ledger or
as literals, so a toolchain or schema bump edits one file.
"""

from __future__ import annotations

import functools
import re
from typing import Any, Mapping

from support import ROOT, GateError
from support.pins import load_toml, table


LOCK_PATH = ROOT / "Krs.lock"


@functools.cache
def krs_lock() -> Mapping[str, Any]:
    lock = load_toml(LOCK_PATH)
    if lock.get("schema") != 1:
        raise GateError(f"unsupported Krs.lock schema: {lock.get('schema')!r}")
    return lock


def section(name: str) -> Mapping[str, Any]:
    return table(krs_lock().get(name), f"Krs.lock [{name}]")


def value(section_name: str, key: str) -> Any:
    found = section(section_name).get(key)
    if found in (None, ""):
        raise GateError(f"Krs.lock [{section_name}] lacks {key}")
    return found


def k_version() -> str:
    return str(value("k", "version"))


def k_commit() -> str:
    return str(value("k", "commit"))


def msrv() -> str:
    return str(value("cargo", "msrv"))


def z3_version() -> str:
    return str(value("solver", "version"))


def krs_ir_schema() -> int:
    """The one schema version of descriptor bundles, Semantic IR, and Definition IR.

    A `krs-ir` unit test requires `SchemaVersion::CURRENT` to equal this pin,
    so gates read it here rather than from Rust source.
    """

    return int(value("schemas", "krs_ir"))


_RUSTC_VERSION = re.compile(r"^rustc (\d+)\.(\d+)\.(\d+)(?:-[0-9A-Za-z.-]+)? ")


def rustc_version(reported: str) -> tuple[int, int, int]:
    """Parse the version out of one `rustc --version` line."""

    match = _RUSTC_VERSION.match(reported)
    if match is None:
        raise GateError(f"cannot parse the rustc version from {reported!r}")
    return int(match.group(1)), int(match.group(2)), int(match.group(3))


def require_stable_at_least_msrv(reported: str) -> None:
    """Accept any stable rustc at or above the `Krs.lock` MSRV."""

    observed = rustc_version(reported)
    minimum = rustc_version(f"rustc {msrv()} ")
    if "-nightly" in reported or "-beta" in reported or "-dev" in reported:
        raise GateError(f"the native frontend toolchain is not a stable rustc: {reported}")
    if observed < minimum:
        raise GateError(f"stable rustc {reported} is older than the Krs.lock MSRV {msrv()}")
