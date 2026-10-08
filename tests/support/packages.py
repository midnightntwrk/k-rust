"""The standalone Rust packages under tests/ and the checks their gates run.

Every tracked `Cargo.toml` under `tests/` that declares its own `[workspace]`
and is not under a `fixtures/` directory has one row here,
and `tests/repo-hygiene/verify.py` rejects one that has none.
Each row names the gate that owns the package.

An authored package is source the project maintains,
so its gate runs rustfmt, `krs fmt`, Clippy with warnings denied,
and a check with the `Krs.lock` MSRV toolchain through `check_packages`.
A fixture package is a pinned input to a compatibility probe;
its source is deliberately shaped for the probe,
so its gate checks the probe's result instead of linting it.
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
from typing import Mapping

from support import ROOT, GateError
from support.lock import msrv
from support.pins import load_toml
from support.process import run
from support.tools import rustfmt_environment


@dataclass(frozen=True)
class Package:
    manifest: str
    gate: str
    kind: str


PACKAGES = (
    Package("tests/imp/rust-definition/Cargo.toml", "imp", "authored"),
    Package("tests/imp/expanded-definition/Cargo.toml", "imp", "authored"),
    Package("tests/imp/oracle/artifact-probe/Cargo.toml", "imp", "authored"),
    Package("tests/imp-state/rust-definition/Cargo.toml", "imp-state", "authored"),
    Package("tests/precedence-associativity/rust-definition/Cargo.toml", "precedence-associativity", "authored"),
    Package("tests/tour-minimal/Cargo.toml", "tour-minimal", "authored"),
    Package("tests/tour-imp/Cargo.toml", "tour-imp", "authored"),
    Package("tests/tour-composition/Cargo.toml", "tour-composition", "authored"),
    Package("tests/tour-negatives/Cargo.toml", "tour-negatives", "authored"),
    Package("tests/grammar-lexing/Cargo.toml", "grammar-lexing", "authored"),
    Package("tests/rule-forms/Cargo.toml", "rule-forms", "authored"),
    Package("tests/imp/compatibility/diagnostics/krs-analysis/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/diagnostics/rust-expansion/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/baseline/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/private-move/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/public-move-pinned/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/public-move/Cargo.toml", "imp", "fixture"),
)


def check_packages(gate: str, *, krs: Path, env: Mapping[str, str], target_dir: Path) -> None:
    """Format-check, lint, and MSRV-check every authored package that `gate` owns.

    `krs` is the caller's KRS binary, which checks the whole package without path arguments.
    `target_dir` is the caller's own Cargo target directory.
    """

    owned = [package for package in PACKAGES if package.gate == gate]
    if not owned:
        raise GateError(f"no standalone packages are registered for gate {gate!r}")
    environment = {**env, "CARGO_TARGET_DIR": os.fspath(target_dir)}
    format_environment = {**environment, **rustfmt_environment()}
    for package in owned:
        if package.kind != "authored":
            continue
        manifest = ROOT / package.manifest
        command = ["cargo", "+stable", "fmt", "--check", "--manifest-path", os.fspath(manifest)]
        if "package" not in load_toml(manifest):
            # A virtual manifest has no package of its own to format.
            command.insert(3, "--all")
        run(command, timeout=300, environment=environment)
        run(
            [os.fspath(krs), "fmt", "--check", "--manifest-path", os.fspath(manifest)],
            timeout=300,
            environment=format_environment,
        )
        run(
            [
                "cargo", "+stable", "clippy", "--manifest-path", os.fspath(manifest),
                "--all-targets", "--locked", "--offline", "--", "-D", "warnings",
            ],
            timeout=900,
            environment=environment,
        )
        run(
            [
                "cargo", f"+{msrv()}", "check", "--manifest-path", os.fspath(manifest),
                "--all-targets", "--locked", "--offline",
            ],
            timeout=900,
            environment=environment,
        )
