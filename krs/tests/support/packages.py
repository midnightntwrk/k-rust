"""The standalone Rust packages under tests/ and the checks their gates run.

Every tracked `Cargo.toml` under `tests/` that declares its own `[workspace]`
and is not under a `fixtures/` directory has one row here,
and `tests/repo-hygiene/verify.py` rejects one that has none.
Each row names the gate that owns the package.

An authored package is source the project maintains,
so its gate runs rustfmt and `krs fmt` through `check_packages`,
and `tests/package-lint/verify.py` runs Clippy with warnings denied
and a check with the `Krs.lock` MSRV toolchain over every authored package through `lint_packages`.
The lint is code hygiene of the package source, not a check of what KRS does with it,
so it is a step of its own (`tests/gates.sh lint`, run by CI) rather than part of each gate.
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
    Package("tests/builtin-domains/Cargo.toml", "builtin-domains", "authored"),
    Package("tests/configuration-cells/Cargo.toml", "configuration-cells", "authored"),
    Package("tests/verification-surface/Cargo.toml", "verification-surface", "authored"),
    Package("tests/patterns-functions/Cargo.toml", "patterns-functions", "authored"),
    Package("tests/sorts-algebra/Cargo.toml", "sorts-algebra", "authored"),
    Package("tests/native-claims/Cargo.toml", "native-claims", "authored"),
    Package("tests/native-finite-claims/Cargo.toml", "native-finite-claims", "authored"),
    Package("tests/imp/compatibility/diagnostics/krs-analysis/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/diagnostics/rust-expansion/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/baseline/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/private-move/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/public-move-pinned/Cargo.toml", "imp", "fixture"),
    Package("tests/imp/compatibility/stable-names/public-move/Cargo.toml", "imp", "fixture"),
)


def check_packages(gate: str, *, krs: Path, env: Mapping[str, str]) -> None:
    """Format-check every authored package that `gate` owns.

    `krs` is the caller's KRS binary, which checks the whole package without path arguments.
    """

    owned = [package for package in PACKAGES if package.gate == gate]
    if not owned:
        raise GateError(f"no standalone packages are registered for gate {gate!r}")
    format_environment = {**env, **rustfmt_environment()}
    for package in owned:
        if package.kind != "authored":
            continue
        manifest = ROOT / package.manifest
        command = ["cargo", "+stable", "fmt", "--check", "--manifest-path", os.fspath(manifest)]
        if "package" not in load_toml(manifest):
            # A virtual manifest has no package of its own to format.
            command.insert(3, "--all")
        run(command, timeout=300, environment=env)
        run(
            [os.fspath(krs), "fmt", "--check", "--manifest-path", os.fspath(manifest)],
            timeout=300,
            environment=format_environment,
        )


def lint_packages(*, env: Mapping[str, str], target_dir: Path) -> list[Package]:
    """Lint and MSRV-check every authored package; return the packages checked.

    Each package's locked dependencies are fetched first, which needs no network
    when they are already downloaded or `CARGO_NET_OFFLINE` is set.
    `target_dir` is the Cargo target directory both toolchains build in.
    """

    environment = {**env, "CARGO_TARGET_DIR": os.fspath(target_dir)}
    authored = [package for package in PACKAGES if package.kind == "authored"]
    for package in authored:
        manifest = os.fspath(ROOT / package.manifest)
        run(
            ["cargo", "+stable", "fetch", "--locked", "--manifest-path", manifest],
            timeout=900,
            environment=environment,
        )
        run(
            [
                "cargo", "+stable", "clippy", "--manifest-path", manifest,
                "--all-targets", "--locked", "--offline", "--", "-D", "warnings",
            ],
            timeout=900,
            environment=environment,
        )
        run(
            [
                "cargo", f"+{msrv()}", "check", "--manifest-path", manifest,
                "--all-targets", "--locked", "--offline",
            ],
            timeout=900,
            environment=environment,
        )
    return authored
