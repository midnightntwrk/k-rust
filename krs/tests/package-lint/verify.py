#!/usr/bin/env python3
"""Lint and MSRV-check every authored standalone package under `tests/`.

Every authored row of `tests/support/packages.py` passes Clippy on current
stable with warnings denied and `cargo check` on the `Krs.lock` MSRV toolchain,
both over all targets with the locked dependencies.
The owning gates format-check the same packages; this entry point holds the
lint because it judges the package source rather than what KRS does with it,
so the light gates do not pay for two more compilations of every package.
It builds in the shared gate target (`support.tools.tool_target`) and needs
the Z3 library only because one package links k-rust.

    krs/tests/gates.sh lint
"""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import entry  # noqa: E402
from support.lock import msrv  # noqa: E402
from support.packages import lint_packages  # noqa: E402
from support.tools import tool_target, z3_environment  # noqa: E402


def main() -> None:
    checked = lint_packages(env=z3_environment(), target_dir=tool_target())
    for package in checked:
        print(f"PASS {package.manifest}: Clippy -D warnings and MSRV {msrv()} check")


if __name__ == "__main__":
    entry("standalone package lint", main)
