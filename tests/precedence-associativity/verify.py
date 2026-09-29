#!/usr/bin/env python3
"""End-to-end bare/explicit associativity qualification."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, entry  # noqa: E402
from support.lock import k_version  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "rust-definition" / "Cargo.toml"
PACKAGE = "krs-precedence-associativity"
MODULE = "KRS-PRECEDENCE-ASSOCIATIVITY"


def main() -> int:
    kompile = k_tool("kompile", k_version())
    kast = k_tool("kast", k_version())

    with tempfile.TemporaryDirectory(prefix="krs-precedence-associativity-") as temporary:
        workspace = Path(temporary)
        target = workspace / "target"
        environment = {**z3_environment(), "CARGO_TARGET_DIR": str(target)}
        binary = build(environment, target=target)
        check_packages(
            "precedence-associativity", env=environment, target_dir=target
        )
        emitted = workspace / "emitted"
        invocation = Invocation(binary, MANIFEST, PACKAGE, "main")
        invocation.run("check", environment=environment)
        invocation.run("emit-k", "--output", emitted, environment=environment)

        source = (emitted / "definition.k").read_text(encoding="utf-8")
        if source.count("syntax non-assoc") != 1:
            raise GateError("emitted definition must contain one explicit non-assoc sentence")

        compiled = workspace / "compiled"
        run(
            [
                kompile,
                emitted / "definition.k",
                "--main-module",
                MODULE,
                "--syntax-module",
                MODULE,
                "--backend",
                "llvm",
                "--output-definition",
                compiled,
            ]
        )

        def parse(program: Path, *, check: bool) -> int:
            return run(
                [
                    kast,
                    "--definition",
                    compiled,
                    "--module",
                    MODULE,
                    "--sort",
                    "Probe",
                    "--output",
                    "json",
                    program,
                ],
                timeout=60,
                check=check,
            ).returncode

        parse(HERE / "corpus" / "accepted" / "iterated-unary.probe", check=True)
        rejected = HERE / "corpus" / "rejected" / "non-associative-equality.probe"
        if parse(rejected, check=False) == 0:
            raise GateError("explicit non_assoc direct nesting unexpectedly parsed")

    print("PASS precedence/associativity: bare iterated unary accepted; explicit non_assoc nesting rejected")
    return 0


if __name__ == "__main__":
    entry("precedence/associativity", main, errors=(OSError,))
