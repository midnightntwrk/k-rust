#!/usr/bin/env python3
"""End-to-end C7 bare/explicit associativity qualification."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from support.process import run  # noqa: E402
from support.tools import k_tool  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "rust-definition" / "Cargo.toml"
PACKAGE = "krs-c7-associativity"
MODULE = "KRS-C7-ASSOCIATIVITY"
K_VERSION = "7.1.337"


def main() -> int:
    kompile = k_tool("kompile", K_VERSION)
    kast = k_tool("kast", K_VERSION)

    with tempfile.TemporaryDirectory(prefix="krs-c7-") as temporary:
        workspace = Path(temporary)
        target = workspace / "target"
        environment = {"CARGO_TARGET_DIR": str(target)}
        run(["cargo", "build", "--locked", "-p", "krs-cli", "--bin", "krs"], environment=environment)
        binary = target / "debug" / "krs"

        emitted = workspace / "emitted"
        selection: list[str | Path] = [
            "--manifest-path",
            MANIFEST,
            "--package",
            PACKAGE,
            "--definition",
            "main",
        ]
        run([binary, "check", *selection], environment=environment)
        run([binary, "emit-k", *selection, "--output", emitted], environment=environment)

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

    print("PASS C7: bare iterated unary accepted; explicit non_assoc nesting rejected")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, GateError) as error:
        print(f"FAIL C7: {error}", file=sys.stderr)
        raise SystemExit(1) from error
