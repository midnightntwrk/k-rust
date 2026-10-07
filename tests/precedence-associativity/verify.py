#!/usr/bin/env python3
"""End-to-end bare/explicit associativity qualification."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError, entry, krs_gate  # noqa: E402
from support.krs import Invocation, build  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.pins import Ledger  # noqa: E402
from support.reference import (  # noqa: E402
    Key, Pin, Snapshot, add_refresh_argument, repository_inputs, substitute,
)
from support.tools import z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "rust-definition" / "Cargo.toml"
PACKAGE = "krs-precedence-associativity"
MODULE = "KRS-PRECEDENCE-ASSOCIATIVITY"
PINS = HERE / "pins.json"
TOOLS = ("kompile", "kast")
ACCEPTED = HERE / "corpus" / "accepted" / "iterated-unary.probe"
REJECTED = HERE / "corpus" / "rejected" / "non-associative-equality.probe"
ASSOCIATIVITY_ERROR = "[Error] Inner Parser: Associativity filter exception."
first_line = substitute(r"\n[\s\S]*", "\n")
"""K reports the rejected nesting at either child from run to run, so only the first diagnostic line is kept."""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="run the gate and rewrite the output pins it measured")
    add_refresh_argument(parser)
    arguments = parser.parse_args()
    pins = Ledger(PINS, record=arguments.record)
    if pins.get("schema") != 1:
        raise GateError("pins.json is not the schema-1 precedence/associativity ledger")

    with tempfile.TemporaryDirectory(prefix="krs-precedence-associativity-") as temporary:
        workspace = Path(temporary)
        target = workspace / "target"
        environment = {**z3_environment(), "CARGO_TARGET_DIR": str(target)}
        binary = build(environment, target=target)
        check_packages(
            "precedence-associativity", krs=binary, env=environment, target_dir=target
        )
        emitted = workspace / "emitted"
        invocation = Invocation(binary, MANIFEST, PACKAGE, "main")
        invocation.run("check", environment=environment)
        invocation.run("emit-k", "--output", emitted, environment=environment)

        gate = krs_gate.build(target, environment=environment)
        rows = krs_gate.ir_query(gate, emitted, {"kind": "sentences", "sentence_kind": "associativity"}, environment=environment)["rows"]
        if sum(row["associativity"] == "non_associative" for row in rows) != 1:
            raise GateError("emitted definition must contain one explicit non-assoc sentence")

        # The emitted definition.k is keyed by its digest, so any change to
        # what KRS emits changes the pinned reference digest.
        k = Snapshot(
            "precedence-associativity/parse", Key(tools=TOOLS, inputs=repository_inputs([ACCEPTED, REJECTED])),
            workspace=workspace, refresh=arguments.refresh_reference, pin=Pin(pins, "parse"),
        )
        compiled = workspace / "compiled"
        compile_process = k.run(
            "kompile/definition",
            "kompile",
            [
                emitted / "definition.k",
                "--main-module",
                MODULE,
                "--syntax-module",
                f"{MODULE}-SYNTAX",
                "--backend",
                "llvm",
                "--output-definition",
                compiled,
            ],
            timeout=600,
        )
        if compile_process.returncode != 0:
            raise GateError(f"kompile rejected the emitted definition:\n{compile_process.stderr}")

        def parse(label: str, program: Path) -> subprocess.CompletedProcess[str]:
            return k.run(
                f"kast/{label}",
                "kast",
                [
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
                streams={"stderr": first_line},
            )

        if parse("accepted", ACCEPTED).returncode != 0:
            raise GateError("bare iterated unary syntax was rejected")
        rejected = parse("rejected", REJECTED)
        if rejected.returncode == 0 or not rejected.stderr.startswith(ASSOCIATIVITY_ERROR):
            raise GateError(f"explicit non_assoc direct nesting was not rejected by the associativity filter: {rejected.stderr}")
        print(f"PASS precedence/associativity reference snapshot: {k.finish()}")
    pins.finish("precedence/associativity")

    print("PASS precedence/associativity: bare iterated unary accepted; explicit non_assoc nesting rejected")
    return 0


if __name__ == "__main__":
    entry("precedence/associativity", main, errors=(OSError,))
