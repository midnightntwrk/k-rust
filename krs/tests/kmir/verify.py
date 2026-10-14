#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KMIR operational slice."""

from __future__ import annotations

from pathlib import Path
from typing import Mapping
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, semantics, entry  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
import native  # noqa: E402


PROBES = (
    (
        "block lookup command",
        "Execution::ExecBlock(list::get(program, index))",
        "ExecBlock",
        "    ExecBlock { block: BasicBlock },",
    ),
    (
        "entry block command",
        "Execution::ExecBlockIdx(0)",
        "ExecBlockIdx",
        "    ExecBlockIdx { index: Int },",
    ),
    (
        "continuation constructor",
        "continuation: EvaluationContinuation::BinaryRight { place, operation, rhs, checked }",
        "BinaryRight",
        "    BinaryRight {",
    ),
    (
        "configuration target",
        "    for Machine;",
        "Machine",
        "pub struct Machine {",
    ),
    (
        "local binding",
        "value: int::add(lhs, rhs)",
        "lhs",
        "checked: false, operation: MirBinaryOp::BinOpAdd(), lhs: Value::Integer { value: lhs, width, signed }",
    ),
    (
        "return constructor",
        "ret_val: ReturnValue::Returned(value)",
        "Returned",
        "    Returned { value: MirValue },",
    ),
)


PORT = semantics.Port(
    label="KMIR",
    key="kmir",
    checkout=ROOT.parent / "inspirations/runtimeverification/mir-semantics",
    descriptors=1222,
    lsp_probes=PROBES,
    lsp_diagnostic_timeout=600,
)


def definition_checks(artifacts: Path, gate: Path, environment: Mapping[str, str]) -> None:
    """Require the typed constructs declared beside the corpus pins."""

    semantics.definition_expectations(
        artifacts, gate, PORT.here / "definition-checks.toml", environment
    )


HOOKS = semantics.Hooks(
    description=__doc__,
    label="readable KMIR operational slice",
    java_help="also run the pinned K toolchain behavior comparison and proof",
    claim_count=1,
    configuration_variables=native.configuration_variables,
    definition_checks=definition_checks,
)


def main() -> int:
    return semantics.run_port(PORT, HOOKS)


if __name__ == "__main__":
    entry(HOOKS.label, main, errors=(OSError,))
