#!/usr/bin/env python3
"""Focused rust-analyzer qualification for the readable KMIR slice."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT  # noqa: E402
from support.lsp import probe  # noqa: E402


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


if __name__ == "__main__":
    probe(ROOT / "semantics/kmir", PROBES, diagnostic_timeout=600)
