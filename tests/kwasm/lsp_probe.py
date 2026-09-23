#!/usr/bin/env python3
"""Focused rust-analyzer qualification for the readable KWasm slice."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT  # noqa: E402
from support.lsp import probe  # noqa: E402


PROBES = (
    (
        "ordinary cell constructor",
        "valstack: Stack::Cons(Value::Integer(IntegerType::I32, rhs)",
        "Cons",
        "    Cons { head: Val, tail: ValStack },",
    ),
    (
        "ordinary cell result constructor",
        "valstack: Stack::Cons(Value::Integer(ty, value), stack)",
        "Cons",
        "    Cons { head: Val, tail: ValStack },",
    ),
    (
        "function application",
        "instrs: [crate::IntBinOp(IntegerType::I32, op, lhs, rhs), ..]",
        "IntBinOp",
        "pub struct IntBinOp {",
    ),
    (
        "configuration target",
        "    for Machine;",
        "Machine",
        "pub struct Machine {",
    ),
    (
        "binding reference",
        "instrs: [crate::IntBinOp(IntegerType::I32, op, lhs, rhs), ..]",
        "rhs",
        "valstack: Stack::Cons(Value::Integer(IntegerType::I32, rhs)",
    ),
    (
        "trap constructor",
        "instrs: [Trap(), ..]",
        "Trap",
        "    Trap(),",
    ),
)


if __name__ == "__main__":
    probe(ROOT / "semantics/kwasm", PROBES, diagnostic_timeout=90)
