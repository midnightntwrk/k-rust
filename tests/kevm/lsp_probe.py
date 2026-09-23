#!/usr/bin/env python3
"""Focused rust-analyzer qualification for the readable KEVM slice."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT  # noqa: E402
from support.lsp import probe  # noqa: E402


PROBES = (
    (
        "program lookup",
        "k: [crate::Lookup { program, pc }, ..]",
        "Lookup",
        "pub struct Lookup {",
    ),
    (
        "stack result constructor",
        "word_stack: Stack::StackCons(crate::Chop(value), stack)",
        "StackCons",
        "    StackCons { head: Int, tail: WordStack },",
    ),
    (
        "push preparation function",
        "k: [crate::PreparePush { op: Operation::Push { width, value }, stack, gas, cost: 3 }, ..]",
        "PreparePush",
        "pub struct PreparePush {",
    ),
    (
        "configuration target",
        "    for Machine;",
        "Machine",
        "pub struct Machine {",
    ),
    (
        "width binding",
        "pc: int::add(pc, int::add(width, 1))",
        "width",
        "k: [GasResult::EnoughGas(Operation::Push { width, value }, remaining), ..]",
    ),
    (
        "exception constructor",
        "status_code: Status::OutOfGas()",
        "OutOfGas",
        "    OutOfGas(),",
    ),
)


if __name__ == "__main__":
    probe(ROOT / "semantics/kevm", PROBES, diagnostic_timeout=600)
