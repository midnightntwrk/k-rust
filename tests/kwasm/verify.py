#!/usr/bin/env python3
"""Fail-closed qualification gate for the readable KWasm integer slice."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, semantics, entry  # noqa: E402
from kwasm import native  # noqa: E402


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


PORT = semantics.Port(
    label="KWasm",
    key="kwasm",
    checkout=ROOT.parent / "inspirations/runtimeverification/wasm-semantics",
    descriptors=60,
    lsp_probes=PROBES,
    lsp_diagnostic_timeout=90,
)


def krun_arguments(case: dict) -> list[str]:
    """Build the KWasm program and stack configuration for the Java route."""

    return [f"-c{name}={value}" for name, value in native.configuration_variables(case).items()]


HOOKS = semantics.Hooks(
    description=__doc__,
    label="readable KWasm integer slice",
    java_help="also run the pinned K toolchain behavior comparison and proof",
    claim_count=1,
    krun_arguments=krun_arguments,
    observed=native.observed,
    checked=native.checked,
)


def main() -> int:
    return semantics.run_port(PORT, HOOKS)


if __name__ == "__main__":
    entry(HOOKS.label, main, errors=(OSError,))
