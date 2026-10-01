#!/usr/bin/env python3
"""Strict production-independent oracle for the IMP calculation/state slice."""

from __future__ import annotations

import os
from pathlib import Path
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, entry  # noqa: E402
from support.imp_oracle import KAST, DivisionCase, RejectionPin, Spec, main as run_oracle  # noqa: E402
from support.packages import check_packages  # noqa: E402
from support.tools import checkout_scratch, z3_environment  # noqa: E402


HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
EXPR = FIXTURES / "expr.k"
CALC = FIXTURES / "calc.k"
INDUCED = FIXTURES / "induced-definition-error.k"
ACCEPTED = HERE / "corpus" / "accepted"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
SEMANTIC_REJECTED = HERE / "corpus" / "rejected" / "semantic"
PINS = HERE / "pins.json"
UPSTREAM = (
    ROOT.parent
    / "inspirations"
    / "runtimeverification"
    / "imp-semantics"
)

MODULE = "KRS-IMP-STATE-CALC"
SYNTAX_MODULE = "KRS-IMP-STATE-CALC-SYNTAX"
EXPR_SYNTAX_MODULE = "KRS-IMP-STATE-EXPR-SYNTAX"
EXPR_RULES_MODULE = "KRS-IMP-STATE-EXPR-RULES"
INDUCED_MODULE = "KRS-IMP-STATE-INDUCED-DEFINITION-ERROR"

EXPECTED_TREES: dict[str, Any] = {
    "single-assignment.calc": ["assign", ["Id", "x"], ["Int", "1"]],
    "initial-environment.calc": [
        "assign",
        ["Id", "y"],
        ["+", ["Id", "x"], ["Int", "1"]],
    ],
    "lookup-evaluation-order.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "2"]],
        [
            "assign",
            ["Id", "y"],
            ["+", ["Id", "x"], ["*", ["Id", "x"], ["Int", "3"]]],
        ],
    ],
    "update-existing.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "1"]],
        ["assign", ["Id", "x"], ["+", ["Id", "x"], ["Int", "4"]]],
    ],
    "right-associated-sequence.calc": [
        "seq",
        ["assign", ["Id", "x"], ["Int", "1"]],
        [
            "seq",
            ["assign", ["Id", "y"], ["Int", "2"]],
            ["assign", ["Id", "z"], ["+", ["Id", "x"], ["Id", "y"]]],
        ],
    ],
}

EXPECTED_EXECUTIONS = {
    "single-assignment.calc": {"initial_env": ".Map", "steps": 1, "env": {"x": "1"}},
    "initial-environment.calc": {
        "initial_env": "x |-> 41",
        "steps": 7,
        "env": {"x": "41", "y": "42"},
    },
    "lookup-evaluation-order.calc": {
        "initial_env": ".Map",
        "steps": 15,
        "env": {"x": "2", "y": "8"},
    },
    "update-existing.calc": {"initial_env": ".Map", "steps": 9, "env": {"x": "5"}},
    "right-associated-sequence.calc": {
        "initial_env": ".Map",
        "steps": 14,
        "env": {"x": "1", "y": "2", "z": "3"},
    },
}

VALIDATION_POLICY = {
    "labels": ["<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"],
    "label_prefixes": ["#freezer"],
    "label_contains": ["KRS-IMP-STATE-"],
    "parameterized_sorts": False,
    "variables": False,
}


LABEL_MAP = {
    "___KRS-IMP-STATE-CALC-SYNTAX_Stmt_Stmt_Stmt": "seq",
    "_=_;_KRS-IMP-STATE-CALC-SYNTAX_Stmt_Id_Expr": "assign",
    "_+__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "+",
    "_*__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "*",
}


PARSED_COUNTS = {
    SYNTAX_MODULE: {"syntax_associativity": 1, "production": 3, "syntax_priority": 1},
    EXPR_SYNTAX_MODULE: {"production": 19, "syntax_associativity": 6, "syntax_priority": 1},
    EXPR_RULES_MODULE: {"rule": 18},
    MODULE: {"production": 11, "rule": 6},
}


SPEC = Spec(
    label="IMP state strict oracle", here=HERE, source=CALC,
    fixture_sources=(EXPR, CALC), induced=INDUCED, accepted=ACCEPTED,
    syntax_rejected=SYNTAX_REJECTED, semantic_rejected=SEMANTIC_REJECTED,
    pins_path=PINS, upstream=UPSTREAM, module=MODULE, syntax_module=SYNTAX_MODULE,
    induced_module=INDUCED_MODULE, extension=".calc",
    surface_fragments=(
        "imports ID-SYNTAX", "syntax Expr ::= Id", 'Id "=" Expr ";"',
        "strict(2)", "right:", "syntax priority stmt > seq-stmt", "$PGM:Stmt",
        "$ENV:Map", "S1 ~> S2", "X |-> V", "E [ X <- V ]",
    ),
    surface_detail="Id injection, grammar, strictness, priority, cells and three state rules occur literally",
    expected_trees=EXPECTED_TREES, expected_executions=EXPECTED_EXECUTIONS,
    syntax_locations={
        "missing-semicolon.calc": (2, 1, 2, 1),
        "missing-identifier.calc": (1, 1, 1, 2),
    },
    stuck_steps={"undefined-variable.calc": 2, "type-error.calc": 1},
    definition_detail="3 calc productions, priority/right-assoc, 3 rules, 1 strict context and 25 heat/cool pairs",
    trees_detail="5 full KAST v4 trees and exact right association",
    final_detail="initialization, lookup, assignment, update and sequencing match",
    trace_detail="exact depth-indexed LLVM states retain generated heat/cool frames",
    rejection_detail="syntax locations, two stuck states and LLVM division error are exact",
    induced_detail="authored @ selected exactly at induced-definition-error.k:2:19-2:20",
    induced_location=(2, 19, 2, 20), compiled_dir="calc-kompiled",
    rejection_pin=RejectionPin(stuck_key="stuck_state_aggregate", stuck_label="stuck aggregate"),
    workers=min(8, os.cpu_count() or 1),
    division=DivisionCase(
        program="division-by-zero.calc",
        stderr="[hook_INT_tdiv]: Division by zero: 1 / 0",
        pin_key="division_error",
    ),
)

KAST_SPEC = KAST(
    validation_policy=VALIDATION_POLICY,
    label_map=LABEL_MAP,
    parsed_counts=PARSED_COUNTS,
    heat_cool=(25, 25),
    context_attributes=("strict",),
    context_count=1,
)


def main() -> int:
    check_packages(
        "imp-state",
        env=z3_environment(),
        target_dir=checkout_scratch() / "imp-state-root-target",
    )
    return run_oracle(SPEC, KAST_SPEC)


if __name__ == "__main__":
    entry("IMP state strict oracle", main)
