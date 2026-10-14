#!/usr/bin/env python3
"""Strict production-independent oracle for the IMP control-flow slice."""

from __future__ import annotations

import os
from pathlib import Path
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import INSPIRATIONS, entry  # noqa: E402
from support.imp_oracle import (  # noqa: E402
    KAST,
    BoundedSearch,
    InheritedLayer,
    RejectionPin,
    Spec,
    main as run_oracle,
)


HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
IMP = FIXTURES / "imp.k"
INDUCED = FIXTURES / "induced-definition-error.k"
ACCEPTED = HERE / "corpus" / "accepted"
NONTERMINATING = HERE / "corpus" / "nonterminating"
SYNTAX_REJECTED = HERE / "corpus" / "rejected" / "syntax"
SEMANTIC_REJECTED = HERE / "corpus" / "rejected" / "semantic"
PINS = HERE / "pins.json"
IMP_STATE = HERE.parent / "imp-state" / "fixtures"
UPSTREAM = INSPIRATIONS / "runtimeverification" / "imp-semantics"

MODULE = "KRS-IMP-CONTROL-FLOW-IMP"
SYNTAX_MODULE = "KRS-IMP-CONTROL-FLOW-IMP-SYNTAX"
CALC_MODULE = "KRS-IMP-STATE-CALC"
CALC_SYNTAX_MODULE = "KRS-IMP-STATE-CALC-SYNTAX"
EXPR_SYNTAX_MODULE = "KRS-IMP-STATE-EXPR-SYNTAX"
EXPR_RULES_MODULE = "KRS-IMP-STATE-EXPR-RULES"
INDUCED_MODULE = "KRS-IMP-CONTROL-FLOW-INDUCED-DEFINITION-ERROR"


def ident(name: str) -> list[str]:
    return ["Id", name]


def integer(value: int) -> list[str]:
    return ["Int", str(value)]


def boolean(value: bool) -> list[str]:
    return ["Bool", str(value).lower()]


def assign(name: str, value: Any) -> list[Any]:
    return ["assign", ident(name), value]


def seq(first: Any, second: Any) -> list[Any]:
    return ["seq", first, second]


EXPECTED_TREES: dict[str, Any] = {
    "empty-block.imp": ["empty-block"],
    "if-true.imp": ["if", boolean(True), assign("x", integer(1))],
    "if-false.imp": ["if", boolean(False), assign("x", integer(1))],
    "explicit-else.imp": [
        "if-else",
        boolean(False),
        assign("x", integer(1)),
        assign("x", integer(2)),
    ],
    "dangling-else.imp": seq(
        assign("x", integer(0)),
        seq(
            assign("y", integer(0)),
            seq(
                [
                    "if",
                    boolean(False),
                    [
                        "if-else",
                        boolean(True),
                        assign("y", integer(1)),
                        assign("y", integer(2)),
                    ],
                ],
                assign("x", integer(1)),
            ),
        ),
    ),
    "block-sequence.imp": seq(
        [
            "block",
            seq(assign("x", integer(1)), assign("y", ["+", ident("x"), integer(1)])),
        ],
        assign("z", ["+", ident("y"), integer(1)]),
    ),
    "while-followed.imp": seq(
        assign("x", integer(3)),
        seq(
            [
                "while",
                [">", ident("x"), integer(0)],
                ["block", assign("x", ["-", ident("x"), integer(1)])],
            ],
            assign("y", ["+", ident("x"), integer(1)]),
        ),
    ),
    "nested-control.imp": seq(
        assign("x", integer(2)),
        [
            "if-else",
            [">", ident("x"), integer(0)],
            [
                "block",
                [
                    "while",
                    [">", ident("x"), integer(0)],
                    assign("x", ["-", ident("x"), integer(1)]),
                ],
            ],
            ["block", assign("x", integer(99))],
        ],
    ),
}

EXPECTED_EXECUTIONS: dict[str, dict[str, Any]] = {
    "empty-block.imp": {"steps": 1, "env": {}},
    "if-true.imp": {"steps": 3, "env": {"x": "1"}},
    "if-false.imp": {"steps": 3, "env": {}},
    "explicit-else.imp": {"steps": 2, "env": {"x": "2"}},
    "dangling-else.imp": {"steps": 9, "env": {"x": "1", "y": "0"}},
    "block-sequence.imp": {"steps": 19, "env": {"x": "1", "y": "2", "z": "3"}},
    "while-followed.imp": {"steps": 83, "env": {"x": "0", "y": "1"}},
    "nested-control.imp": {"steps": 59, "env": {"x": "0"}},
}

SEARCH_DEPTHS = {
    "explicit-else.imp": (0, 1, 2),
    "dangling-else.imp": (0, 1, 2, 4, 9),
}
NONTERMINATING_DEPTHS = (0, 1, 2, 3, 4, 8, 16, 32)
ORACLE_WORKERS = max(
    1,
    int(os.environ.get("KRS_IMP_CONTROL_FLOW_ORACLE_WORKERS", min(8, os.cpu_count() or 1))),
)

VALIDATION_POLICY = {
    "labels": ["<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"],
    "label_prefixes": ["#freezer"],
    "label_contains": ["KRS-IMP-STATE-", "KRS-IMP-CONTROL-FLOW-"],
    "parameterized_sorts": True,
    "variables": False,
}


LABEL_MAP = {
    "___KRS-IMP-STATE-CALC-SYNTAX_Stmt_Stmt_Stmt": "seq",
    "_=_;_KRS-IMP-STATE-CALC-SYNTAX_Stmt_Id_Expr": "assign",
    "_+__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "+",
    "_-__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "-",
    "_>__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": ">",
    "if(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt": "if",
    "if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt": "if-else",
    "while(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt": "while",
    "{_}_KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Stmt": "block",
    "{}_KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt": "empty-block",
}


PARSED_COUNTS = {
    SYNTAX_MODULE: {"production": 5},
    MODULE: {"rule": 6},
    CALC_SYNTAX_MODULE: {"syntax_associativity": 1, "production": 3, "syntax_priority": 1},
    EXPR_SYNTAX_MODULE: {"production": 19, "syntax_associativity": 6, "syntax_priority": 1},
    EXPR_RULES_MODULE: {"rule": 18},
    CALC_MODULE: {"production": 11, "rule": 6},
}


SEARCH_VALIDATION_POLICY = {
    **VALIDATION_POLICY,
    "labels": [*VALIDATION_POLICY["labels"], "#Equals"],
    "variables": True,
}


SPEC = Spec(
    label="IMP control flow strict oracle", here=HERE, source=IMP,
    fixture_sources=(IMP,), induced=INDUCED, accepted=ACCEPTED,
    syntax_rejected=SYNTAX_REJECTED, semantic_rejected=SEMANTIC_REJECTED,
    pins_path=PINS, upstream=UPSTREAM, module=MODULE, syntax_module=SYNTAX_MODULE,
    induced_module=INDUCED_MODULE, extension=".imp",
    surface_fragments=(
        'requires "../../imp-state/fixtures/calc.k"',
        '"if" "(" Expr ")" Stmt "else" Stmt', "strict(1)", "avoid",
        '"while" "(" Expr ")" Stmt', '"{" Stmt "}"', '"{" "}"',
        "if ( C ) S => if ( C ) S else {}", "while ( C ) S", "S ~> { }", "{ } => .K",
    ),
    surface_detail="if/else, dangling-else control, while, blocks and all six rules occur literally",
    expected_trees=EXPECTED_TREES, expected_executions=EXPECTED_EXECUTIONS,
    syntax_locations={
        "missing-condition.imp": (1, 5, 1, 6),
        "missing-else-body.imp": (2, 1, 2, 1),
        "stray-else.imp": (1, 1, 1, 5),
        "unclosed-block.imp": (2, 1, 2, 1),
    },
    syntax_fragments={
        "missing-condition.imp": "unexpected token ')' following token '('",
        "missing-else-body.imp": "unexpected end of file following token",
        "stray-else.imp": "unexpected token 'else'",
        "unclosed-block.imp": "unexpected end of file following token ';'",
    },
    stuck_steps={"non-bool-if.imp": 1, "undefined-condition.imp": 2, "non-bool-while.imp": 2},
    definition_detail="5 control productions, 6 labeled rules, avoid/strict distinction, one context and 26 heat/cool pairs",
    trees_detail="8 full KAST v4 trees freeze right association and dangling else",
    final_detail="both branches, blocks, loops and following statements match",
    trace_detail="exact depth-indexed states retain control and generated strictness frames",
    rejection_detail="four exact syntax diagnostics and three exact stuck states",
    induced_detail="authored @ selected exactly at induced-definition-error.k:2:27-2:28",
    induced_location=(2, 27, 2, 28), compiled_dir="imp-kompiled",
    rejection_pin=RejectionPin(
        stuck_key="stuck_states", stuck_label="stuck", diagnostics_key="syntax_diagnostics",
    ),
    workers=ORACLE_WORKERS,
    inherited_layer=InheritedLayer(
        directory=IMP_STATE, files=("expr.k", "calc.k"), pin_key="imp_state_sha256",
        check="imp_state_layer", detail="the inherited expression/state oracle is exact",
    ),
    search=BoundedSearch(
        depths=SEARCH_DEPTHS, nonterminating=NONTERMINATING,
        nonterminating_program="infinite-loop.imp", nonterminating_depths=NONTERMINATING_DEPTHS,
    ),
    pin_induced_diagnostic=True,
)

KAST_SPEC = KAST(
    validation_policy=VALIDATION_POLICY,
    label_map=LABEL_MAP,
    parsed_counts=PARSED_COUNTS,
    heat_cool=(26, 26),
    context_attributes=("strict",),
    context_count=1,
    search_validation_policy=SEARCH_VALIDATION_POLICY,
    production_attributes={
        "if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt": (("avoid", "strict"), ()),
        "while(_)__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt": ((), ("strict",)),
    },
    rule_labels=tuple(f"{MODULE}.{name}" for name in ("if-true", "if-false", "if-else", "while", "block", "done")),
    compiled_rule_count=58,
    k_heads={
        f"{name}@001": "if(_)_else__KRS-IMP-CONTROL-FLOW-IMP-SYNTAX_Stmt_Expr_Stmt_Stmt"
        for name in ("if-true.imp", "if-false.imp")
    },
)


def main() -> int:
    return run_oracle(SPEC, KAST_SPEC)


if __name__ == "__main__":
    entry("IMP control flow strict oracle", main)
