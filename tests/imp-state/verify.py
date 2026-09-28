#!/usr/bin/env python3
"""Strict production-independent oracle for the IMP calculation/state slice."""

from __future__ import annotations

from collections import Counter
import copy
import json
import os
from pathlib import Path
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import ROOT, entry  # noqa: E402
from support.hashing import canonical_json  # noqa: E402
from support.imp_oracle import KAST, DivisionCase, RejectionPin, Spec, main as run_oracle  # noqa: E402


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

METADATA_ATTRIBUTES = {
    "org.kframework.attributes.Source",
    "org.kframework.attributes.Location",
    "org.kframework.definition.Production",
    "contentStartLine",
    "contentStartColumn",
    "digest",
    "productionID",
    "UNIQUE_ID",
}


def envelope(output: str) -> dict[str, Any]:
    start = output.find("{")
    if start < 0:
        raise ValueError("KAST output has no JSON envelope")
    value = json.loads(output[start:])
    if set(value) != {"format", "version", "term"}:
        raise ValueError(f"unexpected KAST envelope keys {sorted(value)}")
    if value["format"] != "KAST" or value["version"] != 4:
        raise ValueError(f"expected KAST v4, got {value.get('format')} v{value.get('version')}")
    validate_term(value["term"])
    return value


def validate_sort(sort: Any) -> None:
    if not isinstance(sort, dict) or set(sort) != {"node", "name", "params"}:
        raise ValueError(f"unsupported sort shape {sort!r}")
    if sort["node"] != "KSort" or not isinstance(sort["name"], str) or sort["params"] != []:
        raise ValueError(f"unsupported sort {sort!r}")


def validate_label(label: Any) -> str:
    if not isinstance(label, dict) or set(label) != {"node", "name", "params"}:
        raise ValueError(f"unsupported label shape {label!r}")
    if label["node"] != "KLabel" or label["params"] != [] or not isinstance(label["name"], str):
        raise ValueError(f"unsupported label {label!r}")
    name = label["name"]
    fixed = {"<generatedTop>", "<generatedCounter>", "<k>", "<env>", ".Map", "_Map_", "_|->_"}
    if name not in fixed and "KRS-IMP-STATE-" not in name and not name.startswith("#freezer"):
        raise ValueError(f"unrecognized project KLabel {name!r}")
    return name


def validate_term(term: Any) -> None:
    if not isinstance(term, dict) or not isinstance(term.get("node"), str):
        raise ValueError(f"unsupported KAST term {term!r}")
    node = term["node"]
    if node == "KApply":
        if set(term) != {"node", "label", "arity", "args"}:
            raise ValueError(f"unexpected KApply keys {sorted(term)}")
        validate_label(term["label"])
        if term["arity"] != len(term["args"]):
            raise ValueError("KApply arity differs from args")
        for argument in term["args"]:
            validate_term(argument)
    elif node == "KToken":
        if set(term) != {"node", "sort", "token"} or not isinstance(term["token"], str):
            raise ValueError(f"unsupported KToken {term!r}")
        validate_sort(term["sort"])
    elif node == "KSequence":
        if set(term) != {"node", "arity", "items"} or term["arity"] != len(term["items"]):
            raise ValueError(f"unsupported KSequence {term!r}")
        for item in term["items"]:
            validate_term(item)
    else:
        raise ValueError(f"unsupported KAST node {node!r}")


def label(term: dict[str, Any]) -> str:
    if term.get("node") != "KApply":
        raise ValueError(f"expected application, got {term!r}")
    return term["label"]["name"]


def abstract_term(term: dict[str, Any]) -> Any:
    node = term.get("node")
    if node == "KToken":
        return [term["sort"]["name"], term["token"]]
    if node != "KApply":
        raise ValueError(f"unexpected authored-tree node {node!r}")
    name = label(term)
    names = {
        "___KRS-IMP-STATE-CALC-SYNTAX_Stmt_Stmt_Stmt": "seq",
        "_=_;_KRS-IMP-STATE-CALC-SYNTAX_Stmt_Id_Expr": "assign",
        "_+__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "+",
        "_*__KRS-IMP-STATE-EXPR-SYNTAX_Expr_Expr_Expr": "*",
    }
    if name not in names:
        raise ValueError(f"unknown authored-tree label {name!r}")
    return [names[name], *(abstract_term(argument) for argument in term["args"])]


def find_module(definition: dict[str, Any], name: str) -> dict[str, Any]:
    if definition.get("format") != "KAST" or definition.get("version") != 4:
        raise ValueError("definition JSON is not KAST v4")
    modules = definition.get("term", {}).get("modules", [])
    matches = [module for module in modules if module.get("name") == name]
    if len(matches) != 1:
        raise ValueError(f"expected one module {name!r}, found {len(matches)}")
    return matches[0]


def sentence_counts(definition: dict[str, Any], name: str) -> Counter[str]:
    return Counter(sentence.get("node", "<missing>") for sentence in find_module(definition, name)["localSentences"])


def normalized_definition(definition: dict[str, Any]) -> dict[str, Any]:
    value = copy.deepcopy(definition)

    def visit(node: Any) -> Any:
        if isinstance(node, dict):
            result: dict[str, Any] = {}
            for key, child in node.items():
                if node.get("node") == "KAtt" and key == "att":
                    child = {name: item for name, item in child.items() if name not in METADATA_ATTRIBUTES}
                result[key] = visit(child)
            if isinstance(result.get("imports"), list):
                result["imports"].sort(key=canonical_json)
            if isinstance(result.get("localSentences"), list):
                result["localSentences"].sort(key=canonical_json)
            if result.get("node") == "KSyntaxAssociativity":
                result["tags"].sort()
            if result.get("node") == "KSyntaxPriority":
                for group in result["priorities"]:
                    group.sort()
            return result
        if isinstance(node, list):
            return [visit(item) for item in node]
        return node

    value = visit(value)
    value["term"]["modules"].sort(key=lambda module: module["name"])
    return value


def verify_definition_structure(parsed: dict[str, Any], compiled: dict[str, Any]) -> None:
    expected = {
        SYNTAX_MODULE: {"KSyntaxAssociativity": 1, "KProduction": 3, "KSyntaxPriority": 1},
        EXPR_SYNTAX_MODULE: {"KProduction": 19, "KSyntaxAssociativity": 6, "KSyntaxPriority": 1},
        EXPR_RULES_MODULE: {"KRule": 18},
        MODULE: {"KProduction": 11, "KRule": 6},
    }
    for name, counts in expected.items():
        actual = dict(sentence_counts(parsed, name))
        if actual != counts:
            raise ValueError(f"parsed {name} counts differ: expected={counts}, actual={actual}")
    calc_syntax = find_module(compiled, SYNTAX_MODULE)
    contexts = [sentence for sentence in calc_syntax["localSentences"] if sentence.get("node") == "KContext"]
    if len(contexts) != 1 or "strict" not in contexts[0].get("att", {}).get("att", {}):
        raise ValueError("assignment strict(2) did not generate exactly one strict context")
    main_rules = [sentence for sentence in find_module(compiled, MODULE)["localSentences"] if sentence.get("node") == "KRule"]
    heat = sum("heat" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    cool = sum("cool" in sentence.get("att", {}).get("att", {}) for sentence in main_rules)
    if (heat, cool) != (25, 25):
        raise ValueError(f"expected 25 inherited+assignment heat/cool pairs, got {(heat, cool)}")


def parse_map(term: dict[str, Any]) -> dict[str, str]:
    name = label(term)
    if name == ".Map":
        return {}
    if name == "_Map_":
        merged: dict[str, str] = {}
        for child in term["args"]:
            for key, value in parse_map(child).items():
                if key in merged:
                    raise ValueError(f"duplicate concrete map key {key!r}")
                merged[key] = value
        return merged
    if name == "_|->_":
        key, value = term["args"]
        if key.get("node") != "KToken" or key["sort"]["name"] != "Id":
            raise ValueError(f"non-Id environment key {key!r}")
        if value.get("node") != "KToken" or value["sort"]["name"] not in {"Int", "Bool"}:
            raise ValueError(f"non-Value environment value {value!r}")
        return {key["token"]: value["token"]}
    raise ValueError(f"unsupported concrete Map label {name!r}")


def final_environment(term: dict[str, Any]) -> dict[str, str]:
    if label(term) != "<generatedTop>":
        raise ValueError("final configuration is not generatedTop")
    cells = {label(cell): cell["args"][0] for cell in term["args"]}
    k_cell = cells.get("<k>")
    if k_cell != {"node": "KSequence", "arity": 0, "items": []}:
        raise ValueError(f"final k cell is not empty: {k_cell!r}")
    env = cells.get("<env>")
    if not isinstance(env, dict):
        raise ValueError("final configuration lacks env cell")
    return parse_map(env)


def final_environment_if_complete(term: dict[str, Any]) -> dict[str, str] | None:
    try:
        return final_environment(term)
    except ValueError:
        return None


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

KAST_HOOKS = KAST(
    envelope=envelope, abstract_term=abstract_term,
    normalized_definition=normalized_definition,
    verify_definition_structure=verify_definition_structure,
    final_environment=final_environment,
    final_environment_if_complete=final_environment_if_complete,
)


def main() -> int:
    return run_oracle(SPEC, KAST_HOOKS)


if __name__ == "__main__":
    entry("IMP state strict oracle", main)
