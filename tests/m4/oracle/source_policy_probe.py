#!/usr/bin/env python3
"""Development helper: show the first fail-closed M4 source projection delta."""

from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from source_definition import (  # noqa: E402
    DEFAULT_METADATA_ATTRIBUTES, ProjectionPolicy, compare_definitions,
    load_definition, project_definition,
)
from support.hashing import json_sha256  # noqa: E402


REFERENCE_MODULES = {
    "EXPR-SYNTAX", "EXPR-RULES", "CALC-SYNTAX", "CALC", "IMP-SYNTAX", "IMP",
    "IMP-VERIFICATION-SYNTAX", "IMP-VERIFICATION", "KRS-M3D-STATIC-SYNTAX",
    "KRS-M3D-STATIC",
}
ACTUAL_MODULES = {"KRS-M4-COMPLETE-IMP"}
LABEL_MAP = {
    "-__EXPR-SYNTAX_Expr_Expr": "neg",
    "!__EXPR-SYNTAX_Expr_Expr": "not",
    "_*__EXPR-SYNTAX_Expr_Expr_Expr": "mul",
    "_/__EXPR-SYNTAX_Expr_Expr_Expr": "div",
    "_+__EXPR-SYNTAX_Expr_Expr_Expr": "add",
    "_-__EXPR-SYNTAX_Expr_Expr_Expr": "sub",
    "_>=__EXPR-SYNTAX_Expr_Expr_Expr": "ge",
    "_>__EXPR-SYNTAX_Expr_Expr_Expr": "gt",
    "_<=__EXPR-SYNTAX_Expr_Expr_Expr": "le",
    "_<__EXPR-SYNTAX_Expr_Expr_Expr": "lt",
    "_==__EXPR-SYNTAX_Expr_Expr_Expr": "eq",
    "_!=__EXPR-SYNTAX_Expr_Expr_Expr": "ne",
    "_&&__EXPR-SYNTAX_Expr_Expr_Expr": "and",
    "_||__EXPR-SYNTAX_Expr_Expr_Expr": "or",
    "_=_;_CALC-SYNTAX_Stmt_Id_Expr": "assign",
    "___CALC-SYNTAX_Stmt_Stmt_Stmt": "sequence",
    "if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt": "ifThenElse",
    "if(_)__IMP-SYNTAX_Stmt_Expr_Stmt": "ifThen",
    "while(_)__IMP-SYNTAX_Stmt_Expr_Stmt": "while",
    "{_}_IMP-SYNTAX_Stmt_Stmt": "block",
    "{}_IMP-SYNTAX_Stmt": "emptyBlock",
    "(_)_EXPR-SYNTAX_Expr_Expr": "krsGenerated_787219016217a304fd6123cf",
    "#SemanticCastToKItem": "#SemanticCastToK",
}
for _reference, _actual in tuple(LABEL_MAP.items()):
    if _reference.startswith("#") or _reference.startswith("("):
        continue
    for _index in range(2):
        LABEL_MAP[f"#freezer{_reference}{_index}_"] = f"#freezer{_actual}{_index}_"
LABEL_MAP["#freezerm3dTwice0_"] = "#freezer_"


def collect(path: Path, modules: set[str]):
    definition = json.loads(path.read_text())["term"]
    labels, sorts, attributes, names = {""}, set(), set(), {definition["mainModule"]}

    def visit(value):
        if isinstance(value, list):
            for child in value:
                visit(child)
        elif isinstance(value, dict):
            if value.get("node") == "KLabel":
                labels.add(value["name"])
            if value.get("node") == "KSort":
                sorts.add(value["name"])
            if value.get("node") == "KAtt":
                attributes.update(value["att"])
            if value.get("node") == "KImport":
                names.add(value["name"])
            for child in value.values():
                visit(child)

    visit(definition["att"])
    for module in definition["modules"]:
        if module["name"] in modules:
            visit(module)
    return labels, sorts, attributes, names


def main() -> None:
    reference, actual = map(Path, sys.argv[1:3])
    rl, rs, ra, rn = collect(reference, REFERENCE_MODULES)
    al, ass, aa, an = collect(actual, ACTUAL_MODULES)
    metadata = set(DEFAULT_METADATA_ATTRIBUTES) | {"label", "group", "result", "symbol"}
    known = ra | aa | metadata
    baseline = ProjectionPolicy(
        module_origins={name: "complete-imp" for name in REFERENCE_MODULES},
        label_map=LABEL_MAP,
        identity_labels=frozenset(rl - set(LABEL_MAP)),
        identity_sorts=frozenset(rs), identity_names=frozenset(rn),
        known_attributes=frozenset(known), metadata_attributes=frozenset(metadata),
        imports_by_origin={"complete-imp": ()},
        attribute_value_map={
            "format": {"%1 %2%3%4% %5 %6 %7": "%1 %2%3%4 %5 %6 %7"}
        },
    )
    observed = ProjectionPolicy(
        module_origins={name: "complete-imp" for name in ACTUAL_MODULES},
        identity_labels=frozenset(al), identity_sorts=frozenset(ass),
        identity_names=frozenset(an), known_attributes=frozenset(known),
        metadata_attributes=frozenset(metadata), imports_by_origin={"complete-imp": ()},
        redundant_sort_declarations=frozenset({"KItem", "Expr", "Value", "Stmt", "KResult"}),
        redundant_production_klabels=frozenset({"krsGenerated_787219016217a304fd6123cf"}),
        joined_terminal_productions=frozenset({"m3dPositive", "m3dPriority", "m3dTotal"}),
    )
    baseline_definition = load_definition(reference)
    projected = project_definition(baseline_definition, baseline)
    ignored = {
        json_sha256(sentence): 1
        for origin in projected["origins"]
        for sentence in origin["sentences"]
        if sentence.get("node") == "KContext"
    }
    if ignored:
        baseline = ProjectionPolicy(**{**baseline.__dict__, "ignored_sentence_sha256": ignored})
        print(json.dumps({"ignored_context_sha256": sorted(ignored)}, indent=2))
    print(compare_definitions(baseline_definition, load_definition(actual), baseline, observed))


if __name__ == "__main__":
    main()
