#!/usr/bin/env python3
"""Persistent K-Rust execution support for the KMIR qualification corpus."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from support import krs_gate  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def configuration_variables(case: Mapping[str, Any]) -> dict[str, str]:
    """Return surface configuration text for both native and Java execution."""

    return {
        "PGM": "run",
        "PROGRAM": str(case["program"]),
        "LOCALS": str(case["locals"]),
        "RETVAL": "noReturn",
        "CURRENTFUNC": str(case.get("current_func", "ty(-1)")),
        "CALLER": str(case.get("caller", "ty(-1)")),
        "DEST": str(case.get("destination", "place(local(-1), .ProjectionElems)")),
        "TARGET": str(case.get("target", "noBasicBlockIdx")),
        "UNWIND": str(case.get("unwind", "unwindActionContinue")),
        "STACK": str(case.get("stack", ".List")),
        "FUNCTIONS": str(case.get("functions", ".Map")),
        "TYPES": str(case.get("types", ".Map")),
        "MEMORY": str(case.get("memory", ".Map")),
    }


def applications(value: Any, name: str) -> list[Mapping[str, Any]]:
    found = []
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if current.get("tag") == "App" and current.get("name") == name:
                found.append(current)
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    return found


def cell(state: Mapping[str, Any], name: str) -> Mapping[str, Any]:
    matches = applications(state, f"Lbl'-LT-'{name}'-GT-'")
    if len(matches) != 1:
        raise GateError(f"result contains {len(matches)} <{name}> cells")
    arguments = matches[0].get("args")
    if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
        raise GateError(f"<{name}> cell is malformed")
    return arguments[0]


def unwrap_injection(term: Mapping[str, Any]) -> Mapping[str, Any]:
    while term.get("tag") == "App" and term.get("name") == "inj":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
            raise GateError(f"malformed sort injection: {term}")
        term = arguments[0]
    return term


def app_arguments(term: Mapping[str, Any], name: str, arity: int) -> list[Mapping[str, Any]]:
    arguments = term.get("args")
    if term.get("tag") != "App" or term.get("name") != f"Lbl{name}" or not isinstance(arguments, list) or len(arguments) != arity or not all(isinstance(item, dict) for item in arguments):
        raise GateError(f"expected {name}/{arity}: {term}")
    return arguments


def domain_value(term: Mapping[str, Any], sort_name: str) -> str:
    sort = term.get("sort")
    if term.get("tag") != "DV" or not isinstance(sort, dict) or sort.get("name") != f"Sort{sort_name}" or not isinstance(term.get("value"), str):
        raise GateError(f"expected concrete {sort_name}: {term}")
    return str(term["value"])


def rendered_mir_value(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblmoved":
        app_arguments(term, "moved", 0)
        return "Moved"
    if term.get("name") == "Lblinteger":
        value = app_arguments(term, "integer", 3)
        return (
            f"Integer({domain_value(value[0], 'Int')},"
            f"{domain_value(value[1], 'Int')},"
            f"{domain_value(value[2], 'Bool')})"
        )
    if term.get("name") == "Lblboolean":
        return f"BoolVal({domain_value(app_arguments(term, 'boolean', 1)[0], 'Bool')})"
    if term.get("name") == "Lblaggregate":
        value = app_arguments(term, "aggregate", 2)
        variant = domain_value(unwrap_injection(value[0]), "Int")
        fields = " ".join(
            f"ListItem({rendered_mir_value(field)})" for field in list_items(value[1])
        )
        prefix = f"{fields} " if fields else ""
        return f"Aggregate(variantIdx({variant}),{prefix}.List)"
    if term.get("name") == "Lblunion":
        value = app_arguments(term, "union", 2)
        field = domain_value(unwrap_injection(value[0]), "Int")
        return f"Union(fieldIdx({field}),{rendered_mir_value(value[1])})"
    if term.get("name") == "Lblrange":
        elements = " ".join(
            f"ListItem({rendered_mir_value(element)})"
            for element in list_items(app_arguments(term, "range", 1)[0])
        )
        suffix = f"{elements} " if elements else ""
        return f"Range({suffix}.List)"
    if term.get("name") == "Lblreference":
        value = app_arguments(term, "reference", 4)
        return (
            f"Reference({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{rendered_place(value[1])},{rendered_mutability(value[2])},"
            f"{rendered_metadata(value[3])})"
        )
    if term.get("name") == "Lblpointer":
        value = app_arguments(term, "pointer", 4)
        return (
            f"PtrLocal({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{rendered_place(value[1])},{rendered_mutability(value[2])},"
            f"{rendered_metadata(value[3])})"
        )
    if term.get("name") == "LblallocationReference":
        value = app_arguments(term, "allocationReference", 3)
        return (
            f"AllocRef({rendered_alloc_id(value[0])},"
            f"{rendered_projections(value[1])},{rendered_metadata(value[2])})"
        )
    raise GateError(f"unsupported concrete MirValue result: {term}")


def rendered_alloc_id(term: Mapping[str, Any]) -> str:
    value = app_arguments(unwrap_injection(term), "allocId", 1)
    return f"allocId({domain_value(unwrap_injection(value[0]), 'Int')})"


def rendered_binary_op(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    names = {
        "binOpAdd",
        "binOpAddUnchecked",
        "binOpSub",
        "binOpSubUnchecked",
        "binOpMul",
        "binOpMulUnchecked",
        "binOpDiv",
        "binOpRem",
        "binOpBitXor",
        "binOpBitAnd",
        "binOpBitOr",
        "binOpShl",
        "binOpShlUnchecked",
        "binOpShr",
        "binOpShrUnchecked",
        "binOpEq",
        "binOpLt",
        "binOpLe",
        "binOpNe",
        "binOpGe",
        "binOpGt",
    }
    name = str(term.get("name", ""))
    if name.startswith("Lbl") and name[3:] in names:
        rendered = name[3:]
        app_arguments(term, rendered, 0)
        return rendered
    raise GateError(f"unsupported concrete BinaryOp result: {term}")


def rendered_operand(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblconstant":
        value = app_arguments(term, "constant", 1)
        return f"const({rendered_mir_value(value[0])})"
    if term.get("name") in {"Lblcopy", "Lblmove"}:
        name = "copy" if term.get("name") == "Lblcopy" else "move"
        value = app_arguments(term, name, 1)
        return f"{name}({rendered_place(value[0])})"
    raise GateError(f"unsupported concrete Operand result: {term}")


def rendered_assert_message(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "overflow", 3)
    return (
        f"assertMessageOverflow({rendered_binary_op(value[0])},"
        f"{rendered_operand(value[1])},{rendered_operand(value[2])})"
    )


def rendered_mir_error(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblreachedUnreachable":
        app_arguments(term, "reachedUnreachable", 0)
        return "ReachedUnreachable"
    value = app_arguments(term, "assertError", 1)
    return f"AssertError({rendered_assert_message(value[0])})"


def list_items(term: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    name = term.get("name")
    arguments = term.get("args")
    if term.get("tag") == "App" and name == "Lbl'Stop'List" and arguments == []:
        return []
    if term.get("tag") == "App" and name == "Lbl'Unds'List'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return list_items(arguments[0]) + list_items(arguments[1])
    if term.get("tag") == "App" and name == "LblListItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
        return [arguments[0]]
    raise GateError(f"unsupported concrete List result: {term}")


def rendered_ty(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    return f"ty({domain_value(app_arguments(term, 'tyId', 1)[0], 'Int')})"


def rendered_mutability(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnotMutable":
        app_arguments(term, "notMutable", 0)
        return "mutabilityNot"
    if term.get("name") == "Lblmutable":
        app_arguments(term, "mutable", 0)
        return "mutabilityMut"
    raise GateError(f"unsupported concrete Mutability result: {term}")


def rendered_metadata_size(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnoMetadataSize":
        app_arguments(term, "noMetadataSize", 0)
        return "noMetadataSize"
    if term.get("name") in {"LblstaticSize", "LbldynamicSize"}:
        name = "staticSize" if term.get("name") == "LblstaticSize" else "dynamicSize"
        return f"{name}({domain_value(app_arguments(term, name, 1)[0], 'Int')})"
    raise GateError(f"unsupported concrete MetadataSize result: {term}")


def rendered_metadata(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "metadata", 3)
    return (
        f"metadata({rendered_metadata_size(value[0])},"
        f"{domain_value(unwrap_injection(value[1]), 'Int')},"
        f"{rendered_metadata_size(value[2])})"
    )


def rendered_projection(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblderef":
        app_arguments(term, "deref", 0)
        return "projectionElemDeref"
    if term.get("name") == "Lblfield":
        value = app_arguments(term, "field", 2)
        return (
            f"projectionElemField(fieldIdx({domain_value(unwrap_injection(value[0]), 'Int')}),"
            f"{rendered_ty(value[1])})"
        )
    if term.get("name") == "Lblindex":
        value = app_arguments(term, "index", 1)
        return f"projectionElemIndex(local({domain_value(unwrap_injection(value[0]), 'Int')}))"
    if term.get("name") == "LblconstantIndex":
        value = app_arguments(term, "constantIndex", 3)
        return (
            f"projectionElemConstantIndex({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')},"
            f"{domain_value(unwrap_injection(value[2]), 'Bool')})"
        )
    if term.get("name") == "Lblsubslice":
        value = app_arguments(term, "subslice", 3)
        return (
            f"projectionElemSubslice({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')},"
            f"{domain_value(unwrap_injection(value[2]), 'Bool')})"
        )
    if term.get("name") == "Lbldowncast":
        value = app_arguments(term, "downcast", 1)
        return (
            "projectionElemDowncast(variantIdx("
            f"{domain_value(unwrap_injection(value[0]), 'Int')}))"
        )
    if term.get("name") == "LblpointerOffset":
        value = app_arguments(term, "pointerOffset", 2)
        return (
            f"PointerOffset({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')})"
        )
    if term.get("name") == "LblsingletonArray":
        app_arguments(term, "singletonArray", 0)
        return "projectionElemSingletonArray"
    if term.get("name") == "LblwrapStruct":
        app_arguments(term, "wrapStruct", 0)
        return "projectionElemWrapStruct"
    if term.get("name") == "LbltoZst":
        app_arguments(term, "toZst", 0)
        return "projectionElemToZST"
    if term.get("name") == "LblfromZst":
        app_arguments(term, "fromZst", 0)
        return "projectionElemFromZST"
    raise GateError(f"unsupported concrete ProjectionElem result: {term}")


def rendered_projections(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblprojectionsEmpty":
        app_arguments(term, "projectionsEmpty", 0)
        return ".ProjectionElems"
    value = app_arguments(term, "projectionsCons", 2)
    return f"{rendered_projection(value[0])} {rendered_projections(value[1])}"


def rendered_place(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "place", 2)
    return (
        f"place(local({domain_value(unwrap_injection(value[0]), 'Int')}),"
        f"{rendered_projections(value[1])})"
    )


def rendered_typed_local(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnewLocal":
        value = app_arguments(term, "newLocal", 2)
        return f"newLocal({rendered_ty(value[0])},{rendered_mutability(value[1])})"
    if term.get("name") == "LbltypedValue":
        value = app_arguments(term, "typedValue", 3)
        return f"typedValue({rendered_mir_value(value[0])},{rendered_ty(value[1])},{rendered_mutability(value[2])})"
    if term.get("name") == "LblmovedLocal":
        value = app_arguments(term, "movedLocal", 2)
        return f"typedValue(Moved,{rendered_ty(value[0])},{rendered_mutability(value[1])})"
    raise GateError(f"unsupported concrete TypedLocal result: {term}")


def rendered_locals(term: Mapping[str, Any]) -> str:
    items = [rendered_typed_local(value) for value in list_items(term)]
    return " ".join(f"ListItem({value})" for value in items) + " .List"


def normalize_term(value: str) -> str:
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    return re.sub(r"\.\s+", ".", value)


def sole_state(result: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = result.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 1 or not isinstance(leaves[0], dict):
        raise GateError(f"native execution did not produce one leaf: {result}")
    state = leaves[0].get("state")
    if not isinstance(state, dict) or not isinstance(state.get("term"), dict):
        raise GateError(f"native execution leaf has no KORE state: {leaves[0]}")
    return state["term"]


def observed(case: Mapping[str, Any], state: Mapping[str, Any]) -> dict[str, Any]:
    """Render one final KORE JSON configuration into the comparable behavior outcome.

    The K-Rust runner returns KORE JSON and the reference route parses
    `krun --output kore` into the same shape, so both routes share this
    rendering and hash to one behavior digest.
    """

    computation = cell(state, "k")
    blocks = applications(cell(state, "currentBody"), "LblListItem")
    outcome = {
        "id": str(case["id"]),
        "program": normalize_term(str(case["program"])),
        "block_count": len(blocks),
        "locals": normalize_term(rendered_locals(cell(state, "locals"))),
        "stack_depth": len(list_items(cell(state, "stack"))),
    }
    if "expected_error" in case:
        errors = applications(computation, "LblprogramError")
        if len(errors) != 1:
            raise GateError(f"{case['id']} contains {len(errors)} program errors")
        error = app_arguments(errors[0], "programError", 1)[0]
        if unwrap_injection(cell(state, "retVal")).get("name") != "LblnoReturn":
            raise GateError(f"{case['id']} unexpectedly returned after a program error")
        outcome["error"] = normalize_term(rendered_mir_error(error))
        outcome["return"] = "noReturn"
        return outcome
    if computation.get("name") != "dotk":
        raise GateError(f"{case['id']} did not halt")
    returned = app_arguments(cell(state, "retVal"), "returned", 1)[0]
    outcome["return"] = normalize_term(f"return({rendered_mir_value(returned)})")
    return outcome


def checked(case: Mapping[str, Any], outcome: dict[str, Any]) -> dict[str, Any]:
    """Return `outcome` after requiring it to match the case's expected fields."""

    expected: dict[str, Any] = {
        "block_count": int(case["expected_block_count"]),
        "locals": normalize_term(str(case["expected_locals"])),
        "return": normalize_term(str(case["expected_return"])),
        "stack_depth": int(case.get("expected_stack_depth", 0)),
    }
    if "expected_error" in case:
        expected["error"] = normalize_term(str(case["expected_error"]))
    if {key: outcome[key] for key in expected} != expected:
        raise GateError(f"{case['id']} differs: expected={expected}, actual={outcome}")
    return outcome


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path, help="write ordered behavior outcomes as JSON")
    parser.add_argument(
        "--id",
        action="append",
        dest="case_ids",
        help="execute only the named behavior case; repeat to select several cases",
    )
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        cases = [case for case in cases if str(case.get("id")) in requested]
        found = {str(case["id"]) for case in cases}
        missing = requested - found
        if missing:
            raise GateError(f"unknown behavior case ids: {sorted(missing)}")
    outcomes = []
    with krs_gate.Session(arguments.krs_gate) as session:
        session.load(arguments.definition, arguments.module)
        for case in cases:
            pattern = session.configure(configuration_variables(case))["pattern"]
            result = session.execute(pattern)
            if not isinstance(result, dict):
                raise GateError(f"native result shape differs: {result}")
            outcomes.append(checked(case, observed(case, sole_state(result))))
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KMIR behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
