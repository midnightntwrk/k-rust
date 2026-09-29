#!/usr/bin/env python3
"""Persistent K-Rust execution support for the KWasm qualification corpus."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from support import krs_gate  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402


def application(name: str, *arguments: str) -> str:
    return f"Lbl{name}{{}}({','.join(arguments)})"


def integer(value: str | int) -> str:
    return f'\\dv{{SortInt{{}}}}("{int(value)}")'


def map_entry(name: str, sort: str, value: str) -> str:
    key = f'\\dv{{SortKConfigVar{{}}}}("${name}")'
    return application(
        "'UndsPipe'-'-GT-Unds'",
        f"inj{{SortKConfigVar{{}},SortKItem{{}}}}({key})",
        f"inj{{Sort{sort}{{}},SortKItem{{}}}}({value})",
    )


def instruction(source: str) -> str:
    parts = source.split()
    if len(parts) == 2 and parts[0] in {"i32.const", "i64.const"}:
        return application("const", application(parts[0][:3]), integer(parts[1]))
    if len(parts) == 1 and "." in parts[0]:
        ty, operation = parts[0].split(".", 1)
        operations = {"add": "add", "sub": "sub", "mul": "mul", "div_u": "divU"}
        if ty in {"i32", "i64"} and operation in operations:
            return application("binary", application(ty), application(operations[operation]))
    raise GateError(f"unsupported concrete KWasm instruction: {source}")


def instruction_list(source: str) -> str:
    items = [item.strip() for item in source.split(";")]
    if not items or items.pop() != ".Instrs":
        raise GateError(f"unsupported concrete Instrs: {source}")
    result = application("instrEmpty")
    for item in reversed(items):
        result = application("instrCons", instruction(item), result)
    return result


def initial_pattern(case: Mapping[str, Any]) -> str:
    entries = (
        map_entry("PGM", "Instrs", instruction_list(str(case["program"]))),
        map_entry("STACK", "ValStack", application("empty")),
    )
    configuration = application("'Stop'Map")
    for entry in entries:
        configuration = application("'Unds'Map'Unds'", configuration, entry)
    return application("initGeneratedTopCell", configuration)


def applications(value: Any, name: str) -> list[Mapping[str, Any]]:
    found: list[Mapping[str, Any]] = []
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
        raise GateError(f"native result contains {len(matches)} <{name}> cells")
    arguments = matches[0].get("args")
    if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
        raise GateError(f"native <{name}> cell is malformed")
    return arguments[0]


def app_arguments(term: Mapping[str, Any], name: str, arity: int) -> list[Mapping[str, Any]]:
    arguments = term.get("args")
    expected_name = name if name == "kseq" else f"Lbl{name}"
    if term.get("tag") != "App" or term.get("name") != expected_name or not isinstance(arguments, list) or len(arguments) != arity or not all(isinstance(item, dict) for item in arguments):
        raise GateError(f"expected {name}/{arity}: {term}")
    return arguments


def unwrap_injection(term: Mapping[str, Any]) -> Mapping[str, Any]:
    while term.get("tag") == "App" and term.get("name") == "inj":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
            raise GateError(f"malformed sort injection: {term}")
        term = arguments[0]
    return term


def domain_integer(term: Mapping[str, Any]) -> str:
    sort = term.get("sort")
    if term.get("tag") != "DV" or not isinstance(sort, dict) or sort.get("name") != "SortInt" or not isinstance(term.get("value"), str):
        raise GateError(f"expected concrete Int: {term}")
    return str(term["value"])


def sole_state(result: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = result.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 1 or not isinstance(leaves[0], dict):
        raise GateError(f"native execution did not produce one leaf: {result}")
    state = leaves[0].get("state")
    if not isinstance(state, dict) or not isinstance(state.get("term"), dict):
        raise GateError(f"native execution leaf has no KORE state: {leaves[0]}")
    return state["term"]


def observed(case: Mapping[str, Any], state: Mapping[str, Any]) -> dict[str, str]:
    instructions = cell(state, "instrs")
    expected_outcome = str(case.get("expected_outcome", "value"))
    if expected_outcome == "trap":
        head, tail = app_arguments(instructions, "kseq", 2)
        empty, end = app_arguments(tail, "kseq", 2)
        if unwrap_injection(head).get("name") != "Lbltrap" or unwrap_injection(empty).get("name") != "LblinstrEmpty" or end.get("name") != "dotk":
            raise GateError(f"{case['id']} did not finish with a trap: {instructions}")
        if cell(state, "valstack").get("name") != "Lblempty":
            raise GateError(f"{case['id']} trapped with an unexpected stack")
        return {"id": str(case["id"]), "outcome": "trap"}

    if instructions.get("tag") != "App" or instructions.get("name") != "dotk":
        raise GateError(f"{case['id']} did not finish its instruction stream: {instructions}")
    value, tail = app_arguments(cell(state, "valstack"), "cons", 2)
    if tail.get("name") != "Lblempty":
        raise GateError(f"{case['id']} left more than one stack value")
    ty, concrete = app_arguments(value, "integer", 2)
    return {
        "id": str(case["id"]),
        "outcome": "value",
        "type": str(ty.get("name", "")).removeprefix("Lbl"),
        "value": domain_integer(concrete),
    }


def checked(case: Mapping[str, Any], outcome: dict[str, str]) -> dict[str, str]:
    expected = {"id": str(case["id"]), "outcome": str(case.get("expected_outcome", "value"))}
    if expected["outcome"] == "value":
        expected.update(type=str(case["expected_type"]), value=str(case["expected_value"]))
    if outcome != expected:
        raise GateError(f"{case['id']} differs: expected={expected}, actual={outcome}")
    return outcome


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("krs_gate", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--outcomes", type=Path, help="write ordered behavior outcomes as JSON")
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    outcomes = []
    with krs_gate.Session(arguments.krs_gate) as session:
        session.load(arguments.definition, arguments.module)
        for case in cases:
            result = session.execute(initial_pattern(case))
            if not isinstance(result, dict):
                raise GateError(f"native result shape differs: {result}")
            outcomes.append(checked(case, observed(case, sole_state(result))))
    digest = json_sha256(outcomes)
    if arguments.outcomes is not None:
        arguments.outcomes.write_text(canonical_json(outcomes) + "\n", encoding="utf-8")
    print(f"PASS native KWasm behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
