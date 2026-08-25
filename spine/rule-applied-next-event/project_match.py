#!/usr/bin/env python3
"""Validate the pinned exact-pair KAST substitution before projection."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


class EnvelopeError(ValueError):
    """The official KAST result did not have the pinned result envelope."""


NAMED_SORTS = {
    "ID": "String",
    "LABEL": "String",
    "MODULE": "String",
    "SOURCE": "String",
    "LOCATION": "String",
}
ORIGIN_KEYS = {
    "ID": "id",
    "LABEL": "label",
    "MODULE": "module",
    "SOURCE": "source",
    "LOCATION": "location",
}
GENERATED_NAME = re.compile(r"^_(?:DotVar|Gen)[0-9]+$")
GENERATED_COMPLETION_CELLS = {
    "GeneratedCounterCell": ("_DotVar", "<generatedCounter>"),
    "KCell": ("_Gen", "<k>"),
    "StateCell": ("_Gen", "<state>"),
}
CANONICAL_INT = re.compile(r"^(?:0|-?[1-9][0-9]*)$")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise EnvelopeError(message)


def exact_keys(value: Any, keys: set[str], context: str) -> dict[str, Any]:
    require(isinstance(value, dict), f"{context} is not an object")
    require(set(value) == keys, f"{context} has unexpected fields")
    return value


def sort(name: str) -> dict[str, Any]:
    return {"node": "KSort", "name": name, "params": []}


def validate_sort(value: Any, context: str) -> str:
    node = exact_keys(value, {"node", "name", "params"}, context)
    require(node["node"] == "KSort", f"{context} is not KSort")
    require(isinstance(node["name"], str), f"{context} name is not a string")
    require(node["params"] == [], f"{context} is unexpectedly parametric")
    return node["name"]


def validate_label(value: Any, context: str) -> tuple[str, list[str]]:
    node = exact_keys(value, {"node", "name", "params"}, context)
    require(node["node"] == "KLabel", f"{context} is not KLabel")
    require(isinstance(node["name"], str), f"{context} name is not a string")
    require(isinstance(node["params"], list), f"{context} params are not a list")
    return node["name"], [
        validate_sort(item, f"{context} param") for item in node["params"]
    ]


def validate_term(value: Any, context: str = "term") -> None:
    require(isinstance(value, dict), f"{context} is not an object")
    node_name = value.get("node")
    if node_name == "KApply":
        node = exact_keys(value, {"node", "label", "arity", "args"}, context)
        validate_label(node["label"], f"{context} label")
        require(type(node["arity"]) is int, f"{context} arity is not an integer")
        require(isinstance(node["args"], list), f"{context} args are not a list")
        require(node["arity"] == len(node["args"]), f"{context} arity is inconsistent")
        for index, child in enumerate(node["args"]):
            validate_term(child, f"{context} arg {index}")
    elif node_name == "KVariable":
        node = exact_keys(value, {"node", "name", "sort"}, context)
        require(isinstance(node["name"], str), f"{context} name is not a string")
        validate_sort(node["sort"], f"{context} sort")
    elif node_name == "KToken":
        node = exact_keys(value, {"node", "sort", "token"}, context)
        validate_sort(node["sort"], f"{context} sort")
        require(isinstance(node["token"], str), f"{context} token is not a string")
    elif node_name == "KSequence":
        node = exact_keys(value, {"node", "arity", "items"}, context)
        require(type(node["arity"]) is int, f"{context} arity is not an integer")
        require(isinstance(node["items"], list), f"{context} items are not a list")
        require(node["arity"] == len(node["items"]), f"{context} arity is inconsistent")
        for index, child in enumerate(node["items"]):
            validate_term(child, f"{context} item {index}")
    else:
        raise EnvelopeError(f"{context} has unsupported KAST node")


def load_document(path: Path) -> dict[str, Any]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (UnicodeError, OSError, json.JSONDecodeError) as error:
        raise EnvelopeError("invalid or trailing JSON") from error
    envelope = exact_keys(document, {"format", "version", "term"}, "KAST envelope")
    require(envelope["format"] == "KAST", "unsupported KAST format")
    require(type(envelope["version"]) is int and envelope["version"] == 4,
            "unsupported KAST version")
    validate_term(envelope["term"])
    return envelope


def application(value: Any, name: str, params: list[str], arity: int,
                context: str) -> list[Any]:
    node = exact_keys(value, {"node", "label", "arity", "args"}, context)
    require(node["node"] == "KApply", f"{context} is not KApply")
    actual_name, actual_params = validate_label(node["label"], f"{context} label")
    require((actual_name, actual_params) == (name, params), f"{context} has wrong label")
    require(node["arity"] == arity and len(node["args"]) == arity,
            f"{context} has wrong arity")
    return node["args"]


def is_application(value: Any, name: str, params: list[str], arity: int) -> bool:
    try:
        application(value, name, params, arity, "application")
        return True
    except EnvelopeError:
        return False


def flatten_conjunction(value: Any) -> list[Any]:
    if is_application(value, "#And", ["GeneratedTopCell"], 2):
        left, right = application(value, "#And", ["GeneratedTopCell"], 2,
                                  "substitution conjunction")
        return flatten_conjunction(left) + flatten_conjunction(right)
    require(not is_application(value, "#Equals", [], 2),
            "unparameterized equality is unsupported")
    return [value]


def decode_string_token(value: Any, variable: str) -> str:
    node = exact_keys(value, {"node", "sort", "token"}, f"{variable} value")
    require(node["node"] == "KToken", f"{variable} value is not KToken")
    require(validate_sort(node["sort"], f"{variable} token sort") == "String",
            f"{variable} token has wrong sort")
    token = node["token"]
    try:
        decoded = json.loads(token)
    except json.JSONDecodeError as error:
        raise EnvelopeError(f"{variable} has malformed K string encoding") from error
    require(isinstance(decoded, str), f"{variable} token did not encode a string")
    require(json.dumps(decoded, ensure_ascii=False) == token,
            f"{variable} has noncanonical K string encoding")
    return decoded


def validate_int_token(value: Any, context: str) -> None:
    node = exact_keys(value, {"node", "sort", "token"}, context)
    require(node["node"] == "KToken", f"{context} is not KToken")
    require(validate_sort(node["sort"], f"{context} sort") == "Int",
            f"{context} is not an Int token")
    require(isinstance(node["token"], str)
            and CANONICAL_INT.fullmatch(node["token"]) is not None,
            f"{context} is not a canonical Int token")


def validate_generated_completion(value: Any, variable_sort: str,
                                  cell_label: str, context: str) -> None:
    body = application(value, cell_label, [], 1, context)[0]
    if variable_sort in ("GeneratedCounterCell", "StateCell"):
        validate_int_token(body, f"{context} body")
        return
    require(variable_sort == "KCell", f"{context} has unsupported cell sort")
    sequence = exact_keys(body, {"node", "arity", "items"}, f"{context} body")
    require(sequence["node"] == "KSequence", f"{context} body is not KSequence")
    require(sequence["arity"] == 1 and isinstance(sequence["items"], list)
            and len(sequence["items"]) == 1,
            f"{context} KSequence is not the exact singleton completion shape")
    validate_int_token(sequence["items"][0], f"{context} KSequence item")


def parse_substitution(term: Any) -> tuple[dict[str, Any], list[str]]:
    leaves = flatten_conjunction(term)
    require(len(leaves) == len(NAMED_SORTS) + len(GENERATED_COMPLETION_CELLS),
            "substitution has wrong binding cardinality")
    bindings: dict[str, Any] = {}
    generated: list[str] = []
    generated_sorts: list[str] = []
    for index, leaf in enumerate(leaves):
        node = exact_keys(leaf, {"node", "label", "arity", "args"}, f"binding {index}")
        require(node["node"] == "KApply", f"binding {index} is not KApply")
        label_name, label_params = validate_label(node["label"], f"binding {index} label")
        require(label_name == "#Equals" and len(label_params) == 2
                and label_params[1] == "GeneratedTopCell",
                f"binding {index} is not a pinned equality")
        require(node["arity"] == 2 and len(node["args"]) == 2,
                f"binding {index} has wrong arity")
        variable, value = node["args"]
        variable_node = exact_keys(variable, {"node", "name", "sort"},
                                   f"binding {index} variable")
        require(variable_node["node"] == "KVariable",
                f"binding {index} left side is not a variable")
        name = variable_node["name"]
        require(isinstance(name, str), f"binding {index} variable name is invalid")
        variable_sort = validate_sort(variable_node["sort"], f"binding {name} sort")
        require(variable_sort == label_params[0], f"binding {name} sort disagrees with equality")
        require(name not in bindings, f"duplicate binding for {name}")
        if name in NAMED_SORTS:
            require(variable_sort == NAMED_SORTS[name], f"binding {name} has wrong sort")
        else:
            require(GENERATED_NAME.fullmatch(name) is not None,
                    f"unexpected non-anonymous binding {name}")
            require(variable_sort in GENERATED_COMPLETION_CELLS,
                    f"generated binding {name} has unsupported completion sort")
            prefix, cell_label = GENERATED_COMPLETION_CELLS[variable_sort]
            require(name.startswith(prefix),
                    f"generated binding {name} disagrees with completion sort")
            validate_generated_completion(value, variable_sort, cell_label,
                                          f"generated binding {name} value")
            generated.append(name)
            generated_sorts.append(variable_sort)
        bindings[name] = value
    require(set(bindings).issuperset(NAMED_SORTS), "missing required named binding")
    require(sorted(generated_sorts) == sorted(GENERATED_COMPLETION_CELLS),
            "official generated completion bindings are incomplete or duplicated")
    return bindings, sorted(generated)


def raw_origin_from_driver(driver: dict[str, Any]) -> dict[str, str]:
    fields = {
        "id": driver.get("ruleTargetLineage"),
        "label": driver.get("ruleTargetLabel"),
        "module": driver.get("ruleTargetModule"),
        "source": driver.get("ruleTargetSource"),
        "location": driver.get("ruleTargetLocation"),
    }
    require(all(isinstance(value, str) for value in fields.values()),
            "driver raw origin is incomplete")
    return fields  # type: ignore[return-value]


def portable_origin_from_driver(driver: dict[str, Any]) -> dict[str, str]:
    fields = {
        "id": driver.get("portableRuleTargetLineage"),
        "label": driver.get("portableRuleTargetLabel"),
        "module": driver.get("portableRuleTargetModule"),
        "source": driver.get("portableRuleTargetSource"),
        "location": driver.get("portableRuleTargetLocation"),
    }
    require(all(isinstance(value, str) for value in fields.values()),
            "driver portable origin is incomplete")
    return fields  # type: ignore[return-value]


def load_json_object(path: Path, context: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (UnicodeError, OSError, json.JSONDecodeError) as error:
        raise EnvelopeError(f"invalid {context} JSON") from error
    require(isinstance(value, dict), f"{context} is not an object")
    return value


def runtime_origins(runtime: dict[str, Any]) -> list[dict[str, Any]]:
    trace = runtime.get("trace")
    require(isinstance(trace, list) and len(trace) == 2,
            "raw runtime trace is not an exact pair")
    origins: list[dict[str, Any]] = []
    for event in trace:
        require(isinstance(event, dict) and set(event) == {"kind", "origin"}
                and event.get("kind") == "RuleApplied",
                "raw runtime event is not exact RuleApplied")
        origin = event.get("origin")
        require(isinstance(origin, dict)
                and set(origin) == {"id", "label", "module", "source", "location"}
                and all(isinstance(value, str) for value in origin.values()),
                "raw runtime origin is malformed")
        origins.append(origin)
    return origins


def bottom(term: Any) -> bool:
    return term == {
        "node": "KApply",
        "label": {"node": "KLabel", "name": "#Bottom",
                  "params": [sort("GeneratedTopCell")]},
        "arity": 0,
        "args": [],
    }


def project_match(document: dict[str, Any], driver: dict[str, Any],
                  runtime: dict[str, Any]) -> dict[str, Any]:
    require(not bottom(document["term"]), "expected match, found #Bottom")
    bindings, generated = parse_substitution(document["term"])
    raw_origin = {
        ORIGIN_KEYS[name]: decode_string_token(bindings[name], name)
        for name in ORIGIN_KEYS
    }
    expected_raw = raw_origin_from_driver(driver)
    require(raw_origin == expected_raw, "substitution raw origin differs from driver target")
    raw_events = runtime_origins(runtime)
    require(raw_events == [expected_raw, expected_raw],
            "raw runtime pair differs from the shared driver target")
    portable_origin = portable_origin_from_driver(driver)
    return {
        "status": "match",
        "eventIndices": [0, 1],
        "constructors": ["RuleApplied", "RuleApplied"],
        "witnesses": [
            {"origin": portable_origin},
            {"origin": portable_origin},
        ],
        "bindingSorts": NAMED_SORTS,
        "exactTraceExhaustion": {"ownedBy": "K", "literal": ".List",
                                 "remainingEventCount": 0},
        "generatedCompletionBindings": {
            "allowed": True, "count": len(generated), "namesOmitted": True,
        },
        "rawValidation": {
            "fiveFieldSubstitutionEqualsDriverTarget": True,
            "bothRawRuntimeOriginsEqualSubstitutionAndDriverTarget": True,
            "twoRawRuntimeOriginsEqual": True,
            "rawValuesOmitted": True,
            "portableProjectionAfterRawValidation": True,
        },
    }


def project_no_match(document: dict[str, Any]) -> dict[str, Any]:
    require(bottom(document["term"]), "no-match result is not exact pinned #Bottom")
    return {
        "status": "no-match",
        "officialResult": "#Bottom{GeneratedTopCell}()",
        "classification": "exhaustive terminating concrete execution",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--expect", choices=("match", "no-match"), required=True)
    parser.add_argument("--driver", type=Path)
    parser.add_argument("--runtime", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    document = load_document(args.input)
    if args.expect == "match":
        require(args.driver is not None and args.runtime is not None,
                "match projection requires driver and runtime records")
        result = project_match(
            document,
            load_json_object(args.driver, "driver"),
            load_json_object(args.runtime, "runtime"),
        )
    else:
        require(args.driver is None and args.runtime is None,
                "no-match projection does not accept semantic side inputs")
        result = project_no_match(document)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    try:
        main()
    except EnvelopeError as error:
        raise SystemExit(f"envelope error: {error}") from error
