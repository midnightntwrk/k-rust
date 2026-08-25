#!/usr/bin/env python3
"""Trusted-small independent check of the actual official KAST substitution."""

import argparse
import json
from pathlib import Path
from typing import Any


EXPECTED = {
    "ID": ("String", "ruleTargetLineage"),
    "LABEL": ("String", "ruleTargetLabel"),
    "MODULE": ("String", "ruleTargetModule"),
    "SOURCE": ("String", "ruleTargetSource"),
    "LOCATION": ("String", "ruleTargetLocation"),
    "REST": ("List", None),
}


def fail(message: str) -> None:
    raise SystemExit(f"trusted oracle: {message}")


def label(term: Any) -> tuple[str, list[str]] | None:
    if not isinstance(term, dict) or term.get("node") != "KApply":
        return None
    value = term.get("label")
    if not isinstance(value, dict) or value.get("node") != "KLabel":
        return None
    params = value.get("params")
    if not isinstance(params, list):
        return None
    names: list[str] = []
    for item in params:
        if not isinstance(item, dict) or item.get("node") != "KSort" or item.get("params") != []:
            return None
        names.append(item.get("name"))
    return value.get("name"), names


def leaves(term: Any) -> list[Any]:
    if label(term) == ("#And", ["GeneratedTopCell"]) and term.get("arity") == 2:
        args = term.get("args")
        if not isinstance(args, list) or len(args) != 2:
            fail("malformed conjunction")
        return leaves(args[0]) + leaves(args[1])
    return [term]


def decode_string(value: Any) -> str:
    if not isinstance(value, dict) or value.get("node") != "KToken":
        fail("witness value is not a token")
    token_sort = value.get("sort")
    if not isinstance(token_sort, dict) or token_sort.get("node") != "KSort" \
            or token_sort.get("name") != "String" or token_sort.get("params") != []:
        fail("witness token is not String")
    try:
        result = json.loads(value.get("token"))
    except (TypeError, json.JSONDecodeError):
        fail("witness token is not K string encoding")
    if not isinstance(result, str):
        fail("witness token is not a string")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("kast", type=Path)
    parser.add_argument("driver", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    document = json.loads(args.kast.read_text(encoding="utf-8"))
    driver = json.loads(args.driver.read_text(encoding="utf-8"))
    if document.get("format") != "KAST" or document.get("version") != 4:
        fail("wrong official envelope")

    found: dict[str, Any] = {}
    for leaf in leaves(document.get("term")):
        leaf_label = label(leaf)
        if leaf_label is None or leaf_label[0] != "#Equals" or len(leaf_label[1]) != 2:
            fail("non-equality residual in substitution")
        arguments = leaf.get("args")
        if not isinstance(arguments, list) or len(arguments) != 2:
            fail("malformed equality")
        variable, value = arguments
        if not isinstance(variable, dict) or variable.get("node") != "KVariable":
            fail("equality does not bind a variable")
        name = variable.get("name")
        if name not in EXPECTED:
            continue
        if name in found:
            fail("duplicate named binding")
        variable_sort = variable.get("sort")
        expected_sort = EXPECTED[name][0]
        if not isinstance(variable_sort, dict) or variable_sort.get("name") != expected_sort:
            fail("named binding sort mismatch")
        found[name] = value
    if set(found) != set(EXPECTED):
        fail("named witness bindings are incomplete")

    for name, (_, driver_key) in EXPECTED.items():
        value = found[name]
        if name == "REST":
            if label(value) != (".List", []) or value.get("arity") != 0 or value.get("args") != []:
                fail("tail is not empty List")
        elif decode_string(value) != driver.get(driver_key):
            fail("witness differs from independent driver target")

    result = {
        "officialKastVersion": 4,
        "fiveWitnessTermsPresent": True,
        "fiveWitnessTermsEqualDriverTarget": True,
        "emptyListTailPresent": True,
        "namedBindingCount": 6,
    }
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
