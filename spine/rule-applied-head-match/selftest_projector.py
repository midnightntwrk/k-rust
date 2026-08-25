#!/usr/bin/env python3
"""Focused fail-closed tests; these make no compiler or backend invocation."""

from __future__ import annotations

import argparse
import copy
import json
import tempfile
from pathlib import Path
from typing import Any, Callable

import project_match as projector


def ksort(name: str) -> dict[str, Any]:
    return {"node": "KSort", "name": name, "params": []}


def klabel(name: str, params: list[str]) -> dict[str, Any]:
    return {"node": "KLabel", "name": name, "params": [ksort(item) for item in params]}


def kapp(name: str, params: list[str], args: list[Any]) -> dict[str, Any]:
    return {"node": "KApply", "label": klabel(name, params), "arity": len(args), "args": args}


def conjunction(leaves: list[Any]) -> Any:
    if not leaves:
        raise ValueError("cannot build empty conjunction")
    result = leaves[0]
    for leaf in leaves[1:]:
        result = kapp("#And", ["GeneratedTopCell"], [result, leaf])
    return result


def named_leaf(document: dict[str, Any], name: str) -> dict[str, Any]:
    for leaf in projector.flatten_conjunction(document["term"]):
        variable = leaf["args"][0]
        if variable.get("name") == name:
            return leaf
    raise ValueError(f"missing {name}")


def envelope(term: Any) -> dict[str, Any]:
    return {"format": "KAST", "version": 4, "term": term}


def expect_error(name: str, operation: Callable[[], Any], results: list[dict[str, Any]]) -> None:
    try:
        operation()
    except projector.EnvelopeError:
        results.append({"case": name, "classification": "error", "rejected": True})
        return
    raise SystemExit(f"self-test unexpectedly accepted {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("kast", type=Path)
    parser.add_argument("driver", type=Path)
    parser.add_argument("runtime", type=Path)
    parser.add_argument("portable_runtime", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    valid = projector.load_document(args.kast)
    driver = json.loads(args.driver.read_text(encoding="utf-8"))
    runtime = json.loads(args.runtime.read_text(encoding="utf-8"))
    portable_runtime = json.loads(args.portable_runtime.read_text(encoding="utf-8"))
    projector.project_match(valid, driver, runtime, portable_runtime)
    results: list[dict[str, Any]] = []

    leaves = projector.flatten_conjunction(valid["term"])
    duplicate = copy.deepcopy(valid)
    duplicate["term"] = conjunction(copy.deepcopy(leaves + [leaves[0]]))
    expect_error("duplicate named binding", lambda: projector.project_match(
        duplicate, driver, runtime, portable_runtime), results)

    missing = copy.deepcopy(valid)
    missing["term"] = conjunction([copy.deepcopy(leaf) for leaf in leaves
                                    if leaf["args"][0].get("name") != "ID"])
    expect_error("missing named binding", lambda: projector.project_match(
        missing, driver, runtime, portable_runtime), results)

    unexpected = copy.deepcopy(valid)
    named_leaf(unexpected, "ID")["args"][0]["name"] = "UNEXPECTED"
    expect_error("unexpected named binding", lambda: projector.project_match(
        unexpected, driver, runtime, portable_runtime), results)

    wrong_variable_sort = copy.deepcopy(valid)
    id_leaf = named_leaf(wrong_variable_sort, "ID")
    id_leaf["args"][0]["sort"] = ksort("Int")
    id_leaf["label"]["params"][0] = ksort("Int")
    expect_error("wrong variable sort", lambda: projector.project_match(
        wrong_variable_sort, driver, runtime, portable_runtime), results)

    wrong_token_sort = copy.deepcopy(valid)
    named_leaf(wrong_token_sort, "ID")["args"][1]["sort"] = ksort("Int")
    expect_error("wrong token sort", lambda: projector.project_match(
        wrong_token_sort, driver, runtime, portable_runtime), results)

    malformed_token = copy.deepcopy(valid)
    named_leaf(malformed_token, "LABEL")["args"][1]["token"] = '"unterminated'
    expect_error("malformed string token", lambda: projector.project_match(
        malformed_token, driver, runtime, portable_runtime), results)

    noncanonical_token = copy.deepcopy(valid)
    named_leaf(noncanonical_token, "LABEL")["args"][1]["token"] = '"bump\\u002dstate"'
    expect_error("noncanonical string token", lambda: projector.project_match(
        noncanonical_token, driver, runtime, portable_runtime), results)

    nonempty_rest = copy.deepcopy(valid)
    named_leaf(nonempty_rest, "REST")["args"][1] = kapp("_List_", [], [
        kapp(".List", [], []), kapp(".List", [], [])])
    expect_error("non-empty REST", lambda: projector.project_match(
        nonempty_rest, driver, runtime, portable_runtime), results)

    malformed_rest = copy.deepcopy(valid)
    named_leaf(malformed_rest, "REST")["args"][1] = {
        "node": "KToken", "sort": ksort("List"), "token": ".List"}
    expect_error("malformed REST", lambda: projector.project_match(
        malformed_rest, driver, runtime, portable_runtime), results)

    wrong_raw = copy.deepcopy(driver)
    wrong_raw["ruleTargetLabel"] = "wrong-after-valid-substitution"
    expect_error("wrong raw origin after valid substitution", lambda: projector.project_match(
        valid, wrong_raw, runtime, portable_runtime), results)

    malformed_completion = copy.deepcopy(valid)
    named_leaf(malformed_completion, "_Gen0")["args"][1] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("wrong generated completion wrapper", lambda: projector.project_match(
        malformed_completion, driver, runtime, portable_runtime), results)

    k_body_string = copy.deepcopy(valid)
    named_leaf(k_body_string, "_Gen0")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("KCell body is not KSequence", lambda: projector.project_match(
        k_body_string, driver, runtime, portable_runtime), results)

    k_item_string = copy.deepcopy(valid)
    named_leaf(k_item_string, "_Gen0")["args"][1]["args"][0]["items"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("KCell sequence item has wrong sort", lambda: projector.project_match(
        k_item_string, driver, runtime, portable_runtime), results)

    state_body_string = copy.deepcopy(valid)
    named_leaf(state_body_string, "_Gen1")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("StateCell body has wrong sort", lambda: projector.project_match(
        state_body_string, driver, runtime, portable_runtime), results)

    counter_body_string = copy.deepcopy(valid)
    named_leaf(counter_body_string, "_DotVar0")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("GeneratedCounterCell body has wrong sort", lambda: projector.project_match(
        counter_body_string, driver, runtime, portable_runtime), results)

    noncanonical_int = copy.deepcopy(valid)
    named_leaf(noncanonical_int, "_Gen1")["args"][1]["args"][0]["token"] = "02"
    expect_error("generated completion has noncanonical Int", lambda: projector.project_match(
        noncanonical_int, driver, runtime, portable_runtime), results)

    malformed_bottom = envelope(kapp("#Bottom", ["GeneratedTopCell"], [kapp(".List", [], [])]))
    expect_error("malformed Bottom", lambda: projector.project_no_match(malformed_bottom), results)

    residual = envelope(kapp("#Or", ["GeneratedTopCell"], [
        kapp("#Bottom", ["GeneratedTopCell"], []),
        kapp("#Bottom", ["GeneratedTopCell"], [])]))
    expect_error("residual KAST content", lambda: projector.project_no_match(residual), results)

    unsupported_version = copy.deepcopy(valid)
    unsupported_version["version"] = 3
    with tempfile.TemporaryDirectory() as directory:
        temp = Path(directory)
        version_path = temp / "version.json"
        version_path.write_text(json.dumps(unsupported_version), encoding="utf-8")
        expect_error("unsupported KAST version", lambda: projector.load_document(version_path), results)
        noninteger_version = copy.deepcopy(valid)
        noninteger_version["version"] = 4.0
        noninteger_version_path = temp / "noninteger-version.json"
        noninteger_version_path.write_text(json.dumps(noninteger_version), encoding="utf-8")
        expect_error("non-integer KAST version", lambda: projector.load_document(
            noninteger_version_path), results)
        trailing_path = temp / "trailing.json"
        trailing_path.write_text(json.dumps(valid) + "\n{}\n", encoding="utf-8")
        expect_error("trailing JSON", lambda: projector.load_document(trailing_path), results)
        unsupported_node = copy.deepcopy(valid)
        named_leaf(unsupported_node, "ID")["args"][1] = {"node": "KRewrite"}
        node_path = temp / "node.json"
        node_path.write_text(json.dumps(unsupported_node), encoding="utf-8")
        expect_error("unsupported KAST node", lambda: projector.load_document(node_path), results)

    output = {
        "verdict": "pass",
        "classification": "projector envelope errors, never semantic no-match",
        "compilerBackendInvocations": 0,
        "caseCount": len(results),
        "cases": sorted(results, key=lambda item: item["case"]),
    }
    args.output.write_text(json.dumps(output, sort_keys=True, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
