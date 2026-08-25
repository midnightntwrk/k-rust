#!/usr/bin/env python3
"""Focused fail-closed tests with zero compiler/backend invocations."""

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
    return {"node": "KLabel", "name": name,
            "params": [ksort(item) for item in params]}


def kapp(name: str, params: list[str], args: list[Any]) -> dict[str, Any]:
    return {"node": "KApply", "label": klabel(name, params),
            "arity": len(args), "args": args}


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


def generated_leaf(document: dict[str, Any], sort_name: str) -> dict[str, Any]:
    for leaf in projector.flatten_conjunction(document["term"]):
        variable = leaf["args"][0]
        if variable.get("sort", {}).get("name") == sort_name:
            return leaf
    raise ValueError(f"missing generated {sort_name}")


def envelope(term: Any) -> dict[str, Any]:
    return {"format": "KAST", "version": 4, "term": term}


def expect_error(name: str, operation: Callable[[], Any],
                 results: list[dict[str, Any]]) -> None:
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
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    valid = projector.load_document(args.kast)
    driver = json.loads(args.driver.read_text(encoding="utf-8"))
    runtime = json.loads(args.runtime.read_text(encoding="utf-8"))
    projector.project_match(valid, driver, runtime)
    results: list[dict[str, Any]] = []
    leaves = projector.flatten_conjunction(valid["term"])

    duplicate = copy.deepcopy(valid)
    duplicate["term"] = conjunction(copy.deepcopy(leaves + [named_leaf(valid, "ID")]))
    expect_error("duplicated named binding", lambda: projector.project_match(
        duplicate, driver, runtime), results)

    duplicate_second = copy.deepcopy(valid)
    duplicate_second["term"] = conjunction(copy.deepcopy(
        leaves + [named_leaf(valid, "LABEL")]))
    expect_error("named variable appears twice", lambda: projector.project_match(
        duplicate_second, driver, runtime), results)

    missing = copy.deepcopy(valid)
    missing["term"] = conjunction([copy.deepcopy(leaf) for leaf in leaves
                                    if leaf["args"][0].get("name") != "ID"])
    expect_error("missing named binding", lambda: projector.project_match(
        missing, driver, runtime), results)

    unexpected = copy.deepcopy(valid)
    named_leaf(unexpected, "ID")["args"][0]["name"] = "UNEXPECTED"
    expect_error("unexpected named binding", lambda: projector.project_match(
        unexpected, driver, runtime), results)

    wrong_variable_sort = copy.deepcopy(valid)
    id_leaf = named_leaf(wrong_variable_sort, "ID")
    id_leaf["args"][0]["sort"] = ksort("Int")
    id_leaf["label"]["params"][0] = ksort("Int")
    expect_error("wrong variable sort", lambda: projector.project_match(
        wrong_variable_sort, driver, runtime), results)

    wrong_token_sort = copy.deepcopy(valid)
    named_leaf(wrong_token_sort, "ID")["args"][1]["sort"] = ksort("Int")
    expect_error("wrong token sort", lambda: projector.project_match(
        wrong_token_sort, driver, runtime), results)

    malformed_token = copy.deepcopy(valid)
    named_leaf(malformed_token, "LABEL")["args"][1]["token"] = '"unterminated'
    expect_error("malformed string token", lambda: projector.project_match(
        malformed_token, driver, runtime), results)

    noncanonical_token = copy.deepcopy(valid)
    named_leaf(noncanonical_token, "LABEL")["args"][1]["token"] = '"bump\\u002dstate"'
    expect_error("noncanonical string token", lambda: projector.project_match(
        noncanonical_token, driver, runtime), results)

    rest_leaf = copy.deepcopy(named_leaf(valid, "ID"))
    rest_leaf["args"][0] = {"node": "KVariable", "name": "REST", "sort": ksort("List")}
    rest_leaf["label"]["params"][0] = ksort("List")
    rest_leaf["args"][1] = kapp(".List", [], [])
    synthetic_rest = copy.deepcopy(valid)
    synthetic_rest["term"] = conjunction(copy.deepcopy(leaves + [rest_leaf]))
    expect_error("host-supplied synthetic REST", lambda: projector.project_match(
        synthetic_rest, driver, runtime), results)

    rest_leaf["args"][1] = kapp("_List_", [], [
        kapp("ListItem", [], [kapp(".List", [], [])]), kapp(".List", [], [])])
    nonexhaustion = copy.deepcopy(valid)
    nonexhaustion["term"] = conjunction(copy.deepcopy(leaves + [rest_leaf]))
    expect_error("host-supplied non-exhaustion claim", lambda: projector.project_match(
        nonexhaustion, driver, runtime), results)

    wrong_raw = copy.deepcopy(driver)
    wrong_raw["ruleTargetLabel"] = "wrong-after-valid-substitution"
    expect_error("raw origin differs from driver", lambda: projector.project_match(
        valid, wrong_raw, runtime), results)

    wrong_runtime = copy.deepcopy(runtime)
    wrong_runtime["trace"][1]["origin"]["label"] = "different-second-origin"
    expect_error("raw runtime origins differ", lambda: projector.project_match(
        valid, driver, wrong_runtime), results)

    malformed_completion = copy.deepcopy(valid)
    generated_leaf(malformed_completion, "KCell")["args"][1] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("wrong generated completion wrapper", lambda: projector.project_match(
        malformed_completion, driver, runtime), results)

    k_body = copy.deepcopy(valid)
    generated_leaf(k_body, "KCell")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("KCell body is not KSequence", lambda: projector.project_match(
        k_body, driver, runtime), results)

    k_item = copy.deepcopy(valid)
    generated_leaf(k_item, "KCell")["args"][1]["args"][0]["items"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("KCell sequence item wrong sort", lambda: projector.project_match(
        k_item, driver, runtime), results)

    state_body = copy.deepcopy(valid)
    generated_leaf(state_body, "StateCell")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("StateCell body wrong sort", lambda: projector.project_match(
        state_body, driver, runtime), results)

    counter_body = copy.deepcopy(valid)
    generated_leaf(counter_body, "GeneratedCounterCell")["args"][1]["args"][0] = {
        "node": "KToken", "sort": ksort("String"), "token": '"bad"'}
    expect_error("GeneratedCounterCell body wrong sort", lambda: projector.project_match(
        counter_body, driver, runtime), results)

    noncanonical_int = copy.deepcopy(valid)
    generated_leaf(noncanonical_int, "StateCell")["args"][1]["args"][0]["token"] = "02"
    expect_error("generated completion noncanonical Int", lambda: projector.project_match(
        noncanonical_int, driver, runtime), results)

    generated_duplicate = copy.deepcopy(valid)
    generated_duplicate["term"] = conjunction(copy.deepcopy(
        leaves + [generated_leaf(valid, "StateCell")]))
    expect_error("duplicated generated completion", lambda: projector.project_match(
        generated_duplicate, driver, runtime), results)

    generated_missing = copy.deepcopy(valid)
    generated_missing["term"] = conjunction([
        copy.deepcopy(leaf) for leaf in leaves
        if leaf["args"][0].get("sort", {}).get("name") != "StateCell"
    ])
    expect_error("missing generated completion", lambda: projector.project_match(
        generated_missing, driver, runtime), results)

    malformed_bottom = envelope(kapp("#Bottom", ["GeneratedTopCell"], [
        kapp(".List", [], [])]))
    expect_error("malformed Bottom", lambda: projector.project_no_match(
        malformed_bottom), results)

    residual = envelope(kapp("#Or", ["GeneratedTopCell"], [
        kapp("#Bottom", ["GeneratedTopCell"], []),
        kapp("#Bottom", ["GeneratedTopCell"], [])]))
    expect_error("residual KAST content", lambda: projector.project_no_match(
        residual), results)

    with tempfile.TemporaryDirectory() as directory:
        temp = Path(directory)
        unsupported_version = copy.deepcopy(valid)
        unsupported_version["version"] = 3
        version_path = temp / "version.json"
        version_path.write_text(json.dumps(unsupported_version), encoding="utf-8")
        expect_error("unsupported KAST version", lambda: projector.load_document(
            version_path), results)
        noninteger_version = copy.deepcopy(valid)
        noninteger_version["version"] = 4.0
        noninteger_path = temp / "noninteger-version.json"
        noninteger_path.write_text(json.dumps(noninteger_version), encoding="utf-8")
        expect_error("non-integer KAST version", lambda: projector.load_document(
            noninteger_path), results)
        trailing_path = temp / "trailing.json"
        trailing_path.write_text(json.dumps(valid) + "\n{}\n", encoding="utf-8")
        expect_error("trailing JSON", lambda: projector.load_document(
            trailing_path), results)
        unsupported_node = copy.deepcopy(valid)
        named_leaf(unsupported_node, "ID")["args"][1] = {"node": "KRewrite"}
        node_path = temp / "node.json"
        node_path.write_text(json.dumps(unsupported_node), encoding="utf-8")
        expect_error("unsupported KAST node", lambda: projector.load_document(
            node_path), results)

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
