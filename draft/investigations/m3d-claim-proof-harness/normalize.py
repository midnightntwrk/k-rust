#!/usr/bin/env python3
"""Frozen M3D proof/claim normalization, copied without broadening its node set."""

from __future__ import annotations

import copy
import hashlib
import json
from typing import Any


METADATA = {
    "org.kframework.attributes.Source",
    "org.kframework.attributes.Location",
    "org.kframework.definition.Production",
    "contentStartLine",
    "contentStartColumn",
    "digest",
    "productionID",
    "UNIQUE_ID",
}


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def envelope(stdout: str) -> dict[str, Any]:
    value = json.loads(stdout)
    if set(value) != {"format", "version", "term"} or value["format"] != "KAST" or value["version"] != 4:
        raise ValueError("proof/execution output is not exactly a KAST v4 envelope")
    return value


def normalize_proof(value: dict[str, Any]) -> dict[str, Any]:
    value = copy.deepcopy(value)
    variables: dict[tuple[str, str], str] = {}

    def visit(node: Any) -> Any:
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        kind = node.get("node")
        if kind == "KVariable":
            if set(node) != {"node", "name", "sort"}:
                raise ValueError(f"unknown KVariable fields: {sorted(node)}")
            sort = node["sort"].get("name")
            if not isinstance(sort, str):
                raise ValueError("proof variable has no concrete sort name")
            key = (node["name"], sort)
            variables.setdefault(key, f"V{len(variables)}")
            node["name"] = variables[key]
        elif kind not in {None, "KApply", "KLabel", "KSort", "KToken", "KSequence"}:
            raise ValueError(f"unclassified proof KAST node {kind!r}")
        return {key: visit(child) for key, child in node.items()}

    return visit(value)


def normalize_claim_spec(value: dict[str, Any]) -> dict[str, Any]:
    value = copy.deepcopy(value)
    variables: dict[tuple[str, str], str] = {}
    allowed = {
        None,
        "KFlatModuleList",
        "KFlatModule",
        "KImport",
        "KClaim",
        "KRewrite",
        "KApply",
        "KLabel",
        "KSort",
        "KToken",
        "KSequence",
        "KVariable",
        "KAtt",
    }

    def visit(node: Any) -> Any:
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        kind = node.get("node")
        if kind not in allowed:
            raise ValueError(f"unclassified claim KAST node {kind!r}")
        result: dict[str, Any] = {}
        for key, child in node.items():
            if kind == "KAtt" and key == "att":
                child = {name: item for name, item in child.items() if name not in METADATA}
            result[key] = visit(child)
        if kind == "KVariable":
            sort = result.get("sort", {}).get("name")
            if not isinstance(sort, str):
                raise ValueError("claim variable has no concrete sort")
            key = (result["name"], sort)
            variables.setdefault(key, f"V{len(variables)}")
            result["name"] = variables[key]
        if isinstance(result.get("imports"), list):
            result["imports"].sort(key=canonical)
        if isinstance(result.get("localSentences"), list):
            result["localSentences"].sort(key=canonical)
        return result

    return visit(value)

