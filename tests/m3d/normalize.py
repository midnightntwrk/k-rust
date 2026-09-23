"""The recovered M3D proof and claim normalizers.

The M3D gate and the M4 proof comparison both normalize kprove output with
these functions, so the recovered normalization has one home. Importers put
`tests/` on `sys.path` first.
"""

from __future__ import annotations

import copy
import json
from typing import Any

from support.hashing import canonical_json


# This is the exact closed metadata set copied from the lost M3D normalizer.
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


def envelope(stdout: str) -> dict[str, Any]:
    value = json.loads(stdout)
    if (
        set(value) != {"format", "version", "term"}
        or value["format"] != "KAST"
        or value["version"] != 4
    ):
        raise ValueError("proof/execution output is not exactly a KAST v4 envelope")
    return value


def normalize_proof(value: dict[str, Any]) -> dict[str, Any]:
    """Exact recovered M3D proof normalizer, with a closed KAST node set."""

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
    """Exact recovered M3D claim normalizer, including metadata erasure."""

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
            variable_key = (result["name"], sort)
            variables.setdefault(variable_key, f"V{len(variables)}")
            result["name"] = variables[variable_key]
        if isinstance(result.get("imports"), list):
            result["imports"].sort(key=canonical_json)
        if isinstance(result.get("localSentences"), list):
            result["localSentences"].sort(key=canonical_json)
        return result

    return visit(value)
