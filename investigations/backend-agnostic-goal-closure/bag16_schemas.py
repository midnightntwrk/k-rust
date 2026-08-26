#!/usr/bin/env python3
"""Deterministic BAG-16 schema registration and version dispatch.

This module reads and composes portable JSON schema metadata only.  It does
not invoke a backend, compiler, executor, solver, or native adapter.
"""

from __future__ import annotations

import hashlib
import json
import re
import unicodedata
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


BAG16_SCHEMA_FILES = (
    "artifact-catalog-v2.schema.json",
    "artifact-role-specs-v2.schema.json",
    "bag16-common.schema.json",
    "branch-trace-collection.schema.json",
    "cache-semantics-v2.schema.json",
    "corpus-component-invocation.schema.json",
    "corpus-component-result.schema.json",
    "corpus-derivation-result.schema.json",
    "corpus-manifest-v2.schema.json",
    "corpus-result-v2.schema.json",
    "empty-search-decision.schema.json",
    "event-trace-v2.schema.json",
    "execution-attempt-result-v2.schema.json",
    "execution-test-invocation-v2.schema.json",
    "operation-invocation-v2.schema.json",
    "operation-receipt-v2.schema.json",
    "pattern-evaluation-result.schema.json",
    "pattern-result-v2.schema.json",
    "portable-closure-root.schema.json",
    "replay-version-registry-v2.schema.json",
)

BAG16_OPERATIONS = (
    ("execution-attempt", 2),
    ("pattern-evaluation", 1),
    ("corpus-derivation", 1),
    ("oracle-operand-production", 2),
)


def _arm(
    schema_version: int,
    schema_id: str,
    digest_domain: str,
    self_id_field: str,
) -> dict[str, Any]:
    return {
        "schemaVersion": schema_version,
        "schemaId": schema_id,
        "digestDomain": digest_domain,
        "projection": {"kind": "without-field", "field": self_id_field},
        "selfIdField": self_id_field,
        "dispatch": {"kind": "schema-version", "schemaVersion": schema_version},
    }


# These descriptors are materialized with exact raw schema-byte digests by
# build_role_spec_registry.  Historical arms are imported from the frozen v1
# registry at build time rather than duplicated here.
BAG16_ROLE_SPECS: Mapping[str, tuple[Mapping[str, Any], ...]] = {
    "branch-trace-collection": (_arm(1, "branch-trace-collection.schema.json", "k-in-k/branch-trace-collection/v1", "collectionId"),),
    "cache-record": (_arm(2, "cache-semantics-v2.schema.json#/$defs/cacheRecord", "k-in-k/cache-record/v2", "recordId"),),
    "corpus-component-invocation": (_arm(1, "corpus-component-invocation.schema.json", "k-in-k/corpus-component-invocation/v1", "componentInvocationId"),),
    "corpus-component-result": (_arm(1, "corpus-component-result.schema.json", "k-in-k/corpus-component-result/v1", "componentResultId"),),
    "corpus-derivation-result": (_arm(1, "corpus-derivation-result.schema.json", "k-in-k/corpus-derivation-result/v1", "resultId"),),
    "corpus-manifest": (_arm(2, "corpus-manifest-v2.schema.json", "k-in-k/corpus-manifest/v2", "manifestId"),),
    "corpus-result": (_arm(2, "corpus-result-v2.schema.json", "k-in-k/corpus-result/v2", "corpusResultId"),),
    "empty-search-decision": (_arm(1, "empty-search-decision.schema.json", "k-in-k/empty-search-decision/v1", "decisionId"),),
    "event-trace": (_arm(2, "event-trace-v2.schema.json", "k-in-k/event-trace/v2", "traceId"),),
    "execution-attempt-result": (_arm(2, "execution-attempt-result-v2.schema.json", "k-in-k/execution-attempt-result/v2", "resultId"),),
    "execution-test-invocation": (_arm(2, "execution-test-invocation-v2.schema.json", "k-in-k/execution-test-invocation/v2", "testInvocationDigest"),),
    "operation-receipt": (_arm(2, "operation-receipt-v2.schema.json", "k-in-k/operation-receipt/v2", "receiptId"),),
    "pattern-evaluation-result": (_arm(1, "pattern-evaluation-result.schema.json", "k-in-k/pattern-evaluation-result/v1", "resultId"),),
    "pattern-result": (_arm(2, "pattern-result-v2.schema.json", "k-in-k/pattern-result/v2", "resultId"),),
    "replay-version-registry": (_arm(2, "replay-version-registry-v2.schema.json", "k-in-k/replay-version-registry/v2", "registryId"),),
}


@dataclass(frozen=True)
class ResolvedSchema:
    """One exact role-spec dispatch result and its bundled schema node."""

    schema_path: Path
    schema_root: Mapping[str, Any]
    schema: Mapping[str, Any]
    arm: Mapping[str, Any]


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def semantic_digest(domain: str, value: Any) -> str:
    normalized = unicodedata.normalize("NFC", canonical(value)).encode("utf-8")
    return hashlib.sha256(domain.encode("ascii") + b"\0" + normalized).hexdigest()


def raw_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _package_root(root: Path) -> Path:
    candidate = root.resolve()
    if (candidate / "schemas").is_dir() and (candidate / "artifact-role-specs.json").is_file():
        return candidate
    nested = candidate / "investigations" / "backend-agnostic-goal-closure"
    if (nested / "schemas").is_dir() and (nested / "artifact-role-specs.json").is_file():
        return nested
    raise ValueError(f"BAG-16 package root is not recognizable: {root}")


def _load(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def schema_documents(root: Path) -> dict[str, dict[str, Any]]:
    package = _package_root(root)
    return {path.name: _load(path) for path in sorted((package / "schemas").glob("*.schema.json"))}


def _pointer(document: Any, fragment: str) -> Any:
    if fragment in {"", "#"}:
        return document
    if not fragment.startswith("#/"):
        raise ValueError(f"unsupported schema fragment: {fragment}")
    current = document
    for token in fragment[2:].split("/"):
        token = token.replace("~1", "/").replace("~0", "~")
        current = current[int(token)] if isinstance(current, list) else current[token]
    return current


def _split_schema_id(schema_id: str) -> tuple[str, str]:
    file_name, separator, tail = schema_id.partition("#")
    return file_name, f"#{tail}" if separator else ""


def _top_level_schema_versions(
    documents: Mapping[str, Mapping[str, Any]],
    file_name: str,
    fragment: str,
    seen: set[tuple[str, str]] | None = None,
) -> set[int]:
    location = (file_name, fragment)
    if seen is None:
        seen = set()
    if location in seen:
        return set()
    seen.add(location)
    node = _pointer(documents[file_name], fragment)
    if not isinstance(node, Mapping):
        return set()
    required = node.get("required")
    properties = node.get("properties")
    if isinstance(required, list) and "schemaVersion" in required and isinstance(properties, Mapping):
        version_schema = properties.get("schemaVersion")
        if isinstance(version_schema, Mapping) and type(version_schema.get("const")) is int:
            return {version_schema["const"]}
    reference = node.get("$ref")
    versions: set[int] = set()
    if isinstance(reference, str):
        target_name, target_fragment = _split_schema_id(reference)
        versions |= _top_level_schema_versions(documents, target_name or file_name, target_fragment, seen)
    for keyword in ("oneOf", "anyOf", "allOf"):
        children = node.get(keyword)
        if isinstance(children, list):
            for index, child in enumerate(children):
                if isinstance(child, Mapping) and isinstance(child.get("$ref"), str):
                    target_name, target_fragment = _split_schema_id(child["$ref"])
                    versions |= _top_level_schema_versions(documents, target_name or file_name, target_fragment, seen)
                elif isinstance(child, Mapping):
                    child_required = child.get("required")
                    child_properties = child.get("properties")
                    if isinstance(child_required, list) and "schemaVersion" in child_required and isinstance(child_properties, Mapping):
                        version_schema = child_properties.get("schemaVersion")
                        if isinstance(version_schema, Mapping) and type(version_schema.get("const")) is int:
                            versions.add(version_schema["const"])
    return versions


def _projection(spec: Mapping[str, Any]) -> dict[str, Any]:
    projection = deepcopy(spec["projection"])
    if projection["kind"] in {"without-field", "field"} and "field" not in projection:
        field = spec.get("selfIdField")
        if not isinstance(field, str):
            raise ValueError(f"projection {projection['kind']} has no field")
        projection["field"] = field
    return projection


def _historical_arm(
    spec: Mapping[str, Any],
    package: Path,
    documents: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    schema_id = spec["schema"]
    file_name, fragment = _split_schema_id(schema_id)
    versions = _top_level_schema_versions(documents, file_name, fragment)
    semantic_version_match = re.search(r"/v([1-9][0-9]*)$", spec["digestDomain"])
    if semantic_version_match is None:
        raise ValueError(f"role {spec['role']} has a nonversioned digest domain")
    semantic_version = int(semantic_version_match.group(1))
    if versions and versions != {semantic_version}:
        raise ValueError(f"role {spec['role']} schema/domain version disagreement: {versions}")
    dispatch = (
        {"kind": "schema-version", "schemaVersion": semantic_version}
        if versions
        else {"kind": "legacy-no-schema-version"}
    )
    return {
        "schemaVersion": semantic_version,
        "schemaId": schema_id,
        "schemaDigest": raw_sha256(package / "schemas" / file_name),
        "digestDomain": spec["digestDomain"],
        "projection": _projection(spec),
        "selfIdField": spec["selfIdField"],
        "dispatch": dispatch,
    }


def _materialize_arm(package: Path, descriptor: Mapping[str, Any]) -> dict[str, Any]:
    result = deepcopy(dict(descriptor))
    file_name, _ = _split_schema_id(result["schemaId"])
    result["schemaDigest"] = raw_sha256(package / "schemas" / file_name)
    return result


def build_role_spec_registry(root: Path) -> dict[str, Any]:
    """Build the exact v2 registry while importing every frozen v1 arm."""

    package = _package_root(root)
    documents = schema_documents(package)
    historical = _load(package / "artifact-role-specs.json")
    by_role: dict[str, dict[str, Any]] = {}
    for spec in historical["specs"]:
        role = spec["role"]
        if spec["contentModel"] == "opaque-bytes":
            by_role[role] = deepcopy(spec)
            continue
        by_role[role] = {
            "role": role,
            "contentModel": "canonical-json",
            "mediaType": "application/json",
            "structuredVersions": [_historical_arm(spec, package, documents)],
        }
    for role, descriptors in BAG16_ROLE_SPECS.items():
        spec = by_role.setdefault(role, {"role": role, "contentModel": "canonical-json", "mediaType": "application/json", "structuredVersions": []})
        if spec["contentModel"] != "canonical-json":
            raise ValueError(f"BAG-16 structured arm collides with opaque role {role}")
        arms = {item["schemaVersion"]: item for item in spec["structuredVersions"]}
        for descriptor in descriptors:
            arm = _materialize_arm(package, descriptor)
            if arm["schemaVersion"] in arms:
                raise ValueError(f"duplicate semantic schema version for role {role}: {arm['schemaVersion']}")
            arms[arm["schemaVersion"]] = arm
        spec["structuredVersions"] = [arms[version] for version in sorted(arms)]
        legacy_count = sum(item["dispatch"]["kind"] == "legacy-no-schema-version" for item in spec["structuredVersions"])
        if legacy_count > 1:
            raise ValueError(f"role {role} has multiple legacy dispatch arms")
    value: dict[str, Any] = {"schemaVersion": 2, "registryId": "0" * 64, "specs": [by_role[role] for role in sorted(by_role)]}
    value["registryId"] = semantic_digest("k-in-k/artifact-role-specs/v2", {name: item for name, item in value.items() if name != "registryId"})
    return value


def select_structured_version(spec: Mapping[str, Any], value: Mapping[str, Any]) -> Mapping[str, Any]:
    """Select exactly one declared arm from the top-level version field."""

    if spec.get("contentModel") != "canonical-json":
        raise ValueError("structured version dispatch requested for an opaque role")
    arms = spec.get("structuredVersions")
    if not isinstance(arms, list) or not arms:
        raise ValueError("structured role has no version arms")
    if "schemaVersion" in value:
        version = value["schemaVersion"]
        if type(version) is not int:
            raise ValueError("top-level schemaVersion is not an integer")
        candidates = [
            arm for arm in arms
            if arm["dispatch"].get("kind") == "schema-version"
            and arm["dispatch"].get("schemaVersion") == version
            and arm["schemaVersion"] == version
        ]
    else:
        candidates = [arm for arm in arms if arm["dispatch"].get("kind") == "legacy-no-schema-version"]
    if len(candidates) != 1:
        raise ValueError(f"structured role selected {len(candidates)} schema arms")
    return candidates[0]


def schema_for_artifact(
    root: Path,
    registry: Mapping[str, Any],
    role: str,
    value: Mapping[str, Any],
) -> ResolvedSchema:
    """Resolve one artifact through role and explicit version dispatch only."""

    package = _package_root(root)
    specs = [spec for spec in registry.get("specs", []) if spec.get("role") == role]
    if len(specs) != 1:
        raise ValueError(f"role {role!r} resolves to {len(specs)} specifications")
    arm = select_structured_version(specs[0], value)
    file_name, fragment = _split_schema_id(arm["schemaId"])
    schema_path = package / "schemas" / file_name
    if raw_sha256(schema_path) != arm["schemaDigest"]:
        raise ValueError(f"schema bytes differ from registered digest: {file_name}")
    schema_root = _load(schema_path)
    schema = _pointer(schema_root, fragment)
    return ResolvedSchema(schema_path, schema_root, schema, arm)


def build_replay_registry(
    root: Path,
    schema_names: Iterable[str],
    operations: Iterable[tuple[str, int]],
) -> dict[str, Any]:
    """Build a sorted, duplicate-free v2 reachable version registry."""

    package = _package_root(root)
    entries: dict[str, dict[str, Any]] = {}
    for schema_id in schema_names:
        file_name, _ = _split_schema_id(schema_id)
        schema_path = package / "schemas" / file_name
        document = _load(schema_path)
        match = re.fullmatch(r"https://starstream\.dev/k-in-k/backend-agnostic/v([1-9][0-9]*)/[^/]+\.schema\.json", document.get("$id", ""))
        if match is None:
            raise ValueError(f"schema has a noncanonical identity: {file_name}")
        entry = {"schemaId": file_name, "schemaVersion": int(match.group(1)), "schemaDigest": raw_sha256(schema_path)}
        if file_name in entries and entries[file_name] != entry:
            raise ValueError(f"conflicting schema registry entry: {file_name}")
        entries[file_name] = entry
    operation_set = set(operations)
    allowed = {
        ("mutation-materialization", 1), ("execution-attempt", 1),
        ("oracle-operand-production", 1), ("baseline-admission", 1),
        ("oracle-comparison", 1), ("campaign-derivation", 1),
        ("report-publication", 1), *BAG16_OPERATIONS,
    }
    if not operation_set <= allowed:
        raise ValueError(f"registry contains unsupported operations: {sorted(operation_set - allowed)}")
    value: dict[str, Any] = {
        "schemaVersion": 2,
        "registryId": "0" * 64,
        "schemas": [entries[name] for name in sorted(entries)],
        "operations": [{"operationKind": kind, "operationVersion": version} for kind, version in sorted(operation_set)],
    }
    value["registryId"] = semantic_digest("k-in-k/replay-version-registry/v2", {name: item for name, item in value.items() if name != "registryId"})
    return value
