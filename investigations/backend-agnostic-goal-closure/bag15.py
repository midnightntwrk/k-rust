#!/usr/bin/env python3
"""Portable BAG-15 operation receipts and replay/result provenance.

This module constructs and verifies deterministic JSON only.  It does not
invoke K, a compiler, an executor, a solver, or a native adapter.
"""

from __future__ import annotations

import hashlib
import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any, Callable

from bag12 import OracleVerifier
from bag14 import CacheVerifier, canonical, digest, key, obj, array, typed_key, without


DIGEST_REF = {"$ref": "common.schema.json#/$defs/digest"}
ARTIFACT_REF = {"$ref": "common.schema.json#/$defs/artifactKey"}
OPERATIONS = {
    "mutation-materialization": "mutation-materialization-result",
    "execution-attempt": "execution-attempt-result",
    "oracle-operand-production": "oracle-operand-production-result",
    "baseline-admission": "baseline-admission-result",
    "oracle-comparison": "oracle-comparison-production-result",
    "campaign-derivation": "campaign-derivation-result",
    "report-publication": "report-publication-result",
}
RESULT_DOMAINS = {
    role: f"k-in-k/{role}/v1" for role in OPERATIONS.values()
}
NEW_ROLES = set(OPERATIONS.values()) | {
    "operation-receipt", "replay-version-registry", "provenance-mutation-report",
}
ADVERSARIES = (
    "patch-only-as-kill", "result-without-execution-receipt", "subject-reversal",
    "receipt-test-drift", "receipt-definition-drift", "pattern-query-drift",
    "final-result-without-attempt", "oracle-policy-drift", "full-missing-test",
    "first-kill-fabricated-suffix", "baseline-failure-mutant-child",
    "result-in-own-invocation", "role-digest-arity-drift", "transform-role-drift",
    "trace-other-invocation", "dangling-output", "missing-schema-version",
    "extra-schema-version", "incorrect-schema-digest", "refreshed-edge-drift",
    "output-receipt-cycle", "receipt-as-execution-invocation",
    "admission-as-comparison", "missing-admission-before-mutant",
    "complete-treated-as-normal", "campaign-layer-conflation", "digest-only-receipt",
    "cyclic-dag", "unavailable-input", "wrong-output-role", "wrong-output-arity",
    "surplus-child", "invalid-materialization-descendant", "cross-campaign-comparison",
    "missing-operation-version", "surplus-operation-version",
    "execution-key-invocation-conflation", "wrapper-terminal-drift",
    "failed-producer-with-output", "complete-failure-without-wrapper",
    "publication-expected-body-input", "report-self-publication-receipt",
)


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def raw_sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identify(value: dict[str, Any], field: str, domain: str) -> dict[str, Any]:
    value[field] = digest(domain, without(value, field))
    return value


def artifact_edge_schema(edge_roles: list[str], artifact_role: str | None = None) -> dict[str, Any]:
    return obj(
        ["edgeRole", "artifact"],
        {"edgeRole": {"enum": edge_roles}, "artifact": typed_key(artifact_role) if artifact_role else ARTIFACT_REF},
    )


def receipt_edge_schema(edge_roles: list[str]) -> dict[str, Any]:
    return obj(
        ["edgeRole", "receipt"],
        {"edgeRole": {"enum": edge_roles}, "receipt": typed_key("operation-receipt")},
    )


def fixed_array(items: list[dict[str, Any]]) -> dict[str, Any]:
    if not items:
        return {"type": "array", "maxItems": 0}
    return {"type": "array", "prefixItems": items, "items": False, "minItems": len(items), "maxItems": len(items)}


def adapter_schema() -> dict[str, Any]:
    return obj(
        ["adapterId", "adapterVersion"],
        {"adapterId": {"type": "string", "minLength": 1}, "adapterVersion": {"type": "integer", "minimum": 1}},
    )


def operation_parameters() -> dict[str, dict[str, Any]]:
    materialization = obj(
        ["baseline", "operator", "candidateId", "patch", "compatibilityProfile", "loweringProfile", "validationPolicyDigest"],
        {
            "baseline": typed_key("definition"), "operator": typed_key("mutation-operator"),
            "candidateId": DIGEST_REF, "patch": typed_key("patch"),
            "compatibilityProfile": typed_key("compatibility-profile"),
            "loweringProfile": typed_key("lowering-profile"), "validationPolicyDigest": DIGEST_REF,
        },
    )
    execution = obj(
        ["executionKey", "keyDigest"],
        {"executionKey": {"$ref": "cache-semantics.schema.json#/$defs/executionAttemptKey"}, "keyDigest": DIGEST_REF},
    )
    operand = obj(
        ["declaration", "side", "subject", "executionKeyDigest", "executionInvocationDigest", "projectionId", "evaluator"],
        {
            "declaration": typed_key("oracle-declaration"), "side": {"enum": ["baseline", "mutant"]},
            "subject": {"$ref": "oracle-semantics.schema.json#/$defs/operand/properties/subject"}, "executionKeyDigest": DIGEST_REF,
            "executionInvocationDigest": DIGEST_REF, "projectionId": {"type": "string", "minLength": 1},
            "evaluator": obj(["evaluatorId", "evaluatorVersion"], {"evaluatorId": {"type": "string", "minLength": 1}, "evaluatorVersion": {"type": "integer", "minimum": 1}}),
        },
    )
    admission = obj(
        ["evaluationKey", "keyDigest"],
        {"evaluationKey": {"$ref": "cache-semantics.schema.json#/$defs/oracleEvaluationKey"}, "keyDigest": DIGEST_REF},
    )
    comparison = deepcopy(admission)
    derivation = obj(
        ["campaignInvocation", "scheduleMode", "selectedPlan"],
        {
            "campaignInvocation": typed_key("cache-campaign-invocation"), "scheduleMode": {"enum": ["first-kill", "full"]},
            "selectedPlan": array(obj(["slotId", "record"], {"slotId": {"type": "string", "minLength": 1}, "record": typed_key("cache-record")})),
        },
    )
    publication = obj(
        ["derivationResult", "derivationReceipt", "versionRegistry", "reportRole", "reportVersion"],
        {
            "derivationResult": typed_key("campaign-derivation-result"),
            "derivationReceipt": typed_key("operation-receipt"),
            "versionRegistry": typed_key("replay-version-registry"),
            "reportRole": {"const": "provenance-mutation-report"}, "reportVersion": {"const": 1},
        },
    )
    return {
        "mutation-materialization": materialization, "execution-attempt": execution,
        "oracle-operand-production": operand, "baseline-admission": admission,
        "oracle-comparison": comparison, "campaign-derivation": derivation,
        "report-publication": publication,
    }


def invocation_arm(operation: str, parameters: dict[str, Any]) -> dict[str, Any]:
    fixed_inputs = {
        "mutation-materialization": [("baseline-definition", "definition"), ("mutation-operator", "mutation-operator"), ("patch", "patch"), ("compatibility-profile", "compatibility-profile"), ("lowering-profile", "lowering-profile")],
        "baseline-admission": [("declaration", "oracle-declaration"), ("baseline-operand", "oracle-operand-production-result"), ("baseline-execution-result", "execution-attempt-result")],
        "oracle-comparison": [("declaration", "oracle-declaration"), ("baseline-operand", "oracle-operand-production-result"), ("mutant-operand", "oracle-operand-production-result"), ("baseline-execution-result", "execution-attempt-result"), ("mutant-execution-result", "execution-attempt-result")],
        "report-publication": [("derivation-result", "campaign-derivation-result"), ("version-registry", "replay-version-registry")],
    }
    fixed_children = {
        "mutation-materialization": [], "execution-attempt": [],
        "oracle-operand-production": ["execution-production"],
        "baseline-admission": ["baseline-operand-production"],
        "oracle-comparison": ["baseline-operand-production", "mutant-operand-production"],
        "report-publication": ["derivation-production"],
    }
    if operation in fixed_inputs:
        inputs_schema = fixed_array([artifact_edge_schema([edge], role) for edge, role in fixed_inputs[operation]])
    elif operation == "execution-attempt":
        inputs_schema = array(artifact_edge_schema(["key-artifact"]), minimum=1)
    elif operation == "oracle-operand-production":
        ordinary = [("declaration", "oracle-declaration"), ("execution-result", "execution-attempt-result"), ("execution-terminal", None), ("producer-trace", "event-trace")]
        pattern = ordinary + [("pattern-replay", "replay-manifest"), ("pattern-result", "pattern-result")]
        inputs_schema = {"oneOf": [fixed_array([artifact_edge_schema([edge], role) for edge, role in arm]) for arm in (ordinary, pattern)]}
    else:
        inputs_schema = {
            "type": "array", "minItems": 2,
            "prefixItems": [artifact_edge_schema(["campaign-invocation"], "cache-campaign-invocation"), artifact_edge_schema(["materialization-result"], "mutation-materialization-result")],
            "items": {"oneOf": [artifact_edge_schema(["selected-cache-record"], "cache-record"), artifact_edge_schema(["selected-result"])]},
        }
    if operation == "campaign-derivation":
        children_schema = {"type": "array", "minItems": 1, "prefixItems": [receipt_edge_schema(["materialization-production"])], "items": receipt_edge_schema(["selected-record-production"])}
    else:
        children_schema = fixed_array([receipt_edge_schema([edge]) for edge in fixed_children[operation]])
    return obj(
        ["schemaVersion", "invocationDigest", "operationKind", "operationVersion", "adapterContract", "parameters", "inputs", "childReceipts", "outputRoles"],
        {
            "schemaVersion": {"const": 1}, "invocationDigest": DIGEST_REF,
            "operationKind": {"const": operation}, "operationVersion": {"const": 1},
            "adapterContract": adapter_schema(), "parameters": parameters,
            "inputs": inputs_schema,
            "childReceipts": children_schema,
            "outputRoles": {"type": "array", "prefixItems": [{"const": OPERATIONS[operation]}], "items": False, "minItems": 1, "maxItems": 1},
        },
    )


def receipt_schema() -> dict[str, Any]:
    invocations = {name: invocation_arm(name, parameters) for name, parameters in operation_parameters().items()}
    producer = obj(
        ["producerId", "producerVersion", "executionConformance"],
        {
            "producerId": {"type": "string", "minLength": 1}, "producerVersion": {"type": "integer", "minimum": 1},
            "executionConformance": {"enum": ["finite-vector-proven", "native-proven", "not-proven"]},
        },
    )
    failures = {
        "mutation-materialization": {"$ref": "common.schema.json#/$defs/mutantValidationFailure"},
        "execution-attempt": {"oneOf": [{"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}, {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}]},
        "oracle-operand-production": {"$ref": "common.schema.json#/$defs/oracleOperandProductionFailure"},
        "baseline-admission": {"$ref": "common.schema.json#/$defs/baselineOracleGateFailure"},
        "oracle-comparison": {"$ref": "common.schema.json#/$defs/oracleComparisonFailure"},
        "campaign-derivation": {"$ref": "common.schema.json#/$defs/campaignFailure"},
        "report-publication": {"$ref": "common.schema.json#/$defs/reportPublicationFailure"},
    }
    failed_failures = {
        "execution-attempt": {"oneOf": [
            {"allOf": [{"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}, {"type": "object", "required": ["stage"], "properties": {"stage": {"const": "infrastructure"}}}]},
            {"allOf": [{"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}, {"type": "object", "required": ["stage"], "properties": {"stage": {"const": "infrastructure"}}}]},
        ]},
        "campaign-derivation": {"allOf": [
            {"$ref": "common.schema.json#/$defs/campaignFailure"},
            {"type": "object", "required": ["stage", "classification"], "properties": {"stage": {"const": "infrastructure"}, "classification": {"const": "internal"}}},
        ]},
    }
    terminals = {
        "mutation-materialization": {"$ref": "mutation-materialization-result.schema.json#/properties/outcome"},
        "execution-attempt": {"$ref": "cache-semantics.schema.json#/$defs/executionTerminalRecord"},
        "oracle-operand-production": {"$ref": "oracle-operand-production-result.schema.json#/properties/outcome"},
        "baseline-admission": {"$ref": "baseline-admission-result.schema.json#/$defs/terminalRecord"},
        "oracle-comparison": {"$ref": "oracle-comparison-production-result.schema.json#/$defs/terminalRecord"},
        "campaign-derivation": {"$ref": "campaign-derivation-result.schema.json#/properties/outcome"},
        "report-publication": {"$ref": "report-publication-result.schema.json#/properties/outcome"},
    }
    arms = []
    required = ["schemaVersion", "receiptId", "invocationDigest", "invocation", "producer", "producerStatus", "outputs", "semanticTerminal", "failure"]
    for operation, invocation_schema in invocations.items():
        role = OPERATIONS[operation]
        common = {
            "schemaVersion": {"const": 1}, "receiptId": DIGEST_REF, "invocationDigest": DIGEST_REF,
            "invocation": invocation_schema, "producer": producer,
        }
        output = obj(["edgeRole", "artifact"], {"edgeRole": {"const": role}, "artifact": typed_key(role)})
        arms.append(obj(required, {
            **common, "producerStatus": {"const": "complete"}, "outputs": fixed_array([output]),
            "semanticTerminal": terminals[operation], "failure": {"oneOf": [failures[operation], {"type": "null"}]},
        }))
        if operation in failed_failures:
            arms.append(obj(required, {
                **common, "producerStatus": {"const": "failed"}, "outputs": fixed_array([]),
                "semanticTerminal": {"type": "null"}, "failure": failed_failures[operation],
            }))
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/operation-receipt.schema.json",
        "title": "Cycle-free portable operation invocation and receipt v1", "oneOf": arms,
    }


def execution_result_schema() -> dict[str, Any]:
    return obj(
        ["schemaVersion", "resultId", "keyDigest", "invocationDigest", "terminalRecord", "producedArtifacts"],
        {
            "schemaVersion": {"const": 1}, "resultId": DIGEST_REF, "keyDigest": DIGEST_REF,
            "invocationDigest": DIGEST_REF,
            "terminalRecord": {"$ref": "cache-semantics.schema.json#/$defs/executionTerminalRecord"},
            "producedArtifacts": array(ARTIFACT_REF, unique=True),
        },
    )


def oracle_result_schema(role: str, kind_value: str) -> dict[str, Any]:
    failure_name = "baselineOracleGateFailure" if kind_value == "baseline-gate" else "oracleComparisonFailure"
    common = {
        "schemaVersion": {"const": 1}, "resultId": DIGEST_REF, "invocationDigest": DIGEST_REF,
        "evaluationKey": {"$ref": "cache-semantics.schema.json#/$defs/oracleEvaluationKey"},
    }
    success = obj(list(common) + ["terminalRecord", "producedArtifacts", "failure"], {
        **common, "terminalRecord": obj(["kind", "result"], {"kind": {"const": kind_value}, "result": typed_key(role)}),
        "producedArtifacts": fixed_array([typed_key(role)]), "failure": {"type": "null"},
    })
    diagnostic = {"oneOf": [
        obj(["kind", "failure"], {"kind": {"const": "diagnostic-only"}, "failure": {"$ref": f"common.schema.json#/$defs/{failure_name}"}}),
        obj(["kind", "classification", "failure"], {"kind": {"const": "bounded-unknown"}, "classification": {"enum": ["time-limit", "depth-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown", "evaluator-unavailable"]}, "failure": {"$ref": f"common.schema.json#/$defs/{failure_name}"}}),
    ]}
    failure = obj(list(common) + ["terminalRecord", "producedArtifacts", "failure"], {
        **common, "terminalRecord": diagnostic, "producedArtifacts": fixed_array([]), "failure": {"$ref": f"common.schema.json#/$defs/{failure_name}"},
    })
    return {"$defs": {"terminalRecord": {"oneOf": [success["properties"]["terminalRecord"], diagnostic]}}, "oneOf": [success, failure]}


def outcome_wrapper_schema(role: str) -> dict[str, Any]:
    outcome_schemas: dict[str, dict[str, Any]] = {
        "mutation-materialization-result": {"oneOf": [
            obj(["kind", "mutantDefinition", "structuralDiff"], {"kind": {"const": "materialized"}, "mutantDefinition": typed_key("mutant-definition"), "structuralDiff": typed_key("structural-diff")}),
            obj(["kind", "failure"], {"kind": {"const": "invalid"}, "failure": {"$ref": "common.schema.json#/$defs/mutantValidationFailure"}}),
        ]},
        "oracle-operand-production-result": {"oneOf": [
            obj(["kind", "operand"], {"kind": {"const": "operand"}, "operand": typed_key("oracle-operand")}),
            obj(["kind", "failure"], {"kind": {"const": "failure"}, "failure": {"$ref": "common.schema.json#/$defs/oracleOperandProductionFailure"}}),
        ]},
        "campaign-derivation-result": {"oneOf": [obj(
            ["kind", "campaignInvocation", "scheduleMode", "selectedRecords", "testStatuses", "scheduledButUnexecuted", "exclusions", "score", "campaignStatus"],
            {
                "kind": {"const": "derived"}, "campaignInvocation": typed_key("cache-campaign-invocation"),
                "scheduleMode": {"enum": ["first-kill", "full"]},
                "selectedRecords": {"$ref": "cache-semantics.schema.json#/$defs/mutationReport/properties/selectedRecords"},
                "testStatuses": {"$ref": "cache-semantics.schema.json#/$defs/mutationReport/properties/testStatuses"},
                "scheduledButUnexecuted": {"$ref": "cache-semantics.schema.json#/$defs/mutationReport/properties/scheduledButUnexecuted"},
                "exclusions": {"$ref": "cache-semantics.schema.json#/$defs/mutationReport/properties/exclusions"},
                "score": {"$ref": "cache-semantics.schema.json#/$defs/mutationReport/properties/score"}, "campaignStatus": {"const": "complete"},
            },
        ), obj(["kind", "failure"], {"kind": {"const": "failure"}, "failure": {"$ref": "common.schema.json#/$defs/campaignFailure"}})]},
        "report-publication-result": {"oneOf": [
            obj(["kind", "report"], {"kind": {"const": "published"}, "report": typed_key("provenance-mutation-report")}),
            obj(["kind", "failure"], {"kind": {"const": "failure"}, "failure": {"$ref": "common.schema.json#/$defs/reportPublicationFailure"}}),
        ]},
    }
    failure_name = {
        "mutation-materialization-result": "mutantValidationFailure",
        "oracle-operand-production-result": "oracleOperandProductionFailure",
        "campaign-derivation-result": "campaignFailure",
        "report-publication-result": "reportPublicationFailure",
    }[role]
    return obj(
        ["schemaVersion", "resultId", "invocationDigest", "outcome", "failure"],
        {
            "schemaVersion": {"const": 1}, "resultId": DIGEST_REF, "invocationDigest": DIGEST_REF,
            "outcome": outcome_schemas[role],
            "failure": {"oneOf": [{"$ref": f"common.schema.json#/$defs/{failure_name}"}, {"type": "null"}]},
        },
    )


def wrapper_schema(role: str) -> dict[str, Any]:
    if role == "execution-attempt-result":
        body = execution_result_schema()
    elif role == "baseline-admission-result":
        body = oracle_result_schema("baseline-oracle-gate-result", "baseline-gate")
    elif role == "oracle-comparison-production-result":
        body = oracle_result_schema("oracle-comparison-result", "comparison")
    else:
        body = outcome_wrapper_schema(role)
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://starstream.dev/k-in-k/backend-agnostic/v1/{role}.schema.json",
        "title": f"Portable {role} v1", **body,
    }


def registry_schema() -> dict[str, Any]:
    schema_entry = obj(["schemaId", "schemaVersion", "schemaDigest"], {"schemaId": {"type": "string", "minLength": 1}, "schemaVersion": {"const": 1}, "schemaDigest": DIGEST_REF})
    operation_entry = obj(["operationKind", "operationVersion"], {"operationKind": {"enum": list(OPERATIONS)}, "operationVersion": {"const": 1}})
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema", "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/replay-version-registry.schema.json",
        "title": "Exact recursive portable replay version registry v1",
        **obj(["schemaVersion", "registryId", "schemas", "operations"], {"schemaVersion": {"const": 1}, "registryId": DIGEST_REF, "schemas": array(schema_entry, minimum=1, unique=True), "operations": array(operation_entry, minimum=1, unique=True)}),
    }


def report_schema() -> dict[str, Any]:
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema", "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/provenance-mutation-report.schema.json",
        "title": "Receipt-provenance mutation report v1",
        **obj(
            ["schemaVersion", "reportId", "derivationResult", "derivationReceipt", "versionRegistry", "outcome"],
            {
                "schemaVersion": {"const": 1}, "reportId": DIGEST_REF,
                "derivationResult": typed_key("campaign-derivation-result"), "derivationReceipt": typed_key("operation-receipt"),
                "versionRegistry": typed_key("replay-version-registry"), "outcome": outcome_wrapper_schema("campaign-derivation-result")["properties"]["outcome"],
            },
        ),
    }


def role_specs() -> dict[str, dict[str, Any]]:
    specs = {}
    for role in OPERATIONS.values():
        specs[role] = {
            "role": role, "contentModel": "canonical-json", "mediaType": "application/json",
            "schema": f"{role}.schema.json", "digestDomain": RESULT_DOMAINS[role],
            "projection": {"kind": "without-field"}, "selfIdField": "resultId",
        }
    specs.update({
        "operation-receipt": {"role": "operation-receipt", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "operation-receipt.schema.json", "digestDomain": "k-in-k/operation-receipt/v1", "projection": {"kind": "without-field"}, "selfIdField": "receiptId"},
        "replay-version-registry": {"role": "replay-version-registry", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "replay-version-registry.schema.json", "digestDomain": "k-in-k/replay-version-registry/v1", "projection": {"kind": "without-field"}, "selfIdField": "registryId"},
        "provenance-mutation-report": {"role": "provenance-mutation-report", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "provenance-mutation-report.schema.json", "digestDomain": "k-in-k/provenance-mutation-report/v1", "projection": {"kind": "without-field"}, "selfIdField": "reportId"},
    })
    return specs


def install_schemas_and_roles(root: Path) -> None:
    schemas = root / "schemas"
    write_json(schemas / "operation-receipt.schema.json", receipt_schema())
    for role in OPERATIONS.values():
        write_json(schemas / f"{role}.schema.json", wrapper_schema(role))
    write_json(schemas / "replay-version-registry.schema.json", registry_schema())
    write_json(schemas / "provenance-mutation-report.schema.json", report_schema())
    common_path = schemas / "common.schema.json"
    common = read_json(common_path)
    common["$defs"]["artifactRole"]["enum"] = sorted(set(common["$defs"]["artifactRole"]["enum"]) | NEW_ROLES)
    write_json(common_path, common)
    specs_path = root / "artifact-role-specs.json"
    value = read_json(specs_path)
    by_role = {item["role"]: item for item in value["specs"]}
    by_role.update(role_specs())
    value["specs"] = [by_role[role] for role in sorted(by_role)]
    write_json(specs_path, value)


def artifact_keys(value: Any) -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    if isinstance(value, dict):
        if set(value) == {"role", "digest"} and isinstance(value.get("role"), str):
            result.append(deepcopy(value))
        else:
            for name in sorted(value):
                result.extend(artifact_keys(value[name]))
    elif isinstance(value, list):
        for item in value:
            result.extend(artifact_keys(item))
    return result


def unique_artifacts(values: list[dict[str, str]]) -> list[dict[str, str]]:
    seen: set[tuple[str, str]] = set()
    result = []
    for item in values:
        identity = (item["role"], item["digest"])
        if identity not in seen:
            seen.add(identity)
            result.append(deepcopy(item))
    return result


def json_pointer(document: Any, fragment: str) -> Any:
    current = document
    if fragment in {"", "#"}:
        return current
    if not fragment.startswith("#/"):
        raise AssertionError(f"BAG-15 unsupported schema fragment {fragment}")
    for token in fragment[2:].split("/"):
        token = token.replace("~1", "/").replace("~0", "~")
        current = current[int(token)] if isinstance(current, list) else current[token]
    return current


def derive_version_claim(
    root: Path,
    assets: dict[tuple[str, str], Any],
    receipt_ids: set[str],
    seed_keys: list[dict[str, str]],
    *,
    planned_roles: set[str] | None = None,
    planned_operations: set[tuple[str, int]] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Derive portable schema/operation versions from a typed artifact closure."""
    specifications = read_json(root / "artifact-role-specs.json")["specs"]
    by_role = {item["role"]: item for item in specifications}
    if len(by_role) != len(specifications):
        raise AssertionError("BAG-15 artifact role specifications duplicate a role")
    roles = set(planned_roles or set())
    pending = list(seed_keys)
    visited: set[tuple[str, str]] = set()
    while pending:
        artifact = pending.pop()
        identity = (artifact["role"], artifact["digest"])
        roles.add(artifact["role"])
        if identity in visited:
            continue
        visited.add(identity)
        value = assets.get(identity)
        if value is None:
            continue
        if artifact["role"] == "operation-receipt" and artifact["digest"] not in receipt_ids:
            raise AssertionError("BAG-15 reachable receipt escaped exact publication closure")
        pending.extend(artifact_keys(value))

    schema_documents = {path.name: read_json(path) for path in (root / "schemas").glob("*.schema.json")}
    id_to_name: dict[str, str] = {}
    versions: dict[str, int] = {}
    for name, document in schema_documents.items():
        schema_id = document.get("$id")
        match = re.fullmatch(r"https://starstream\.dev/k-in-k/backend-agnostic/v([0-9]+)/([^/]+\.schema\.json)", schema_id or "")
        if match is None or match.group(2) != name or schema_id in id_to_name:
            raise AssertionError(f"BAG-15 schema has noncanonical/duplicate identity: {name}")
        id_to_name[schema_id] = name
        versions[name] = int(match.group(1))

    pending_schemas = [by_role[role]["schema"] for role in roles if role in by_role and by_role[role]["schema"] is not None]
    reached_documents: set[str] = set()
    visited_locations: set[tuple[str, str]] = set()
    while pending_schemas:
        reference = pending_schemas.pop()
        name, separator, tail = reference.partition("#")
        fragment = f"#{tail}" if separator else ""
        if name not in schema_documents:
            raise AssertionError(f"BAG-15 typed role references unknown schema {name}")
        location = (name, fragment)
        if location in visited_locations:
            continue
        visited_locations.add(location)
        reached_documents.add(name)
        node = json_pointer(schema_documents[name], fragment)

        def walk(value: Any, current_name: str) -> None:
            if isinstance(value, dict):
                target = value.get("$ref")
                if isinstance(target, str):
                    target_name, target_separator, target_tail = target.partition("#")
                    target_name = target_name or current_name
                    if "://" in target_name or "/" in target_name or target_name not in schema_documents:
                        raise AssertionError(f"BAG-15 schema reference is not a bundled canonical filename: {target}")
                    pending_schemas.append(target_name + (f"#{target_tail}" if target_separator else ""))
                for key_name, child in value.items():
                    if key_name not in {"$ref", "$defs", "definitions"}:
                        walk(child, current_name)
            elif isinstance(value, list):
                for child in value:
                    walk(child, current_name)

        walk(node, name)

    schema_entries = [
        {"schemaId": name, "schemaVersion": versions[name], "schemaDigest": raw_sha256((root / "schemas" / name).read_bytes())}
        for name in sorted(reached_documents)
    ]
    operation_tuples = set(planned_operations or set())
    for receipt_id in receipt_ids:
        receipt_value = assets[("operation-receipt", receipt_id)]
        operation_tuples.add((receipt_value["invocation"]["operationKind"], receipt_value["invocation"]["operationVersion"]))
    operation_entries = [{"operationKind": kind, "operationVersion": version} for kind, version in sorted(operation_tuples)]
    return schema_entries, operation_entries


def invocation(operation: str, parameters: dict[str, Any], inputs: list[tuple[str, dict[str, str]]], children: list[tuple[str, dict[str, str]]]) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "invocationDigest": "0" * 64, "operationKind": operation, "operationVersion": 1,
        "adapterContract": {"adapterId": "bag15-portable-finite", "adapterVersion": 1},
        "parameters": deepcopy(parameters),
        "inputs": [{"edgeRole": edge, "artifact": deepcopy(item)} for edge, item in inputs],
        "childReceipts": [{"edgeRole": edge, "receipt": deepcopy(item)} for edge, item in children],
        "outputRoles": [OPERATIONS[operation]],
    }
    value["invocationDigest"] = digest("k-in-k/operation-invocation/v1", without(value, "invocationDigest"))
    return value


def wrapper(role: str, invocation_digest: str, payload: dict[str, Any]) -> dict[str, Any]:
    value = {"schemaVersion": 1, "resultId": "0" * 64, "invocationDigest": invocation_digest, **deepcopy(payload)}
    value["resultId"] = digest(RESULT_DOMAINS[role], without(value, "resultId"))
    return value


def selected_failure(terminal: Any) -> dict[str, Any] | None:
    if isinstance(terminal, dict):
        if isinstance(terminal.get("failure"), dict):
            return deepcopy(terminal["failure"])
        outcome = terminal.get("outcome")
        if isinstance(outcome, dict) and isinstance(outcome.get("failure"), dict):
            return deepcopy(outcome["failure"])
    return None


def receipt(inv: dict[str, Any], result_key: dict[str, str], terminal: Any, *, conformance: str = "finite-vector-proven") -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "receiptId": "0" * 64, "invocationDigest": inv["invocationDigest"], "invocation": deepcopy(inv),
        "producer": {"producerId": "bag15-deterministic-python", "producerVersion": 1, "executionConformance": conformance},
        "producerStatus": "complete", "outputs": [{"edgeRole": inv["outputRoles"][0], "artifact": deepcopy(result_key)}],
        "semanticTerminal": deepcopy(terminal), "failure": selected_failure(terminal),
    }
    value["receiptId"] = digest("k-in-k/operation-receipt/v1", without(value, "receiptId"))
    return value


def failed_receipt(inv: dict[str, Any], failure: dict[str, Any]) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "receiptId": "0" * 64, "invocationDigest": inv["invocationDigest"], "invocation": deepcopy(inv),
        "producer": {"producerId": "bag15-unavailable-producer", "producerVersion": 1, "executionConformance": "not-proven"},
        "producerStatus": "failed", "outputs": [], "semanticTerminal": None, "failure": deepcopy(failure),
    }
    value["receiptId"] = digest("k-in-k/operation-receipt/v1", without(value, "receiptId"))
    return value


def structured_entry(root: Path, role: str, identity: str, value: Any, name: str) -> dict[str, Any]:
    data = canonical(value).encode("utf-8")
    (root / "material" / name).write_bytes(data)
    return {
        "role": role, "digest": identity, "contentModel": "canonical-json", "mediaType": "application/json",
        "contentSha256": raw_sha256(data), "availability": "bundled",
        "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{name}", "resolverId": "repo-v1",
    }


def derive_structural_diff(baseline: dict[str, Any], mutant: dict[str, Any], patch: dict[str, Any]) -> dict[str, Any]:
    baseline_by_lineage = {sentence["provenance"]["lineageId"]: sentence for module in baseline["modules"] for sentence in module["sentences"]}
    mutant_by_lineage = {sentence["provenance"]["lineageId"]: sentence for module in mutant["modules"] for sentence in module["sentences"]}
    entries = []
    for edit in patch["edits"]:
        before = baseline_by_lineage[edit["targetLineage"]]
        after = mutant_by_lineage[edit["targetLineage"]]
        entries.append({
            "editId": edit["editId"], "operation": edit["operation"], "targetLineage": edit["targetLineage"],
            "targetPath": deepcopy(edit["targetPath"]), "beforeFingerprint": before["provenance"]["contentFingerprint"],
            "afterFingerprint": after["provenance"]["contentFingerprint"], "affectedProvenance": deepcopy(after["provenance"]),
        })
    return identify({
        "schemaVersion": 1, "diffId": "0" * 64, "baselineDefinitionDigest": baseline["definitionDigest"],
        "mutantDefinitionDigest": mutant["definitionDigest"], "portableApplication": "applied-and-locally-well-formed",
        "nativeIrValidation": "rust-proof-pending", "entries": entries,
    }, "diffId", "k-in-k/structural-diff/v1")


def semantic_terminal_for_wrapper(role: str, result: dict[str, Any]) -> Any:
    return deepcopy(result["terminalRecord"] if role in {"execution-attempt-result", "baseline-admission-result", "oracle-comparison-production-result"} else result["outcome"])


def make_result_and_receipt(operation: str, inv: dict[str, Any], payload: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    role = OPERATIONS[operation]
    result = wrapper(role, inv["invocationDigest"], payload)
    result_key = key(role, result["resultId"])
    return result, receipt(inv, result_key, semantic_terminal_for_wrapper(role, result))


def replay_invocation_payload(value: dict[str, Any]) -> dict[str, Any]:
    payload = without(value, "replayId", "invocationDigest", "expectedResultDigest")
    payload["steps"] = [{name: deepcopy(item) for name, item in step.items() if name != "expectedArtifacts"} for step in value["steps"]]
    return payload


def install_legacy_materialization_name(root: Path) -> None:
    schema_path = root / "schemas" / "replay-manifest.schema.json"
    schema = read_json(schema_path)
    def replace(value: Any) -> None:
        if isinstance(value, dict):
            for name, item in value.items():
                if name in {"const"} and item == "mutation-instance":
                    value[name] = "mutation-materialization"
                else:
                    replace(item)
        elif isinstance(value, list):
            for index, item in enumerate(value):
                if item == "mutation-instance":
                    value[index] = "mutation-materialization"
                else:
                    replace(item)
    replace(schema)
    write_json(schema_path, schema)
    fixture = root / "fixtures" / "mutation-replay-manifest.json"
    replay = read_json(fixture)
    replay["kind"] = "mutation-materialization"
    replay["invocationDigest"] = digest("k-in-k/replay-invocation/v1", replay_invocation_payload(replay))
    replay["replayId"] = digest("k-in-k/replay-manifest/v1", without(replay, "replayId"))
    write_json(fixture, replay)


def finalize_refresh(root: Path) -> None:
    """Publish the deterministic BAG-15 derivative receipt graph."""
    install_schemas_and_roles(root)
    install_legacy_materialization_name(root)
    fixtures = root / "fixtures"
    bag14_catalog = read_json(fixtures / "bag14-cache-artifact-catalog.json")
    base_entries = {(item["role"], item["digest"]): deepcopy(item) for item in bag14_catalog["entries"]}
    base_assets: dict[tuple[str, str], Any] = {}
    for identity, entry in base_entries.items():
        if entry["contentModel"] == "canonical-json":
            base_assets[identity] = json.loads((root.parents[1] / entry["logicalPath"].removeprefix("repo://")).read_text(encoding="utf-8"))

    manifest = next(value for (role, _), value in base_assets.items() if role == "cache-campaign-manifest")
    operator_key, operator = next((key(role, identity), value) for (role, identity), value in base_assets.items() if role == "mutation-operator")
    baseline = base_assets[(manifest["baselineDefinition"]["role"], manifest["baselineDefinition"]["digest"])]
    mutant = base_assets[(manifest["candidate"]["mutantDefinition"]["role"], manifest["candidate"]["mutantDefinition"]["digest"])]
    patch = base_assets[(manifest["candidate"]["patch"]["role"], manifest["candidate"]["patch"]["digest"])]
    diff = derive_structural_diff(baseline, mutant, patch)

    new_assets: dict[tuple[str, str], tuple[dict[str, Any], str]] = {}
    receipts: list[dict[str, Any]] = []
    def add(role: str, value: dict[str, Any], name: str, identity: str | None = None) -> dict[str, str]:
        self_field = role_specs().get(role, {}).get("selfIdField") or {
            "cache-record": "recordId", "structural-diff": "diffId",
        }.get(role)
        if identity is None and self_field is None:
            raise AssertionError(f"BAG-15 add lacks identity field for {role}")
        identity = identity or value[self_field]
        new_assets[(role, identity)] = (deepcopy(value), name)
        return key(role, identity)
    def add_receipt(value: dict[str, Any], name: str) -> dict[str, str]:
        receipts.append(value)
        return add("operation-receipt", value, name)

    active_catalog = read_json(fixtures / "artifact-catalog.json")
    active_entries = {(item["role"], item["digest"]): deepcopy(item) for item in active_catalog["entries"]}
    pattern_declaration_value = read_json(fixtures / "oracle-declaration-execution-pattern-pattern-outcome-distinguish.json")
    pattern_comparison_value = read_json(fixtures / "oracle-comparison-execution-pattern-pattern-outcome-distinguish.json")
    pattern_operand_values = {
        side: read_json(fixtures / f"oracle-operand-execution-pattern-pattern-outcome-distinguish-{side}.json")
        for side in ("baseline", "mutant")
    }
    pattern_replays = {side: read_json(fixtures / f"bag12-{side}-pattern-replay.json") for side in ("baseline", "mutant")}
    pattern_results = {side: read_json(fixtures / f"bag12-{side}-pattern-result.json") for side in ("baseline", "mutant")}
    pattern_gate_value = read_json(fixtures / "baseline-oracle-gate-execution-pattern-pattern-outcome-distinguish.json")
    pattern_seed_keys = [
        key("oracle-declaration", pattern_declaration_value["declarationId"]),
        key("oracle-comparison-result", pattern_comparison_value["comparisonId"]),
        key("baseline-oracle-gate-result", pattern_gate_value["gateResultId"]),
        *[key("oracle-operand", value["operandId"]) for value in pattern_operand_values.values()],
        *[key("replay-manifest", value["replayId"]) for value in pattern_replays.values()],
        *[key("pattern-result", value["resultId"]) for value in pattern_results.values()],
        *[key("observation-manifest", value["observationManifestDigest"]) for value in pattern_replays.values()],
    ]
    pending_pattern = list(pattern_seed_keys)
    imported_pattern: set[tuple[str, str]] = set()
    while pending_pattern:
        artifact = pending_pattern.pop()
        identity = (artifact["role"], artifact["digest"])
        if identity in imported_pattern:
            continue
        imported_pattern.add(identity)
        entry = active_entries.get(identity)
        if entry is None or entry["availability"] != "bundled":
            continue
        path = root.parents[1] / entry["logicalPath"].removeprefix("repo://")
        base_entries[identity] = entry
        if entry["contentModel"] == "canonical-json":
            imported = json.loads(path.read_text(encoding="utf-8"))
            base_assets[identity] = imported
            pending_pattern.extend(artifact_keys(imported))

    from refresh_fixture_ids import materialize_mutant_definition
    active_baseline = read_json(fixtures / "semantic-definition-memory.json")
    active_campaign = read_json(fixtures / "mutation-campaign.json")
    active_patch = active_campaign["generation"]["candidates"][0]["patch"]
    active_mutant = materialize_mutant_definition(active_baseline, active_patch)
    active_operator = read_json(fixtures / "mutation-operator.json")
    active_compatibility = {"profile": deepcopy(active_baseline["family"]["compatibilityProfile"])}
    pattern_baseline_key = add("definition", active_baseline, "bag15-pattern-baseline-definition.json", active_baseline["definitionDigest"])
    pattern_mutant_key = add("mutant-definition", active_mutant, "bag15-pattern-mutant-definition.json", active_mutant["definitionDigest"])
    pattern_operator_key = add("mutation-operator", active_operator, "bag15-pattern-mutation-operator.json", active_operator["operatorDigest"])
    pattern_patch_key = add("patch", active_patch, "bag15-pattern-patch.json", active_patch["patchId"])
    add("compatibility-profile", active_compatibility, "bag15-pattern-compatibility-profile.json", pattern_declaration_value["compatibilityProfileDigest"])
    for role, profile_digest in (
        ("lowering-profile", "6d07d5437a05b5bda922083438b7d4c5ee448bbbea5955ee4a49e97582eafefd"),
        ("execution-profile", pattern_declaration_value["executionProfileDigest"]),
        ("solver-profile", pattern_declaration_value["solverProfileDigest"]),
    ):
        profile_entry = active_entries[(role, profile_digest)]
        base_entries[(role, profile_digest)] = deepcopy(profile_entry)

    diff_key = add("structural-diff", diff, "bag15-structural-diff.json")
    materialization_parameters = {
        "baseline": deepcopy(manifest["baselineDefinition"]), "operator": operator_key,
        "candidateId": manifest["candidate"]["candidateId"], "patch": deepcopy(manifest["candidate"]["patch"]),
        "compatibilityProfile": deepcopy(manifest["compatibilityProfile"]), "loweringProfile": deepcopy(manifest["loweringProfile"]),
        "validationPolicyDigest": digest("k-in-k/materialization-validation-policy/v1", {"mode": "portable-local-well-formedness"}),
    }
    materialization_invocation = invocation("mutation-materialization", materialization_parameters, [
        ("baseline-definition", manifest["baselineDefinition"]), ("mutation-operator", operator_key),
        ("patch", manifest["candidate"]["patch"]), ("compatibility-profile", manifest["compatibilityProfile"]),
        ("lowering-profile", manifest["loweringProfile"]),
    ], [])
    materialization_result, materialization_receipt = make_result_and_receipt("mutation-materialization", materialization_invocation, {
        "outcome": {"kind": "materialized", "mutantDefinition": deepcopy(manifest["candidate"]["mutantDefinition"]), "structuralDiff": diff_key}, "failure": None,
    })
    materialization_result_key = add("mutation-materialization-result", materialization_result, "bag15-materialization-result.json")
    materialization_receipt_key = add_receipt(materialization_receipt, "bag15-receipt-materialization.json")

    invalid_invocation = deepcopy(materialization_invocation)
    invalid_invocation["parameters"]["validationPolicyDigest"] = digest("k-in-k/materialization-validation-policy/v1", {"mode": "reject-invalid-lowering"})
    invalid_invocation["invocationDigest"] = digest("k-in-k/operation-invocation/v1", without(invalid_invocation, "invocationDigest"))
    invalid_failure = {"stage": "ir-validation", "classification": "invalid-module", "context": "mutant-validation", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
    invalid_result, invalid_receipt = make_result_and_receipt("mutation-materialization", invalid_invocation, {"outcome": {"kind": "invalid", "failure": invalid_failure}, "failure": invalid_failure})
    invalid_result_key = add("mutation-materialization-result", invalid_result, "bag15-materialization-invalid-result.json")
    invalid_receipt_key = add_receipt(invalid_receipt, "bag15-receipt-materialization-invalid.json")

    bag14_records = {identity: value for (role, identity), value in base_assets.items() if role == "cache-record"}
    execution_by_key: dict[str, tuple[dict[str, Any], dict[str, Any], dict[str, str], dict[str, str]]] = {}
    derivative_records: dict[str, dict[str, Any]] = {}
    record_receipts: dict[str, dict[str, str]] = {}
    for record_id, record in bag14_records.items():
        if record["kind"] != "execution-attempt":
            continue
        execution_inputs = [("key-artifact", item) for item in unique_artifacts(artifact_keys(record["key"]))]
        inv = invocation("execution-attempt", {"executionKey": deepcopy(record["key"]), "keyDigest": record["keyDigest"]}, execution_inputs, [])
        result, production_receipt = make_result_and_receipt("execution-attempt", inv, {
            "keyDigest": record["keyDigest"], "terminalRecord": deepcopy(record["terminalRecord"]), "producedArtifacts": deepcopy(record["producedArtifacts"]),
        })
        result_key = add("execution-attempt-result", result, f"bag15-execution-result-{record_id}.json")
        receipt_key = add_receipt(production_receipt, f"bag15-receipt-execution-{record_id}.json")
        derivative = deepcopy(record)
        derivative["productionEvidence"] = {"mode": "operation-receipt", "receipt": receipt_key, "result": result_key}
        derivative["recordId"] = digest("k-in-k/cache-record/v1", without(derivative, "recordId"))
        derivative_key = add("cache-record", derivative, f"bag15-cache-record-{record_id}.json")
        derivative_records[record_id] = derivative
        record_receipts[record_id] = receipt_key
        execution_by_key[record["keyDigest"]] = (result, production_receipt, result_key, receipt_key)

    failed_source = next(record for record in bag14_records.values() if record["kind"] == "execution-attempt" and record["terminalRecord"]["kind"] == "diagnostic-only")
    failed_invocation = invocation("execution-attempt", {"executionKey": deepcopy(failed_source["key"]), "keyDigest": failed_source["keyDigest"]}, [("key-artifact", item) for item in unique_artifacts(artifact_keys(failed_source["key"]))], [])
    producer_failure = {"stage": "infrastructure", "classification": "worker-lost", "context": "mutant-execution", "scope": "mutant", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}
    failed_producer_key = add_receipt(failed_receipt(failed_invocation, producer_failure), "bag15-receipt-failed-producer.json")

    operands = [(identity, value) for (role, identity), value in base_assets.items() if role == "oracle-operand"]
    operand_receipts: dict[str, dict[str, str]] = {}
    operand_results: dict[str, dict[str, str]] = {}
    for operand_id, operand in operands:
        if operand["completionEvidence"]["kind"] == "pattern-result":
            continue
        trace_key = operand["completionEvidence"]["producerTrace"]
        terminal_key = operand["completionEvidence"]["terminal"]["artifact"]
        side = operand["subject"]["side"]
        candidates = [item for item in bag14_records.values() if item["kind"] == "execution-attempt" and item["key"]["subject"]["kind"] == side and trace_key in item["producedArtifacts"]]
        if side == "mutant":
            candidates = [item for item in bag14_records.values() if item["kind"] == "execution-attempt" and item["key"]["subject"]["kind"] == "mutant" and trace_key in item["producedArtifacts"]]
        execution_record = candidates[0]
        execution_result, _, execution_result_key, execution_receipt_key = execution_by_key[execution_record["keyDigest"]]
        declaration = base_assets[(operand["declaration"]["role"], operand["declaration"]["digest"])]
        inv = invocation("oracle-operand-production", {
            "declaration": deepcopy(operand["declaration"]), "side": side, "subject": deepcopy(operand["subject"]),
            "executionKeyDigest": execution_record["keyDigest"], "executionInvocationDigest": execution_result["invocationDigest"],
            "projectionId": declaration["projectionSpec"]["projectionId"], "evaluator": {"evaluatorId": "bag12-portable-exit-stop", "evaluatorVersion": 1},
        }, [
            ("declaration", operand["declaration"]), ("execution-result", execution_result_key),
            ("execution-terminal", terminal_key), ("producer-trace", trace_key),
        ], [("execution-production", execution_receipt_key)])
        result, production_receipt = make_result_and_receipt("oracle-operand-production", inv, {"outcome": {"kind": "operand", "operand": key("oracle-operand", operand_id)}, "failure": None})
        result_key = add("oracle-operand-production-result", result, f"bag15-operand-result-{operand_id}.json")
        receipt_key = add_receipt(production_receipt, f"bag15-receipt-operand-{operand_id}.json")
        operand_receipts[operand_id] = receipt_key
        operand_results[operand_id] = result_key

    for record_id, record in bag14_records.items():
        if record["kind"] != "oracle-evaluation":
            continue
        comparison = record["key"]["evaluationKind"] == "baseline-mutant-comparison"
        operation = "oracle-comparison" if comparison else "baseline-admission"
        result_role = "oracle-comparison-production-result" if comparison else "baseline-admission-result"
        by_side: dict[str, tuple[dict[str, str], dict[str, str], dict[str, str]]] = {}
        for semantic in record["key"]["semanticInputs"]:
            operand_key = semantic["value"]
            operand = base_assets[(operand_key["role"], operand_key["digest"])]
            trace_key = operand["completionEvidence"]["producerTrace"]
            execution_record = next(item for item in bag14_records.values() if item["kind"] == "execution-attempt" and trace_key in item["producedArtifacts"])
            by_side[semantic["side"]] = (operand_results[operand_key["digest"]], operand_receipts[operand_key["digest"]], execution_by_key[execution_record["keyDigest"]][2])
        inputs = [("declaration", record["key"]["declaration"])]
        inputs.extend((f"{side}-operand", by_side[side][0]) for side in (["baseline", "mutant"] if comparison else ["baseline"]))
        inputs.extend((f"{side}-execution-result", by_side[side][2]) for side in (["baseline", "mutant"] if comparison else ["baseline"]))
        children = [(f"{side}-operand-production", by_side[side][1]) for side in (["baseline", "mutant"] if comparison else ["baseline"])]
        inv = invocation(operation, {"evaluationKey": deepcopy(record["key"]), "keyDigest": record["keyDigest"]}, inputs, children)
        result, production_receipt = make_result_and_receipt(operation, inv, {
            "evaluationKey": deepcopy(record["key"]), "terminalRecord": deepcopy(record["terminalRecord"]), "producedArtifacts": deepcopy(record["producedArtifacts"]),
            "failure": selected_failure(record["terminalRecord"]),
        })
        result_key = add(result_role, result, f"bag15-{result_role}-{record_id}.json")
        receipt_key = add_receipt(production_receipt, f"bag15-receipt-{operation}-{record_id}.json")
        derivative = deepcopy(record)
        derivative["productionEvidence"] = {"mode": "operation-receipt", "receipt": receipt_key, "result": result_key}
        derivative["recordId"] = digest("k-in-k/cache-record/v1", without(derivative, "recordId"))
        add("cache-record", derivative, f"bag15-cache-record-{record_id}.json")
        derivative_records[record_id] = derivative
        record_receipts[record_id] = receipt_key

    pattern_execution: dict[str, tuple[dict[str, str], dict[str, str]]] = {}
    pattern_operand_production: dict[str, tuple[dict[str, str], dict[str, str]]] = {}
    pattern_candidate = active_campaign["generation"]["candidates"][0]
    pattern_mutant = active_campaign["mutants"][0]
    query_regression_key = read_json(root / "vectors" / "cache-semantics-vectors.json")["queryCoupledRegression"]["executionKey"]
    for side in ("baseline", "mutant"):
        subject = {"kind": "baseline", "definition": pattern_baseline_key} if side == "baseline" else {
            "kind": "mutant", "baselineDefinition": pattern_baseline_key, "candidateId": pattern_candidate["candidateId"],
            "operator": pattern_operator_key, "patch": pattern_patch_key, "mutantId": pattern_mutant["mutantId"],
            "mutantDefinition": pattern_mutant_key,
        }
        execution_key_value = deepcopy(query_regression_key)
        execution_key_value["subject"] = subject
        execution_key_value["attemptKind"]["observationInputs"] = [key("observation-manifest", pattern_replays[side]["observationManifestDigest"])]
        execution_key_value["keyDigest"] = digest("k-in-k/execution-attempt-key/v1", without(execution_key_value, "keyDigest"))
        execution_invocation = invocation(
            "execution-attempt", {"executionKey": execution_key_value, "keyDigest": execution_key_value["keyDigest"]},
            [("key-artifact", item) for item in unique_artifacts(artifact_keys(execution_key_value))], [],
        )
        pattern_result_key = key("pattern-result", pattern_results[side]["resultId"])
        path_result = pattern_results[side]["pathResults"][0]
        terminal_key = path_result["executionTerminal"]["artifact"]
        trace_key = key("event-trace", path_result["traceDigest"])
        execution_result, execution_receipt = make_result_and_receipt("execution-attempt", execution_invocation, {
            "keyDigest": execution_key_value["keyDigest"], "terminalRecord": {"kind": path_result["executionTerminal"]["kind"], "terminal": terminal_key},
            "producedArtifacts": [terminal_key, trace_key],
        })
        execution_result_key = add("execution-attempt-result", execution_result, f"bag15-pattern-execution-result-{side}.json")
        execution_receipt_key = add_receipt(execution_receipt, f"bag15-receipt-pattern-execution-{side}.json")
        pattern_execution[side] = (execution_result_key, execution_receipt_key)

        operand = pattern_operand_values[side]
        replay_key = key("replay-manifest", pattern_replays[side]["replayId"])
        operand_invocation = invocation("oracle-operand-production", {
            "declaration": key("oracle-declaration", pattern_declaration_value["declarationId"]), "side": side,
            "subject": deepcopy(operand["subject"]), "executionKeyDigest": execution_key_value["keyDigest"],
            "executionInvocationDigest": execution_result["invocationDigest"], "projectionId": pattern_declaration_value["projectionSpec"]["projectionId"],
            "evaluator": {"evaluatorId": "bag12-portable-execution-pattern", "evaluatorVersion": 1},
        }, [
            ("declaration", key("oracle-declaration", pattern_declaration_value["declarationId"])),
            ("execution-result", execution_result_key), ("execution-terminal", terminal_key), ("producer-trace", trace_key),
            ("pattern-replay", replay_key), ("pattern-result", pattern_result_key),
        ], [("execution-production", execution_receipt_key)])
        operand_result, operand_receipt = make_result_and_receipt("oracle-operand-production", operand_invocation, {
            "outcome": {"kind": "operand", "operand": key("oracle-operand", operand["operandId"])}, "failure": None,
        })
        operand_result_key = add("oracle-operand-production-result", operand_result, f"bag15-pattern-operand-result-{side}.json")
        operand_receipt_key = add_receipt(operand_receipt, f"bag15-receipt-pattern-operand-{side}.json")
        pattern_operand_production[side] = (operand_result_key, operand_receipt_key)

    def pattern_evaluation_key(kind_name: str) -> dict[str, Any]:
        sides = ["baseline"] if kind_name == "baseline-admission" else ["baseline", "mutant"]
        value = {
            "schemaVersion": 1, "keyDigest": "0" * 64,
            "operation": {"operationId": "portable-oracle-evaluation", "operationVersion": 1, "adapterId": "bag15-portable-finite", "adapterVersion": 1},
            "evaluationKind": kind_name,
            "declaration": key("oracle-declaration", pattern_declaration_value["declarationId"]),
            "semanticInputs": [{"side": side, "value": key("oracle-operand", pattern_operand_values[side]["operandId"])} for side in sides],
            "evaluator": {"evaluatorId": "bag12-portable-execution-pattern", "evaluatorVersion": 1, "mode": "built-in"},
        }
        value["keyDigest"] = digest("k-in-k/oracle-evaluation-key/v1", without(value, "keyDigest"))
        return value

    pattern_admission_key = pattern_evaluation_key("baseline-admission")
    pattern_admission_invocation = invocation("baseline-admission", {"evaluationKey": pattern_admission_key, "keyDigest": pattern_admission_key["keyDigest"]}, [
        ("declaration", pattern_admission_key["declaration"]), ("baseline-operand", pattern_operand_production["baseline"][0]),
        ("baseline-execution-result", pattern_execution["baseline"][0]),
    ], [("baseline-operand-production", pattern_operand_production["baseline"][1])])
    pattern_admission_result, pattern_admission_receipt = make_result_and_receipt("baseline-admission", pattern_admission_invocation, {
        "evaluationKey": pattern_admission_key, "terminalRecord": {"kind": "baseline-gate", "result": key("baseline-oracle-gate-result", pattern_gate_value["gateResultId"])},
        "producedArtifacts": [key("baseline-oracle-gate-result", pattern_gate_value["gateResultId"])], "failure": None,
    })
    pattern_admission_result_key = add("baseline-admission-result", pattern_admission_result, "bag15-pattern-admission-result.json")
    pattern_admission_receipt_key = add_receipt(pattern_admission_receipt, "bag15-receipt-pattern-admission.json")

    pattern_comparison_key = pattern_evaluation_key("baseline-mutant-comparison")
    pattern_comparison_invocation = invocation("oracle-comparison", {"evaluationKey": pattern_comparison_key, "keyDigest": pattern_comparison_key["keyDigest"]}, [
        ("declaration", pattern_comparison_key["declaration"]),
        ("baseline-operand", pattern_operand_production["baseline"][0]), ("mutant-operand", pattern_operand_production["mutant"][0]),
        ("baseline-execution-result", pattern_execution["baseline"][0]), ("mutant-execution-result", pattern_execution["mutant"][0]),
    ], [
        ("baseline-operand-production", pattern_operand_production["baseline"][1]),
        ("mutant-operand-production", pattern_operand_production["mutant"][1]),
    ])
    pattern_comparison_result, pattern_comparison_receipt = make_result_and_receipt("oracle-comparison", pattern_comparison_invocation, {
        "evaluationKey": pattern_comparison_key, "terminalRecord": {"kind": "comparison", "result": key("oracle-comparison-result", pattern_comparison_value["comparisonId"])},
        "producedArtifacts": [key("oracle-comparison-result", pattern_comparison_value["comparisonId"])], "failure": None,
    })
    pattern_comparison_result_key = add("oracle-comparison-production-result", pattern_comparison_result, "bag15-pattern-comparison-result.json")
    pattern_comparison_receipt_key = add_receipt(pattern_comparison_receipt, "bag15-receipt-pattern-comparison.json")

    bag14_invocations = {identity: value for (role, identity), value in base_assets.items() if role == "cache-campaign-invocation"}
    bag14_reports = [value for (role, _), value in base_assets.items() if role == "cache-mutation-report"]
    derivations: dict[str, tuple[dict[str, Any], dict[str, Any], dict[str, str], dict[str, str]]] = {}
    original_records_by_id = bag14_records
    for report in bag14_reports:
        campaign_invocation = bag14_invocations[report["campaignInvocation"]["digest"]]
        selected_plan = []
        inputs = [("campaign-invocation", report["campaignInvocation"]), ("materialization-result", materialization_result_key)]
        children = [("materialization-production", materialization_receipt_key)]
        selected_records = []
        for selected in report["selectedRecords"]:
            original_id = selected["recordId"]
            derivative = derivative_records[original_id]
            derivative_key = key("cache-record", derivative["recordId"])
            selected_plan.append({"slotId": selected["slotId"], "record": derivative_key})
            selected_records.append({"slotId": selected["slotId"], "recordId": derivative["recordId"]})
            inputs.append(("selected-cache-record", derivative_key))
            inputs.append(("selected-result", derivative["productionEvidence"]["result"]))
            children.append(("selected-record-production", record_receipts[original_id]))
        inv = invocation("campaign-derivation", {"campaignInvocation": deepcopy(report["campaignInvocation"]), "scheduleMode": report["scheduleMode"], "selectedPlan": selected_plan}, inputs, children)
        outcome = {
            "kind": "derived", "campaignInvocation": deepcopy(report["campaignInvocation"]), "scheduleMode": report["scheduleMode"],
            "selectedRecords": selected_records, "testStatuses": deepcopy(report["testStatuses"]),
            "scheduledButUnexecuted": deepcopy(report["scheduledButUnexecuted"]), "exclusions": deepcopy(report["exclusions"]),
            "score": deepcopy(report["score"]), "campaignStatus": report["campaignStatus"],
        }
        result, production_receipt = make_result_and_receipt("campaign-derivation", inv, {"outcome": outcome, "failure": None})
        result_key = add("campaign-derivation-result", result, f"bag15-derivation-result-{report['scheduleMode']}.json")
        receipt_key = add_receipt(production_receipt, f"bag15-receipt-derivation-{report['scheduleMode']}.json")
        derivations[report["scheduleMode"]] = (result, production_receipt, result_key, receipt_key)

    claim_assets = deepcopy(base_assets)
    claim_assets.update({identity: value for identity, (value, _) in new_assets.items()})
    receipt_by_id = {value["receiptId"]: value for value in receipts}
    claims = []
    for _, _, derivation_result_key, derivation_receipt_key in derivations.values():
        closure: set[str] = set()
        pending_receipts = [derivation_receipt_key["digest"]]
        while pending_receipts:
            receipt_id = pending_receipts.pop()
            if receipt_id in closure:
                continue
            closure.add(receipt_id)
            pending_receipts.extend(item["receipt"]["digest"] for item in receipt_by_id[receipt_id]["invocation"]["childReceipts"])
        claims.append(derive_version_claim(
            root, claim_assets, closure, [derivation_result_key, derivation_receipt_key],
            planned_roles={"operation-receipt", "report-publication-result", "provenance-mutation-report", "replay-version-registry"},
            planned_operations={("report-publication", 1)},
        ))
    if not claims or any(claim != claims[0] for claim in claims[1:]):
        raise AssertionError("BAG-15 first-kill/full closures derive different version registries")
    schema_entries, operation_entries = claims[0]
    registry = {
        "schemaVersion": 1, "registryId": "0" * 64,
        "schemas": schema_entries,
        "operations": operation_entries,
    }
    registry["registryId"] = digest("k-in-k/replay-version-registry/v1", without(registry, "registryId"))
    registry_key = add("replay-version-registry", registry, "bag15-replay-version-registry.json")

    publication_roots = []
    for schedule, (derivation_result, _, derivation_result_key, derivation_receipt_key) in derivations.items():
        inv = invocation("report-publication", {
            "derivationResult": derivation_result_key, "derivationReceipt": derivation_receipt_key,
            "versionRegistry": registry_key, "reportRole": "provenance-mutation-report", "reportVersion": 1,
        }, [("derivation-result", derivation_result_key), ("version-registry", registry_key)], [("derivation-production", derivation_receipt_key)])
        report = identify({
            "schemaVersion": 1, "reportId": "0" * 64, "derivationResult": derivation_result_key,
            "derivationReceipt": derivation_receipt_key, "versionRegistry": registry_key, "outcome": deepcopy(derivation_result["outcome"]),
        }, "reportId", "k-in-k/provenance-mutation-report/v1")
        report_key = add("provenance-mutation-report", report, f"bag15-provenance-report-{schedule}.json")
        publication_result, publication_receipt = make_result_and_receipt("report-publication", inv, {"outcome": {"kind": "published", "report": report_key}, "failure": None})
        publication_result_key = add("report-publication-result", publication_result, f"bag15-publication-result-{schedule}.json")
        publication_receipt_key = add_receipt(publication_receipt, f"bag15-receipt-publication-{schedule}.json")
        publication_roots.append({"scheduleMode": schedule, "report": report_key, "publicationResult": publication_result_key, "publicationReceipt": publication_receipt_key})

    entries = deepcopy(base_entries)
    for (role, identity), (value, name) in new_assets.items():
        entries[(role, identity)] = structured_entry(root, role, identity, value, name)
        write_json(fixtures / name, value)
    catalog = {"schemaVersion": 1, "catalogId": "0" * 64, "entries": sorted(entries.values(), key=lambda item: (item["role"], item["digest"])), "unboundRequirements": []}
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(catalog, "catalogId"))
    write_json(fixtures / "bag15-replay-artifact-catalog.json", catalog)

    pattern_evidence = {
        "baselineExecutionResult": pattern_execution["baseline"][0], "baselineExecutionReceipt": pattern_execution["baseline"][1],
        "mutantExecutionResult": pattern_execution["mutant"][0], "mutantExecutionReceipt": pattern_execution["mutant"][1],
        "baselineOperandResult": pattern_operand_production["baseline"][0], "baselineOperandReceipt": pattern_operand_production["baseline"][1],
        "mutantOperandResult": pattern_operand_production["mutant"][0], "mutantOperandReceipt": pattern_operand_production["mutant"][1],
        "admissionResult": pattern_admission_result_key, "admissionReceipt": pattern_admission_receipt_key,
        "comparisonResult": pattern_comparison_result_key, "comparisonReceipt": pattern_comparison_receipt_key,
        "baselineReplay": key("replay-manifest", read_json(fixtures / "bag12-baseline-pattern-replay.json")["replayId"]),
        "mutantReplay": key("replay-manifest", read_json(fixtures / "bag12-mutant-pattern-replay.json")["replayId"]),
        "baselinePatternResult": key("pattern-result", read_json(fixtures / "bag12-baseline-pattern-result.json")["resultId"]),
        "mutantPatternResult": key("pattern-result", read_json(fixtures / "bag12-mutant-pattern-result.json")["resultId"]),
    }
    pattern_evidence.update({
        "declaration": key("oracle-declaration", pattern_declaration_value["declarationId"]),
        "operands": [side["normalOperand"] for side in pattern_comparison_value["sides"]],
        "comparison": key("oracle-comparison-result", pattern_comparison_value["comparisonId"]),
    })
    ordinary_comparison_record = next(
        value for value in bag14_records.values()
        if value["kind"] == "oracle-evaluation" and value["key"]["evaluationKind"] == "baseline-mutant-comparison"
    )
    ordinary_declaration_key = ordinary_comparison_record["key"]["declaration"]
    ordinary_admission_record = next(
        value for value in bag14_records.values()
        if value["kind"] == "oracle-evaluation" and value["key"]["evaluationKind"] == "baseline-admission"
        and value["key"]["declaration"] == ordinary_declaration_key
    )
    ordinary_final_evidence: dict[str, Any] = {
        "declaration": ordinary_declaration_key,
        "admissionResult": derivative_records[ordinary_admission_record["recordId"]]["productionEvidence"]["result"],
        "admissionReceipt": record_receipts[ordinary_admission_record["recordId"]],
        "comparisonResult": derivative_records[ordinary_comparison_record["recordId"]]["productionEvidence"]["result"],
        "comparisonReceipt": record_receipts[ordinary_comparison_record["recordId"]],
        "comparison": ordinary_comparison_record["terminalRecord"]["result"],
    }
    for semantic in ordinary_comparison_record["key"]["semanticInputs"]:
        side = semantic["side"]
        operand_id = semantic["value"]["digest"]
        operand = base_assets[("oracle-operand", operand_id)]
        execution_record = next(
            value for value in bag14_records.values()
            if value["kind"] == "execution-attempt" and operand["completionEvidence"]["producerTrace"] in value["producedArtifacts"]
        )
        ordinary_final_evidence[f"{side}Operand"] = semantic["value"]
        ordinary_final_evidence[f"{side}OperandResult"] = operand_results[operand_id]
        ordinary_final_evidence[f"{side}OperandReceipt"] = operand_receipts[operand_id]
        ordinary_final_evidence[f"{side}ExecutionResult"] = execution_by_key[execution_record["keyDigest"]][2]
        ordinary_final_evidence[f"{side}ExecutionReceipt"] = execution_by_key[execution_record["keyDigest"]][3]
    vector = {
        "schemaVersion": 1, "artifactCatalogDigest": catalog["catalogId"],
        "publicationRoots": sorted(publication_roots, key=lambda item: item["scheduleMode"]),
        "standaloneRoots": {"invalidMaterialization": invalid_receipt_key, "boundedExecution": next(value[3] for value in execution_by_key.values() if value[0]["terminalRecord"]["kind"] == "bounded-stop")},
        "producerStateMatrix": [
            {"state": "complete-semantic-success", "receipt": materialization_receipt_key, "hasWrapper": True},
            {"state": "complete-semantic-failure", "receipt": invalid_receipt_key, "hasWrapper": True},
            {"state": "complete-bounded", "receipt": next(value[3] for value in execution_by_key.values() if value[0]["terminalRecord"]["kind"] == "bounded-stop"), "hasWrapper": True},
            {"state": "complete-diagnostic", "receipt": next(value[3] for value in execution_by_key.values() if value[0]["terminalRecord"]["kind"] == "diagnostic-only"), "hasWrapper": True},
            {"state": "failed-producer", "receipt": failed_producer_key, "hasWrapper": False},
        ],
        "patternEvidence": pattern_evidence,
        "ordinaryFinalEvidence": ordinary_final_evidence,
        "adversaries": [{"probe": name, "expected": "reject"} for name in ADVERSARIES],
    }
    write_json(root / "vectors" / "replay-provenance-vectors.json", vector)


class ReceiptVerifier:
    def __init__(self, root: Path, api: dict[str, Any]):
        self.root = root
        self.fixtures = root / "fixtures"
        self.api = api
        self.ok: Callable[[bool, str], None] = api["ok"]
        self.catalog = read_json(self.fixtures / "bag15-replay-artifact-catalog.json")
        self.entries = {(item["role"], item["digest"]): item for item in self.catalog["entries"]}
        self.ok(len(self.entries) == len(self.catalog["entries"]), "BAG-15 derivative catalog duplicates a key")
        self.assets: dict[tuple[str, str], Any] = {}
        for identity, entry in self.entries.items():
            self.ok(entry["availability"] == "bundled" and entry["resolverId"] == "repo-v1", "BAG-15 positive material is not wholly bundled")
            path = root.parents[1] / entry["logicalPath"].removeprefix("repo://")
            self.ok(path.is_file(), "BAG-15 bundled material is missing")
            data = path.read_bytes()
            self.ok(raw_sha256(data) == entry["contentSha256"], "BAG-15 material byte digest drift")
            if entry["contentModel"] == "canonical-json":
                value = json.loads(data.decode("utf-8"))
                self.ok(data == canonical(value).encode("utf-8"), "BAG-15 material is not canonical JSON")
                self.assets[identity] = value
        self.vector = read_json(root / "vectors" / "replay-provenance-vectors.json")
        self.ok(self.vector["artifactCatalogDigest"] == self.catalog["catalogId"] == digest("k-in-k/artifact-catalog/v1", without(self.catalog, "catalogId")), "BAG-15 vector/catalog identity drift")
        self.receipts = {identity: value for (role, identity), value in self.assets.items() if role == "operation-receipt"}
        self.oracle = OracleVerifier(root, api)
        self.bag14 = CacheVerifier(root, {**api, "validate_operation_receipt_production": self.validate_operation_receipt_production})

    def resolve(self, artifact: dict[str, str]) -> Any:
        self.ok(set(artifact) == {"role", "digest"}, "BAG-15 artifact key is open")
        identity = (artifact["role"], artifact["digest"])
        self.ok(identity in self.entries, f"BAG-15 unresolved artifact {artifact}")
        return self.assets.get(identity, self.entries[identity])

    def validate_wrapper_identity(self, role: str, value: dict[str, Any], identity: str) -> None:
        self.ok(value["resultId"] == identity == digest(RESULT_DOMAINS[role], without(value, "resultId")), f"BAG-15 {role} identity drift")

    def validate_no_output_receipt_cycle(self, receipt_id: str, result: dict[str, Any]) -> None:
        self.ok(receipt_id not in {item["digest"] for item in artifact_keys(result)}, "BAG-15 result creates an output-to-receipt cycle")

    def child_output(self, child: dict[str, Any]) -> dict[str, str]:
        child_value = self.receipts[child["receipt"]["digest"]]
        self.ok(child_value["producerStatus"] == "complete" and len(child_value["outputs"]) == 1, "BAG-15 child receipt did not atomically publish one wrapper")
        return child_value["outputs"][0]["artifact"]

    def validate_invocation_edges(self, value: dict[str, Any]) -> None:
        inv = value["invocation"]
        operation = inv["operationKind"]
        inputs = inv["inputs"]
        children = inv["childReceipts"]
        parameters = inv["parameters"]
        if operation == "mutation-materialization":
            expected_inputs = [
                ("baseline-definition", parameters["baseline"]), ("mutation-operator", parameters["operator"]),
                ("patch", parameters["patch"]), ("compatibility-profile", parameters["compatibilityProfile"]),
                ("lowering-profile", parameters["loweringProfile"]),
            ]
            expected_children: list[tuple[str, dict[str, str]]] = []
        elif operation == "execution-attempt":
            expected_inputs = [("key-artifact", item) for item in unique_artifacts(artifact_keys(parameters["executionKey"]))]
            expected_children = []
        elif operation == "oracle-operand-production":
            self.ok(len(children) == 1 and children[0]["edgeRole"] == "execution-production", "BAG-15 operand production child sequence drift")
            execution_result = self.child_output(children[0])
            outcome = self.resolve(value["outputs"][0]["artifact"])["outcome"] if value["producerStatus"] == "complete" else None
            self.ok(isinstance(outcome, dict) and outcome.get("kind") == "operand", "BAG-15 finite operand producer did not publish an operand")
            operand = self.resolve(outcome["operand"])
            declaration = self.resolve(parameters["declaration"])
            if declaration["kind"] == "execution-pattern":
                pattern_result_key = operand["completionEvidence"]["patternResult"]
                pattern_result = self.resolve(pattern_result_key)
                self.ok(len(pattern_result["pathResults"]) == 1, "BAG-15 reviewed pattern operand does not have one exact execution path")
                path_result = pattern_result["pathResults"][0]
                terminal = path_result["executionTerminal"]["artifact"]
                trace = key("event-trace", path_result["traceDigest"])
            else:
                terminal = operand["completionEvidence"]["terminal"]["artifact"]
                trace = operand["completionEvidence"]["producerTrace"]
            expected_inputs = [("declaration", parameters["declaration"]), ("execution-result", execution_result), ("execution-terminal", terminal), ("producer-trace", trace)]
            if declaration["kind"] == "execution-pattern":
                self.ok(len(inputs) == 6, "BAG-15 execution-pattern operand lacks exact replay/result provenance")
                expected_inputs.extend([("pattern-replay", inputs[4]["artifact"]), ("pattern-result", inputs[5]["artifact"])])
                replay = self.resolve(inputs[4]["artifact"])
                pattern_result = self.resolve(inputs[5]["artifact"])
                config = declaration["kindConfig"]
                definition_digest = operand["subject"]["definitionDigest"] if operand["subject"]["side"] == "baseline" else operand["subject"]["mutantDefinitionDigest"]
                self.ok(inputs[5]["artifact"] == operand["completionEvidence"]["patternResult"] and replay["expectedResultDigest"] == pattern_result["resultId"], "BAG-15 pattern operand/replay names another result")
                self.ok(pattern_result["inputs"]["replayInvocationDigest"] == replay["invocationDigest"] and replay["definitionDigest"] == pattern_result["inputs"]["definitionDigest"] == definition_digest, "BAG-15 pattern replay/result belongs to another execution subject")
                self.ok(replay["testId"] == pattern_result["testId"] and declaration["testInvocationDigest"] == operand["testInvocationDigest"], "BAG-15 pattern replay/result belongs to another test")
                self.ok(replay["patternSource"] == pattern_result["inputs"]["patternSource"] == config["patternSource"] and replay["patternPlan"] == pattern_result["inputs"]["patternPlan"] == config["patternPlan"] and replay["patternQuery"] == pattern_result["inputs"]["patternQuery"] == config["patternQuery"], "BAG-15 pattern query/plan/source drift")
                self.ok(trace in pattern_result["inputs"]["artifacts"] and trace in replay["steps"][2]["expectedArtifacts"], "BAG-15 pattern result trace lacks exact replay production")
                self.oracle.validate_operand(operand)
            expected_children = [("execution-production", children[0]["receipt"])]
            execution_wrapper = self.resolve(execution_result)
            execution_receipt = self.receipts[children[0]["receipt"]["digest"]]
            execution_key = execution_receipt["invocation"]["parameters"]["executionKey"]
            self.ok(execution_key["testInvocationDigest"] == operand["testInvocationDigest"] == declaration["testInvocationDigest"], "BAG-15 receipt/test invocation drift")
            self.ok(execution_key["compatibilityProfileDigest"] == operand["compatibilityProfileDigest"] and execution_key["executionProfileDigest"] == operand["executionProfileDigest"] and execution_key["solverProfileDigest"] == operand["solverProfileDigest"], "BAG-15 execution/operand profile drift")
            if operand["subject"]["side"] == "baseline":
                self.ok(execution_key["subject"] == {"kind": "baseline", "definition": key("definition", operand["subject"]["definitionDigest"])}, "BAG-15 baseline execution/operand definition drift")
            else:
                self.ok(execution_key["subject"]["kind"] == "mutant" and execution_key["subject"]["baselineDefinition"]["digest"] == operand["subject"]["baselineDefinitionDigest"] and execution_key["subject"]["mutantId"] == operand["subject"]["mutantId"] and execution_key["subject"]["mutantDefinition"]["digest"] == operand["subject"]["mutantDefinitionDigest"], "BAG-15 mutant execution/operand definition drift")
            self.ok(parameters["side"] == operand["subject"]["side"] and parameters["subject"] == operand["subject"] and parameters["declaration"] == operand["declaration"], "BAG-15 operand subject/declaration drift")
            self.ok(parameters["executionKeyDigest"] == execution_wrapper["keyDigest"] and parameters["executionInvocationDigest"] == execution_wrapper["invocationDigest"], "BAG-15 operand names another execution attempt")
            self.ok(terminal in execution_wrapper["producedArtifacts"] and trace in execution_wrapper["producedArtifacts"], "BAG-15 operand terminal/trace was not produced by its execution attempt")
        elif operation in {"baseline-admission", "oracle-comparison"}:
            sides = ["baseline"] if operation == "baseline-admission" else ["baseline", "mutant"]
            expected_inputs = [("declaration", parameters["evaluationKey"]["declaration"])]
            expected_children = []
            execution_inputs: list[tuple[str, dict[str, str]]] = []
            semantic_by_side = {item["side"]: item["value"] for item in parameters["evaluationKey"]["semanticInputs"]}
            self.ok(len(children) == len(sides), "BAG-15 oracle child cardinality drift")
            for index, side in enumerate(sides):
                child = children[index]
                self.ok(child["edgeRole"] == f"{side}-operand-production", "BAG-15 oracle operand child order drift")
                operand_wrapper_key = self.child_output(child)
                operand_wrapper = self.resolve(operand_wrapper_key)
                self.ok(operand_wrapper["outcome"] == {"kind": "operand", "operand": semantic_by_side[side]}, "BAG-15 oracle child produced another semantic operand")
                expected_inputs.append((f"{side}-operand", operand_wrapper_key))
                execution_key = self.receipts[child["receipt"]["digest"]]["invocation"]["inputs"][1]["artifact"]
                execution_inputs.append((f"{side}-execution-result", execution_key))
                expected_children.append((f"{side}-operand-production", child["receipt"]))
            expected_inputs.extend(execution_inputs)
        elif operation == "campaign-derivation":
            plan = parameters["selectedPlan"]
            self.ok(len(children) == len(plan) + 1 and children[0]["edgeRole"] == "materialization-production", "BAG-15 derivation child cardinality/order drift")
            materialization = self.child_output(children[0])
            expected_inputs = [("campaign-invocation", parameters["campaignInvocation"]), ("materialization-result", materialization)]
            expected_children = [("materialization-production", children[0]["receipt"])]
            for index, selected in enumerate(plan, start=1):
                record = self.resolve(selected["record"])
                child = children[index]
                self.ok(child["edgeRole"] == "selected-record-production" and child["receipt"] == record["productionEvidence"]["receipt"], "BAG-15 derivation selected another record producer")
                result_key = self.child_output(child)
                self.ok(result_key == record["productionEvidence"]["result"], "BAG-15 derivation selected record/result wrapper drift")
                expected_inputs.extend([("selected-cache-record", selected["record"]), ("selected-result", result_key)])
                expected_children.append(("selected-record-production", child["receipt"]))
        else:
            self.ok(len(children) == 1 and children[0]["edgeRole"] == "derivation-production", "BAG-15 publication child sequence drift")
            expected_inputs = [("derivation-result", parameters["derivationResult"]), ("version-registry", parameters["versionRegistry"])]
            expected_children = [("derivation-production", parameters["derivationReceipt"])]
            self.ok(children[0]["receipt"] == parameters["derivationReceipt"] and self.child_output(children[0]) == parameters["derivationResult"], "BAG-15 publication names another derivation producer")
        actual_inputs = [(item["edgeRole"], item["artifact"]) for item in inputs]
        actual_children = [(item["edgeRole"], item["receipt"]) for item in children]
        self.ok(actual_inputs == expected_inputs, f"BAG-15 {operation} exact input edge sequence drift")
        self.ok(actual_children == expected_children, f"BAG-15 {operation} exact child edge sequence drift")

    def validate_operation_failure(self, operation: str, inv: dict[str, Any], failure: dict[str, Any]) -> None:
        contexts = {
            "mutation-materialization": "mutant-validation", "oracle-operand-production": "oracle-operand-production",
            "baseline-admission": "baseline-oracle-gate", "oracle-comparison": "oracle-comparison",
            "campaign-derivation": "campaign", "report-publication": "report-publication",
        }
        expected = contexts.get(operation)
        if operation == "execution-attempt":
            expected = "baseline-execution" if inv["parameters"]["executionKey"]["subject"]["kind"] == "baseline" else "mutant-execution"
        self.ok(failure["context"] == expected, "BAG-15 failure is incompatible with its operation/subject")

    def validate_materialization_result(self, inv: dict[str, Any], result: dict[str, Any]) -> None:
        parameters = inv["parameters"]
        baseline = self.resolve(parameters["baseline"])
        operator = self.resolve(parameters["operator"])
        patch = self.resolve(parameters["patch"])
        self.resolve(parameters["compatibilityProfile"])
        self.resolve(parameters["loweringProfile"])
        self.ok((patch["operatorId"], patch["operatorVersion"]) == (operator["operatorId"], operator["operatorVersion"]), "BAG-15 materialization operator/patch authority drift")
        expected_candidate = digest("k-in-k/candidate/v1", {
            "operatorId": patch["operatorId"], "operatorVersion": patch["operatorVersion"],
            "baselineDefinitionDigest": baseline["definitionDigest"], "patchId": patch["patchId"],
        })
        self.ok(parameters["candidateId"] == expected_candidate, "BAG-15 materialization candidate identity was not independently derived")
        local_policy = digest("k-in-k/materialization-validation-policy/v1", {"mode": "portable-local-well-formedness"})
        rejecting_policy = digest("k-in-k/materialization-validation-policy/v1", {"mode": "reject-invalid-lowering"})
        outcome = result["outcome"]
        if parameters["validationPolicyDigest"] == local_policy:
            mutant = self.resolve(outcome["mutantDefinition"])
            selector = self.resolve(key("mutation-selector", operator["selectorDigest"]))
            self.ok(outcome["kind"] == "materialized", "BAG-15 successful materialization selected another semantic arm")
            self.bag14.validate_patch_materialization(baseline, mutant, operator, selector, patch)
            expected_diff = derive_structural_diff(baseline, mutant, patch)
            self.ok(self.resolve(outcome["structuralDiff"]) == expected_diff, "BAG-15 structural diff was not independently derived from the exact patch")
            self.ok(result["failure"] is None, "BAG-15 successful materialization carries a failure")
        else:
            expected_failure = {"stage": "ir-validation", "classification": "invalid-module", "context": "mutant-validation", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
            self.ok(parameters["validationPolicyDigest"] == rejecting_policy and outcome == {"kind": "invalid", "failure": expected_failure} and result["failure"] == expected_failure, "BAG-15 completed validation failure was not exactly derived from its reviewed policy/input row")

    def validate_pattern_execution_result(self, inv: dict[str, Any], result: dict[str, Any]) -> None:
        execution_key = inv["parameters"]["executionKey"]
        evidence = self.vector["patternEvidence"]
        pattern_result_ids = {evidence["baselineExecutionResult"]["digest"], evidence["mutantExecutionResult"]["digest"]}
        if execution_key["attemptKind"]["kind"] != "query-coupled" and result["resultId"] not in pattern_result_ids:
            return
        side = "baseline" if execution_key["subject"]["kind"] == "baseline" else "mutant"
        replay = self.resolve(evidence[f"{side}Replay"])
        pattern_result = self.resolve(evidence[f"{side}PatternResult"])
        declaration = self.resolve(evidence["declaration"])
        operand = self.resolve(evidence["operands"][0 if side == "baseline" else 1])
        regression = deepcopy(self.bag14.vector["queryCoupledRegression"])
        if side == "baseline":
            self.bag14.validate_query_coupled_regression(regression)
            expected_subject = {"kind": "baseline", "definition": key("definition", operand["subject"]["definitionDigest"])}
        else:
            campaign = read_json(self.fixtures / "mutation-campaign.json")
            candidate = campaign["generation"]["candidates"][0]
            mutant = campaign["mutants"][0]
            operator = read_json(self.fixtures / "mutation-operator.json")
            expected_subject = {
                "kind": "mutant", "baselineDefinition": key("definition", operand["subject"]["baselineDefinitionDigest"]),
                "candidateId": candidate["candidateId"], "operator": key("mutation-operator", operator["operatorDigest"]),
                "patch": key("patch", candidate["patch"]["patchId"]), "mutantId": mutant["mutantId"],
                "mutantDefinition": key("mutant-definition", operand["subject"]["mutantDefinitionDigest"]),
            }
        expected_key = deepcopy(regression["executionKey"])
        expected_key["subject"] = expected_subject
        expected_key["attemptKind"]["observationInputs"] = [key("observation-manifest", replay["observationManifestDigest"])]
        expected_key["keyDigest"] = digest("k-in-k/execution-attempt-key/v1", without(expected_key, "keyDigest"))
        self.ok(execution_key == expected_key and inv["parameters"]["keyDigest"] == expected_key["keyDigest"], "BAG-15 pattern execution key is not the exact BAG-11/declaration-derived request")
        attempt = execution_key["attemptKind"]
        config = declaration["kindConfig"]
        self.ok({name: attempt[name] for name in ("patternSource", "patternPlan", "patternQuery", "searchPolicy")} == {name: config[name] for name in ("patternSource", "patternPlan", "patternQuery", "searchPolicy")}, "BAG-15 pattern attempt/query declaration drift")
        self.ok(replay["patternSource"] == attempt["patternSource"] and replay["patternPlan"] == attempt["patternPlan"] and replay["patternQuery"] == attempt["patternQuery"] and replay["searchPolicy"] == attempt["searchPolicy"], "BAG-15 pattern execution key differs from its exact BAG-11 replay")
        self.ok(digest("k-in-k/bounds/v1", replay["bounds"]) == declaration["boundsDigest"] and replay["testId"] == pattern_result["testId"], "BAG-15 pattern bounds/test replay drift")
        self.ok(execution_key["testInvocationDigest"] == declaration["testInvocationDigest"] == operand["testInvocationDigest"] and execution_key["compatibilityProfileDigest"] == replay["compatibilityProfileDigest"] and execution_key["executionProfileDigest"] == replay["executionProfileDigest"] and execution_key["solverProfileDigest"] == replay["solverProfileDigest"], "BAG-15 pattern test/profile key drift")
        observation_key = attempt["observationInputs"][0]
        observation = self.resolve(observation_key)
        definition_digest = operand["subject"]["definitionDigest"] if side == "baseline" else operand["subject"]["mutantDefinitionDigest"]
        self.ok(observation_key == key("observation-manifest", replay["observationManifestDigest"]) and observation["inputDefinitionDigest"] == observation["outputDefinitionDigest"] == definition_digest, "BAG-15 pattern observation input belongs to another subject/replay")
        self.ok(len(pattern_result["pathResults"]) == 1, "BAG-15 reviewed pattern execution has ambiguous path outputs")
        path_result = pattern_result["pathResults"][0]
        terminal_key = path_result["executionTerminal"]["artifact"]
        trace_key = key("event-trace", path_result["traceDigest"])
        expected_terminal = {"kind": path_result["executionTerminal"]["kind"], "terminal": terminal_key}
        self.ok(result["terminalRecord"] == expected_terminal and result["producedArtifacts"] == [terminal_key, trace_key], "BAG-15 non-cache pattern execution outputs were not exactly derived in order/cardinality")
        self.ok(trace_key in replay["steps"][2]["expectedArtifacts"] and trace_key in pattern_result["inputs"]["artifacts"] and replay["expectedResultDigest"] == pattern_result["resultId"], "BAG-15 pattern trace/result lacks exact BAG-11 replay production")

    def validate_receipt(self, value: dict[str, Any]) -> None:
        self.ok(value["receiptId"] == digest("k-in-k/operation-receipt/v1", without(value, "receiptId")), "BAG-15 receipt identity drift")
        inv = value["invocation"]
        self.ok(value["invocationDigest"] == inv["invocationDigest"] == digest("k-in-k/operation-invocation/v1", without(inv, "invocationDigest")), "BAG-15 invocation/receipt identity drift")
        operation = inv["operationKind"]
        role = OPERATIONS[operation]
        self.ok(inv["operationVersion"] == 1 and inv["outputRoles"] == [role], "BAG-15 operation version/output role drift")
        self.ok(inv["adapterContract"] == {"adapterId": "bag15-portable-finite", "adapterVersion": 1}, "BAG-15 adapter contract drift")
        for edge in inv["inputs"]:
            self.resolve(edge["artifact"])
        for child in inv["childReceipts"]:
            self.ok(child["receipt"]["digest"] in self.receipts and child["receipt"]["digest"] != value["receiptId"], "BAG-15 missing/self child receipt")
        self.validate_invocation_edges(value)
        if value["producerStatus"] == "failed":
            self.ok(value["outputs"] == [] and value["semanticTerminal"] is None and value["failure"] is not None and value["producer"]["executionConformance"] == "not-proven", "BAG-15 failed producer fabricated semantic publication")
            self.ok(operation in {"execution-attempt", "campaign-derivation"} and value["failure"]["stage"] == "infrastructure", "BAG-15 semantic failure was converted into a failed producer")
            if operation == "campaign-derivation":
                self.ok(value["failure"]["classification"] == "internal", "BAG-15 campaign failed producer is not the exact BAG-10 infrastructure placement")
            self.validate_failure_taxonomy(value["failure"])
            self.validate_operation_failure(operation, inv, value["failure"])
            return
        self.ok(value["producerStatus"] == "complete" and len(value["outputs"]) == 1, "BAG-15 complete receipt output arity drift")
        output = value["outputs"][0]
        self.ok(output["edgeRole"] == role and output["artifact"]["role"] == role, "BAG-15 receipt output role drift")
        result = self.resolve(output["artifact"])
        self.validate_wrapper_identity(role, result, output["artifact"]["digest"])
        self.validate_no_output_receipt_cycle(value["receiptId"], result)
        self.ok(result["invocationDigest"] == inv["invocationDigest"], "BAG-15 wrapper names another invocation")
        terminal = semantic_terminal_for_wrapper(role, result)
        expected_failure = selected_failure(terminal)
        self.ok(value["semanticTerminal"] == terminal and value["failure"] == expected_failure, "BAG-15 wrapper/receipt terminal or failure drift")
        if role != "execution-attempt-result":
            self.ok(result["failure"] == expected_failure, "BAG-15 wrapper top-level failure drift")
        if value["failure"] is not None:
            self.validate_failure_taxonomy(value["failure"])
            self.validate_operation_failure(operation, inv, value["failure"])
        self.ok(value["producer"]["executionConformance"] == "finite-vector-proven", "BAG-15 bundled receipt is not finite-vector-proven")
        if operation == "mutation-materialization":
            self.validate_materialization_result(inv, result)
        elif operation == "execution-attempt":
            self.ok(result["keyDigest"] == inv["parameters"]["keyDigest"] == inv["parameters"]["executionKey"]["keyDigest"], "BAG-15 BAG-14 execution key drift")
            self.ok(result["keyDigest"] != inv["invocationDigest"], "BAG-15 BAG-14 key was conflated with generic invocation")
            self.ok(result["terminalRecord"] == value["semanticTerminal"], "BAG-15 execution semanticTerminal is not exact terminalRecord")
            self.validate_pattern_execution_result(inv, result)
        elif operation in {"baseline-admission", "oracle-comparison"}:
            self.ok(result["evaluationKey"] == inv["parameters"]["evaluationKey"] and result["evaluationKey"]["keyDigest"] == inv["parameters"]["keyDigest"], "BAG-15 oracle wrapper key drift")
        elif operation == "report-publication":
            forbidden = {"expectedBody", "expectedBodyBytes", "reportDigest", "reportBody", "body"}
            self.ok(not (forbidden & set(inv["parameters"])), "BAG-15 publication invocation contains expected report output")

    def validate_failure_taxonomy(self, failure: dict[str, Any]) -> None:
        matches = [
            entry for entry in self.oracle.taxonomy["entries"]
            if (entry["stage"], entry["classification"]) == (failure["stage"], failure["classification"])
            and any((placement["context"], placement["scope"]) == (failure["context"], failure["scope"]) for placement in entry["placements"])
        ]
        self.ok(len(matches) == 1 and matches[0]["retryability"] == failure["retryability"], "BAG-15 failure lacks exact active BAG-10 taxonomy authority")

    def validate_operation_receipt_production(self, record: dict[str, Any], production: dict[str, Any]) -> None:
        receipt_value = self.resolve(production["receipt"])
        result = self.resolve(production["result"])
        self.validate_receipt(receipt_value)
        self.ok(receipt_value["outputs"][0]["artifact"] == production["result"], "BAG-15 cache production names another receipt output")
        if record["kind"] == "execution-attempt":
            self.ok(production["result"]["role"] == "execution-attempt-result", "BAG-15 execution cache uses another wrapper")
            self.ok(result["keyDigest"] == record["keyDigest"] and result["terminalRecord"] == record["terminalRecord"] and result["producedArtifacts"] == record["producedArtifacts"], "BAG-15 execution wrapper/cache record disagreement")
        else:
            expected_role = "baseline-admission-result" if record["key"]["evaluationKind"] == "baseline-admission" else "oracle-comparison-production-result"
            self.ok(production["result"]["role"] == expected_role, "BAG-15 oracle cache uses wrong wrapper")
            self.ok(result["evaluationKey"] == record["key"] and result["terminalRecord"] == record["terminalRecord"] and result["producedArtifacts"] == record["producedArtifacts"], "BAG-15 oracle wrapper/cache record disagreement")

    def validate_dag(self, root_receipt: dict[str, str]) -> set[str]:
        visited: set[str] = set()
        active: set[str] = set()
        def visit(receipt_id: str) -> None:
            self.ok(receipt_id not in active, "BAG-15 cyclic receipt DAG")
            if receipt_id in visited:
                return
            active.add(receipt_id)
            current = self.receipts[receipt_id]
            for child in current["invocation"]["childReceipts"]:
                visit(child["receipt"]["digest"])
            active.remove(receipt_id)
            visited.add(receipt_id)
        visit(root_receipt["digest"])
        producers: dict[tuple[str, str], str] = {}
        consumers: dict[tuple[str, str], int] = {}
        for receipt_id in visited:
            current = self.receipts[receipt_id]
            if current["producerStatus"] == "complete":
                output = current["outputs"][0]["artifact"]
                identity = (output["role"], output["digest"])
                self.ok(identity not in producers, "BAG-15 closure has duplicate producers for one wrapper")
                producers[identity] = receipt_id
            for edge in current["invocation"]["inputs"]:
                artifact = edge["artifact"]
                identity = (artifact["role"], artifact["digest"])
                consumers[identity] = consumers.get(identity, 0) + 1
            parent_inputs = [edge["artifact"] for edge in current["invocation"]["inputs"]]
            for child in current["invocation"]["childReceipts"]:
                output = self.child_output(child)
                self.ok(parent_inputs.count(output) == 1, "BAG-15 child output is dangling, duplicated, or not consumed by its parent")
        for identity, producer in producers.items():
            if producer == root_receipt["digest"]:
                self.ok(consumers.get(identity, 0) == 0, "BAG-15 publication root output was consumed inside its own closure")
            else:
                self.ok(consumers.get(identity, 0) >= 1, "BAG-15 intermediate wrapper has no exact consumer")
        for receipt_id in visited:
            for edge in self.receipts[receipt_id]["invocation"]["inputs"]:
                artifact = edge["artifact"]
                if artifact["role"] in set(OPERATIONS.values()):
                    self.ok((artifact["role"], artifact["digest"]) in producers, "BAG-15 wrapper input has no producer in the exact closure")
        return visited

    def validate_registry(self, registry: dict[str, Any], report_key: dict[str, str], closure: set[str]) -> None:
        self.ok(registry["registryId"] == digest("k-in-k/replay-version-registry/v1", without(registry, "registryId")), "BAG-15 registry identity drift")
        schemas = registry["schemas"]
        operations = registry["operations"]
        self.ok(schemas == sorted(schemas, key=lambda item: (item["schemaId"], item["schemaVersion"])) and len({item["schemaId"] for item in schemas}) == len(schemas), "BAG-15 schema registry order/duplicate drift")
        self.ok(operations == sorted(operations, key=lambda item: (item["operationKind"], item["operationVersion"])) and len({(item["operationKind"], item["operationVersion"]) for item in operations}) == len(operations), "BAG-15 operation registry order/duplicate drift")
        expected_schemas, expected_operations = derive_version_claim(self.root, self.assets, closure, [report_key])
        self.ok(schemas == expected_schemas, "BAG-15 recursive schema registry has missing, surplus, aliased, or incorrect byte claims")
        self.ok(operations == expected_operations, "BAG-15 operation registry differs from exact receipt closure")

    def validate_report_root(self, root: dict[str, Any]) -> None:
        publication = self.resolve(root["publicationReceipt"])
        self.validate_receipt(publication)
        closure = self.validate_dag(root["publicationReceipt"])
        operations = {self.receipts[item]["invocation"]["operationKind"] for item in closure}
        self.ok(operations == set(OPERATIONS), "BAG-15 claimed report receipt closure omits an operation kind")
        report = self.resolve(root["report"])
        publication_result = self.resolve(root["publicationResult"])
        self.ok(publication_result["outcome"] == {"kind": "published", "report": root["report"]}, "BAG-15 publication result names another report")
        derivation = self.resolve(report["derivationResult"])
        derivation_receipt = self.resolve(report["derivationReceipt"])
        self.ok(derivation_receipt["outputs"][0]["artifact"] == report["derivationResult"] and report["outcome"] == derivation["outcome"], "BAG-15 report did not derive from exact result/receipt")
        self.ok(root["publicationReceipt"]["digest"] not in {item["digest"] for item in artifact_keys(report)}, "BAG-15 report points to its own publication receipt")
        self.validate_registry(self.resolve(report["versionRegistry"]), root["report"], closure)
        outcome = derivation["outcome"]
        self.ok(outcome["kind"] == "derived" and outcome["scheduleMode"] == root["scheduleMode"], "BAG-15 publication selected another campaign/schedule outcome")
        selected = outcome["selectedRecords"]
        invocation_value = self.resolve(derivation["outcome"]["campaignInvocation"])
        original_selected = []
        for mapping in selected:
            derivative = self.resolve(key("cache-record", mapping["recordId"]))
            originals = [
                original for original in self.bag14.records.values()
                if original["kind"] == derivative["kind"] and original["keyDigest"] == derivative["keyDigest"]
            ]
            self.ok(len(originals) == 1, "BAG-15 derivative cache record does not map to one exact BAG-14 key/kind")
            original_selected.append({"slotId": mapping["slotId"], "recordId": originals[0]["recordId"]})
        expected_report = self.bag14.derive_semantic_report(invocation_value, original_selected)
        expected_outcome = {
            "kind": "derived", "campaignInvocation": expected_report["campaignInvocation"], "scheduleMode": expected_report["scheduleMode"],
            "selectedRecords": deepcopy(selected), "testStatuses": expected_report["testStatuses"],
            "scheduledButUnexecuted": expected_report["scheduledButUnexecuted"], "exclusions": expected_report["exclusions"],
            "score": expected_report["score"], "campaignStatus": expected_report["campaignStatus"],
        }
        self.ok(outcome == expected_outcome, "BAG-15 statuses/exclusions/score/first-kill closure were not independently derived through BAG-14")
        selected_plan = derivation_receipt["invocation"]["parameters"]["selectedPlan"]
        self.ok(selected_plan == [{"slotId": item["slotId"], "record": key("cache-record", item["recordId"])} for item in selected], "BAG-15 derivation parameters differ from exact derived record selection")

    def expect_rejection(self, callback: Callable[[], None], message: str) -> None:
        try:
            callback()
        except (AssertionError, KeyError, ValueError, TypeError):
            self.ok(True, message)
        else:
            raise AssertionError(message)

    def adversaries(self) -> None:
        advertised = [item["probe"] for item in self.vector["adversaries"]]
        self.ok(advertised == list(ADVERSARIES) and len(set(advertised)) == len(advertised), "BAG-15 adversary registry drift")
        complete = next(value for value in self.receipts.values() if value["producerStatus"] == "complete" and value["invocation"]["operationKind"] == "execution-attempt")
        failed = next(value for value in self.receipts.values() if value["producerStatus"] == "failed")
        by_operation = {operation: next(value for value in self.receipts.values() if value["producerStatus"] == "complete" and value["invocation"]["operationKind"] == operation) for operation in OPERATIONS}
        pattern = self.vector["patternEvidence"]
        pattern_operand = self.resolve(pattern["baselineOperandReceipt"])
        ordinary = self.vector["ordinaryFinalEvidence"]
        first_root, full_root = self.vector["publicationRoots"]

        def reject_edges(bad: dict[str, Any], name: str) -> None:
            self.expect_rejection(lambda: self.validate_invocation_edges(bad), name)

        def original_selection(root: dict[str, Any]) -> tuple[dict[str, Any], list[dict[str, str]]]:
            report = self.resolve(root["report"])
            outcome = self.resolve(report["derivationResult"])["outcome"]
            campaign = self.resolve(outcome["campaignInvocation"])
            mappings = []
            for item in outcome["selectedRecords"]:
                derivative = self.resolve(key("cache-record", item["recordId"]))
                original = next(value for value in self.bag14.records.values() if value["kind"] == derivative["kind"] and value["keyDigest"] == derivative["keyDigest"])
                mappings.append({"slotId": item["slotId"], "recordId": original["recordId"]})
            return campaign, mappings

        for name in advertised:
            if name == "patch-only-as-kill":
                bad = deepcopy(by_operation["campaign-derivation"]); bad["invocation"]["childReceipts"][1] = deepcopy(bad["invocation"]["childReceipts"][0]); reject_edges(bad, name)
            elif name in {"result-without-execution-receipt", "final-result-without-attempt"}:
                bad = deepcopy(pattern_operand if name == "result-without-execution-receipt" else self.resolve(ordinary["baselineOperandReceipt"])); bad["invocation"]["childReceipts"] = []; reject_edges(bad, name)
            elif name == "subject-reversal":
                bad = deepcopy(pattern_operand); bad["invocation"]["parameters"]["side"] = "mutant"; reject_edges(bad, name)
            elif name in {"receipt-test-drift", "receipt-definition-drift"}:
                child_id = pattern_operand["invocation"]["childReceipts"][0]["receipt"]["digest"]
                original_child = self.receipts[child_id]
                bad_child = deepcopy(original_child)
                if name == "receipt-test-drift":
                    bad_child["invocation"]["parameters"]["executionKey"]["testInvocationDigest"] = "f" * 64
                else:
                    bad_child["invocation"]["parameters"]["executionKey"]["subject"]["definition"]["digest"] = "f" * 64
                self.receipts[child_id] = bad_child
                try: self.expect_rejection(lambda: self.validate_invocation_edges(pattern_operand), name)
                finally: self.receipts[child_id] = original_child
            elif name == "pattern-query-drift":
                source = self.resolve(pattern["baselineExecutionReceipt"])
                source_result = self.resolve(pattern["baselineExecutionResult"])
                ordinary_key = deepcopy(source["invocation"]); ordinary_key["parameters"]["executionKey"]["attemptKind"] = {"kind": "ordinary"}; ordinary_key["parameters"]["executionKey"]["keyDigest"] = digest("k-in-k/execution-attempt-key/v1", without(ordinary_key["parameters"]["executionKey"], "keyDigest")); ordinary_key["parameters"]["keyDigest"] = ordinary_key["parameters"]["executionKey"]["keyDigest"]
                self.expect_rejection(lambda: self.validate_pattern_execution_result(ordinary_key, source_result), name)
                alternate = deepcopy(source["invocation"]); alternate["parameters"]["executionKey"]["attemptKind"]["patternQuery"] = key("pattern-query", read_json(self.fixtures / "pattern-query-single-write.json")["queryId"]); alternate["parameters"]["executionKey"]["keyDigest"] = digest("k-in-k/execution-attempt-key/v1", without(alternate["parameters"]["executionKey"], "keyDigest")); alternate["parameters"]["keyDigest"] = alternate["parameters"]["executionKey"]["keyDigest"]
                self.expect_rejection(lambda: self.validate_pattern_execution_result(alternate, source_result), name)
            elif name == "oracle-policy-drift":
                record = deepcopy(self.resolve(key("cache-record", next(item["recordId"] for item in self.resolve(full_root["report"])["outcome"]["selectedRecords"] if self.resolve(key("cache-record", item["recordId"]))["kind"] == "oracle-evaluation"))))
                record["key"]["evaluator"]["evaluatorId"] = "other-policy"; record["keyDigest"] = record["key"]["keyDigest"] = digest("k-in-k/oracle-evaluation-key/v1", without(record["key"], "keyDigest")); record["recordId"] = digest("k-in-k/cache-record/v1", without(record, "recordId"))
                self.expect_rejection(lambda record=record: self.bag14.validate_record(record), name)
            elif name in {"full-missing-test", "first-kill-fabricated-suffix", "baseline-failure-mutant-child", "missing-admission-before-mutant", "cross-campaign-comparison"}:
                root = full_root if name in {"full-missing-test", "baseline-failure-mutant-child", "missing-admission-before-mutant", "cross-campaign-comparison"} else first_root
                campaign, mappings = original_selection(root)
                if name == "full-missing-test": mappings.pop()
                elif name == "first-kill-fabricated-suffix":
                    slot = campaign["requestedPlan"][len(mappings)]; original = next(value for value in self.bag14.records.values() if value["keyDigest"] == slot["keyDigest"] and value["kind"] == slot["recordKind"]); mappings.append({"slotId": slot["slotId"], "recordId": original["recordId"]})
                elif name == "baseline-failure-mutant-child": mappings[0]["recordId"] = next(value["recordId"] for value in self.bag14.records.values() if value["terminalRecord"]["kind"] == "diagnostic-only")
                elif name == "missing-admission-before-mutant": mappings = [item for item in mappings if "baseline-gate" not in item["slotId"]]
                else:
                    target = next(index for index, item in enumerate(mappings) if "comparison" in item["slotId"]); mappings[target]["recordId"] = next(value["recordId"] for value in self.bag14.records.values() if value["kind"] == "oracle-evaluation" and value["recordId"] != mappings[target]["recordId"])
                self.expect_rejection(lambda campaign=campaign, mappings=mappings: self.bag14.derive_semantic_report(campaign, mappings), name)
            elif name == "result-in-own-invocation":
                bad = deepcopy(complete); bad["invocation"]["inputs"].append({"edgeRole": "key-artifact", "artifact": deepcopy(bad["outputs"][0]["artifact"])}); reject_edges(bad, name)
            elif name == "role-digest-arity-drift":
                bad = deepcopy(self.resolve(pattern["baselineExecutionReceipt"])); old_key = bad["outputs"][0]["artifact"]
                bad_wrapper = deepcopy(self.resolve(old_key)); bad_wrapper["producedArtifacts"].append(deepcopy(self.resolve(pattern["mutantExecutionResult"])["producedArtifacts"][1])); bad_wrapper["resultId"] = digest(RESULT_DOMAINS[old_key["role"]], without(bad_wrapper, "resultId")); new_key = key(old_key["role"], bad_wrapper["resultId"])
                bad["outputs"][0]["artifact"] = new_key; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId")); self.assets[(new_key["role"], new_key["digest"])] = bad_wrapper; self.entries[(new_key["role"], new_key["digest"])] = deepcopy(self.entries[(old_key["role"], old_key["digest"])])
                try: self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
                finally: self.assets.pop((new_key["role"], new_key["digest"])); self.entries.pop((new_key["role"], new_key["digest"]))
            elif name == "transform-role-drift":
                bad = deepcopy(pattern_operand); bad["invocation"]["inputs"][5]["artifact"] = deepcopy(pattern["mutantPatternResult"]); reject_edges(bad, name)
            elif name == "trace-other-invocation":
                bad = deepcopy(pattern_operand); mutant_operand = self.resolve(pattern["mutantOperandReceipt"]); bad["invocation"]["inputs"][3]["artifact"] = deepcopy(mutant_operand["invocation"]["inputs"][3]["artifact"]); reject_edges(bad, name)
            elif name in {"dangling-output", "surplus-child"}:
                bad = deepcopy(by_operation["campaign-derivation"])
                if name == "dangling-output": bad["invocation"]["inputs"].pop(3)
                else: bad["invocation"]["childReceipts"].append(deepcopy(bad["invocation"]["childReceipts"][-1]))
                reject_edges(bad, name)
            elif name == "refreshed-edge-drift":
                bad = deepcopy(by_operation["mutation-materialization"]); old_key = bad["outputs"][0]["artifact"]
                bad_wrapper = deepcopy(self.resolve(old_key)); bad_wrapper["outcome"]["mutantDefinition"] = key("mutant-definition", self.resolve(pattern["operands"][1])["subject"]["mutantDefinitionDigest"]); bad_wrapper["resultId"] = digest(RESULT_DOMAINS[old_key["role"]], without(bad_wrapper, "resultId")); new_key = key(old_key["role"], bad_wrapper["resultId"])
                bad["outputs"][0]["artifact"] = new_key; bad["semanticTerminal"] = deepcopy(bad_wrapper["outcome"]); bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId")); self.assets[(new_key["role"], new_key["digest"])] = bad_wrapper; self.entries[(new_key["role"], new_key["digest"])] = deepcopy(self.entries[(old_key["role"], old_key["digest"])])
                try: self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
                finally: self.assets.pop((new_key["role"], new_key["digest"])); self.entries.pop((new_key["role"], new_key["digest"]))
            elif name == "output-receipt-cycle":
                output_key = complete["outputs"][0]["artifact"]; bad_result = deepcopy(self.resolve(output_key)); bad_result["producedArtifacts"].append(key("operation-receipt", complete["receiptId"])); bad_result["resultId"] = digest(RESULT_DOMAINS[output_key["role"]], without(bad_result, "resultId")); self.validate_wrapper_identity(output_key["role"], bad_result, bad_result["resultId"])
                self.expect_rejection(lambda: self.validate_no_output_receipt_cycle(complete["receiptId"], bad_result), name)
            elif name == "receipt-as-execution-invocation":
                bad = deepcopy(pattern_operand); bad["invocation"]["parameters"]["executionInvocationDigest"] = bad["invocation"]["childReceipts"][0]["receipt"]["digest"]; reject_edges(bad, name)
            elif name == "admission-as-comparison":
                bad = deepcopy(self.resolve(pattern["comparisonReceipt"])); bad["invocation"]["childReceipts"][1] = {"edgeRole": "mutant-operand-production", "receipt": deepcopy(pattern["admissionReceipt"])}; reject_edges(bad, name)
            elif name == "complete-treated-as-normal":
                bad = deepcopy(self.resolve(self.vector["standaloneRoots"]["boundedExecution"])); bad["semanticTerminal"] = deepcopy(complete["semanticTerminal"]); bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId")); self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "campaign-layer-conflation":
                bad = deepcopy(by_operation["report-publication"]); bad["invocation"]["parameters"]["derivationResult"] = deepcopy(bad["invocation"]["parameters"]["versionRegistry"]); reject_edges(bad, name)
            elif name == "digest-only-receipt":
                bad = {"schemaVersion": 1, "receiptId": complete["receiptId"]}; self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "execution-key-invocation-conflation":
                bad = deepcopy(complete); bad["invocation"]["invocationDigest"] = bad["invocation"]["parameters"]["keyDigest"]; bad["invocationDigest"] = bad["invocation"]["invocationDigest"]; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "wrapper-terminal-drift":
                bad = deepcopy(self.resolve(self.vector["standaloneRoots"]["invalidMaterialization"]))
                old_key = bad["outputs"][0]["artifact"]
                bad_wrapper = deepcopy(self.resolve(old_key)); bad_wrapper["failure"] = None
                bad_wrapper["resultId"] = digest(RESULT_DOMAINS[old_key["role"]], without(bad_wrapper, "resultId"))
                new_key = key(old_key["role"], bad_wrapper["resultId"])
                bad["outputs"][0]["artifact"] = new_key; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.assets[(new_key["role"], new_key["digest"])] = bad_wrapper; self.entries[(new_key["role"], new_key["digest"])] = deepcopy(self.entries[(old_key["role"], old_key["digest"])])
                try: self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
                finally: self.assets.pop((new_key["role"], new_key["digest"])); self.entries.pop((new_key["role"], new_key["digest"]))
            elif name == "failed-producer-with-output":
                bad = deepcopy(failed); bad["outputs"] = deepcopy(complete["outputs"]); bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "wrong-output-role":
                bad = deepcopy(complete); bad["outputs"][0]["edgeRole"] = "campaign-derivation-result"; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "wrong-output-arity":
                bad = deepcopy(complete); bad["outputs"].append(deepcopy(bad["outputs"][0])); bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "unavailable-input":
                bad = deepcopy(complete); bad["invocation"]["inputs"][0]["artifact"]["digest"] = "f" * 64; self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "invalid-materialization-descendant":
                bad = deepcopy(self.resolve(self.vector["standaloneRoots"]["invalidMaterialization"])); bad["invocation"]["childReceipts"] = [{"edgeRole": "materialization-production", "receipt": deepcopy(pattern["baselineExecutionReceipt"])}]; reject_edges(bad, name)
            elif name == "cyclic-dag":
                root = deepcopy(self.vector["publicationRoots"][0]["publicationReceipt"])
                receipt_id = root["digest"]
                original = self.receipts[receipt_id]
                bad = deepcopy(original); bad["invocation"]["childReceipts"].append({"edgeRole": "derivation-production", "receipt": root})
                self.receipts[receipt_id] = bad
                try:
                    self.expect_rejection(lambda root=root: self.validate_dag(root), name)
                finally:
                    self.receipts[receipt_id] = original
            elif name in {"missing-schema-version", "extra-schema-version", "incorrect-schema-digest", "missing-operation-version", "surplus-operation-version"}:
                registry = deepcopy(self.resolve(next(iter(self.vector["publicationRoots"]))["report"]))
                registry = deepcopy(self.resolve(registry["versionRegistry"]))
                if name == "missing-schema-version": registry["schemas"].pop()
                elif name == "extra-schema-version": registry["schemas"].append({"schemaId": "artifact-catalog.schema.json", "schemaVersion": 1, "schemaDigest": raw_sha256((self.root / "schemas" / "artifact-catalog.schema.json").read_bytes())})
                elif name == "incorrect-schema-digest": registry["schemas"][0]["schemaDigest"] = "f" * 64
                elif name == "missing-operation-version": registry["operations"].pop()
                else: registry["operations"].append({"operationKind": "execution-attempt", "operationVersion": 1})
                registry["schemas"] = sorted(registry["schemas"], key=lambda item: (item["schemaId"], item["schemaVersion"]))
                registry["operations"] = sorted(registry["operations"], key=lambda item: (item["operationKind"], item["operationVersion"]))
                registry["registryId"] = digest("k-in-k/replay-version-registry/v1", without(registry, "registryId"))
                root = self.vector["publicationRoots"][0]
                closure = self.validate_dag(root["publicationReceipt"])
                self.expect_rejection(lambda registry=registry, root=root, closure=closure: self.validate_registry(registry, root["report"], closure), name)
            elif name == "publication-expected-body-input":
                publication = next(value for value in self.receipts.values() if value["invocation"]["operationKind"] == "report-publication")
                bad = deepcopy(publication); bad["invocation"]["parameters"]["expectedBody"] = {}; bad["invocation"]["invocationDigest"] = digest("k-in-k/operation-invocation/v1", without(bad["invocation"], "invocationDigest")); bad["invocationDigest"] = bad["invocation"]["invocationDigest"]; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId"))
                self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "complete-failure-without-wrapper":
                bad = deepcopy(self.resolve(self.vector["standaloneRoots"]["invalidMaterialization"])); bad["producerStatus"] = "failed"; bad["producer"]["executionConformance"] = "not-proven"; bad["outputs"] = []; bad["semanticTerminal"] = None; bad["receiptId"] = digest("k-in-k/operation-receipt/v1", without(bad, "receiptId")); self.expect_rejection(lambda bad=bad: self.validate_receipt(bad), name)
            elif name == "report-self-publication-receipt":
                report_key = first_root["report"]; original_report = self.assets[(report_key["role"], report_key["digest"])]; bad_report = deepcopy(original_report); bad_report["publicationReceipt"] = deepcopy(first_root["publicationReceipt"]); self.assets[(report_key["role"], report_key["digest"])] = bad_report
                try: self.expect_rejection(lambda: self.validate_report_root(first_root), name)
                finally: self.assets[(report_key["role"], report_key["digest"])] = original_report
            else:
                raise AssertionError(f"BAG-15 advertised adversary has no bespoke semantic mutation: {name}")

    def run(self) -> None:
        # Revalidate every active declaration through BAG-12's complete
        # six-kind dispatcher before any BAG-15 operand/comparison evidence.
        for declaration in self.oracle.declarations.values():
            self.oracle.validate_declaration(declaration)
        for (role, identity), value in self.assets.items():
            if role in RESULT_DOMAINS:
                self.validate_wrapper_identity(role, value, identity)
        for value in self.receipts.values():
            self.validate_receipt(value)
        for (role, _), record in self.assets.items():
            if role == "cache-record" and record["productionEvidence"]["mode"] == "operation-receipt":
                self.bag14.validate_record(record)
        roots = self.vector["publicationRoots"]
        self.ok([item["scheduleMode"] for item in roots] == ["first-kill", "full"], "BAG-15 publication roots missing/reordered")
        for root in roots:
            self.validate_report_root(root)
        invalid = self.resolve(self.vector["standaloneRoots"]["invalidMaterialization"])
        self.ok(invalid["semanticTerminal"]["kind"] == "invalid" and invalid["outputs"] and not invalid["invocation"]["childReceipts"], "BAG-15 invalid materialization is not a terminal wrapper-only root")
        bounded = self.resolve(self.vector["standaloneRoots"]["boundedExecution"])
        self.ok(bounded["producerStatus"] == "complete" and bounded["semanticTerminal"]["kind"] == "bounded-stop" and bounded["outputs"], "BAG-15 bounded execution was confused with producer failure")
        matrix = self.vector["producerStateMatrix"]
        self.ok([item["state"] for item in matrix] == ["complete-semantic-success", "complete-semantic-failure", "complete-bounded", "complete-diagnostic", "failed-producer"], "BAG-15 producer state matrix drift")
        for item in matrix:
            value = self.resolve(item["receipt"])
            self.ok(bool(value["outputs"]) == item["hasWrapper"] and (value["producerStatus"] == "failed") == (item["state"] == "failed-producer"), "BAG-15 producer matrix conflates completion and semantic result")
        pattern = self.vector["patternEvidence"]
        pattern_declaration = self.oracle.resolve_json(pattern["declaration"])
        self.oracle.validate_declaration(pattern_declaration)
        pattern_comparison = self.oracle.resolve_json(pattern["comparison"])
        self.ok(pattern["operands"] == [side["normalOperand"] for side in pattern_comparison["sides"]], "BAG-15 pattern comparison operand order drift")
        self.oracle.validate_comparison(pattern_comparison)
        for field in ("baselineExecutionReceipt", "mutantExecutionReceipt", "baselineOperandReceipt", "mutantOperandReceipt", "admissionReceipt", "comparisonReceipt"):
            self.validate_receipt(self.resolve(pattern[field]))
        for side in ("baseline", "mutant"):
            execution_receipt = self.resolve(pattern[f"{side}ExecutionReceipt"])
            operand_receipt = self.resolve(pattern[f"{side}OperandReceipt"])
            self.ok(execution_receipt["outputs"][0]["artifact"] == pattern[f"{side}ExecutionResult"], "BAG-15 pattern execution receipt/result drift")
            self.ok(operand_receipt["outputs"][0]["artifact"] == pattern[f"{side}OperandResult"] and self.resolve(pattern[f"{side}OperandResult"])["outcome"] == {"kind": "operand", "operand": pattern["operands"][0 if side == "baseline" else 1]}, "BAG-15 pattern operand receipt/result drift")
        pattern_admission = self.resolve(pattern["admissionReceipt"])
        pattern_comparison_receipt = self.resolve(pattern["comparisonReceipt"])
        pattern_gate_key = pattern_admission["semanticTerminal"]["result"]
        self.oracle.validate_gate(self.oracle.resolve_json(pattern_gate_key))
        self.ok(pattern_admission["outputs"][0]["artifact"] == pattern["admissionResult"], "BAG-15 pattern admission wrapper/receipt drift")
        self.ok(pattern_comparison_receipt["outputs"][0]["artifact"] == pattern["comparisonResult"] and pattern_comparison_receipt["semanticTerminal"] == {"kind": "comparison", "result": pattern["comparison"]}, "BAG-15 pattern comparison is not the exact active BAG-12 result")
        for field, fixture_name, domain, id_field in (
            ("baselineReplay", "bag12-baseline-pattern-replay.json", "k-in-k/replay-manifest/v1", "replayId"),
            ("mutantReplay", "bag12-mutant-pattern-replay.json", "k-in-k/replay-manifest/v1", "replayId"),
            ("baselinePatternResult", "bag12-baseline-pattern-result.json", "k-in-k/pattern-result/v1", "resultId"),
            ("mutantPatternResult", "bag12-mutant-pattern-result.json", "k-in-k/pattern-result/v1", "resultId"),
        ):
            value = read_json(self.fixtures / fixture_name)
            self.ok(pattern[field]["digest"] == value[id_field] == digest(domain, without(value, id_field)), "BAG-15 execution-pattern evidence drift")
        ordinary = self.vector["ordinaryFinalEvidence"]
        ordinary_comparison = self.resolve(ordinary["comparisonReceipt"])
        ordinary_admission = self.resolve(ordinary["admissionReceipt"])
        self.ok(ordinary_comparison["semanticTerminal"] == {"kind": "comparison", "result": ordinary["comparison"]}, "BAG-15 ordinary comparison receipt names another final-result comparison")
        self.ok(ordinary_admission["invocation"]["parameters"]["evaluationKey"]["declaration"] == ordinary["declaration"], "BAG-15 ordinary admission belongs to another declaration")
        for side in ("baseline", "mutant"):
            execution_receipt = self.resolve(ordinary[f"{side}ExecutionReceipt"])
            operand_receipt = self.resolve(ordinary[f"{side}OperandReceipt"])
            self.ok(execution_receipt["outputs"][0]["artifact"] == ordinary[f"{side}ExecutionResult"], "BAG-15 ordinary execution result lacks its exact receipt")
            self.ok(operand_receipt["outputs"][0]["artifact"] == ordinary[f"{side}OperandResult"] and self.resolve(ordinary[f"{side}OperandResult"])["outcome"] == {"kind": "operand", "operand": ordinary[f"{side}Operand"]}, "BAG-15 ordinary final operand lacks its exact producing attempt")
        self.adversaries()


def new_official_fixtures(root: Path) -> dict[str, str]:
    fixtures = root / "fixtures"
    result = {"bag15-replay-artifact-catalog.json": "artifact-catalog.schema.json", "bag15-replay-version-registry.json": "replay-version-registry.schema.json"}
    for path in fixtures.glob("bag15-*.json"):
        name = path.name
        if name in result or name.startswith("bag15-cache-record-"):
            if name.startswith("bag15-cache-record-"):
                result[name] = "cache-semantics.schema.json"
            continue
        value = read_json(path)
        if "receiptId" in value:
            result[name] = "operation-receipt.schema.json"
        elif "resultId" in value:
            role = next((role for role, specification in role_specs().items() if specification.get("selfIdField") == "resultId" and digest(specification["digestDomain"], without(value, "resultId")) == value["resultId"]), None)
            if role:
                result[name] = f"{role}.schema.json"
        elif "reportId" in value:
            result[name] = "provenance-mutation-report.schema.json"
        elif "diffId" in value:
            result[name] = "structural-diff.schema.json"
    return result


def verify_package(root: Path, api: dict[str, Any]) -> None:
    ReceiptVerifier(root, api).run()
