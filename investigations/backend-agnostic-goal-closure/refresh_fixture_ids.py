#!/usr/bin/env python3
"""Refresh the acyclic digest graph for the portable example fixtures.

This is fixture maintenance only: it never invokes K or a backend.
"""

from __future__ import annotations

import hashlib
import json
import sys
import unicodedata
from copy import deepcopy
from itertools import product
from pathlib import Path
from types import ModuleType
from typing import Any

from bag12 import finalize_refresh as finalize_bag12_refresh
from bag12 import prepare_refresh as prepare_bag12_refresh
from bag14 import finalize_refresh as finalize_bag14_refresh


ROOT = Path(__file__).resolve().parent
FIXTURES = ROOT / "fixtures"
MATERIAL = ROOT / "material"
REPOSITORY = ROOT.parents[1]

BAG10_CONTEXTS = [
    "observation-installation", "mutation-discovery", "candidate-generation",
    "pattern-path", "pattern-test", "corpus-shared-setup", "baseline-validation",
    "baseline-execution", "baseline-oracle-gate", "mutant-validation",
    "mutant-execution", "oracle-operand-production", "oracle-comparison", "campaign", "report-publication",
]


def bag10_failure_context(failure: dict[str, Any], path: str = "") -> str:
    stage, scope, classification = failure["stage"], failure["scope"], failure["classification"]
    if "discovery/failure" in path:
        return "mutation-discovery"
    if "candidateRejections" in path or "/generation/" in path or stage in {"operator", "selection", "patch"}:
        return "candidate-generation"
    if scope == "path":
        return "pattern-path"
    if scope == "test":
        return "observation-installation" if stage == "observation" else "pattern-test"
    if classification == "baseline-mismatch":
        return "baseline-oracle-gate"
    if scope == "mutant":
        if stage == "lowering" and classification in {"time-limit", "resource-limit"}:
            return "mutant-execution"
        return "mutant-validation" if stage in {"ir-validation", "lowering", "backend-validation"} else "mutant-execution"
    if stage == "backend-validation":
        return "baseline-validation"
    if stage in {"infrastructure", "execution"} and "baseline" in path:
        return "baseline-execution"
    if stage == "oracle":
        if classification in {"projection-invalid", "evaluator-unavailable"}:
            return "oracle-operand-production"
        return "oracle-comparison"
    if stage == "report":
        return "report-publication"
    if stage == "input":
        return "corpus-shared-setup"
    return "campaign"


def migrate_bag10_value(value: Any, path: str = "$") -> None:
    if isinstance(value, dict):
        if {"stage", "classification", "scope", "retryability", "details"} <= value.keys() and isinstance(value["stage"], str):
            value["context"] = bag10_failure_context(value, path)
            value["semanticEvidence"] = value.get("semanticEvidence", [])
        if "source" in value and "failure" in value and set(value) <= {"source", "sourceSide", "failure"}:
            value["sourceSide"] = value.pop("source")
        for key, item in list(value.items()):
            migrate_bag10_value(item, f"{path}/{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            migrate_bag10_value(item, f"{path}/{index}")


def migrate_bag10_inputs() -> None:
    for base in (FIXTURES, ROOT / "vectors"):
        for path in sorted(base.glob("*.json")):
            value = json.loads(path.read_text(encoding="utf-8"))
            migrate_bag10_value(value)
            path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def bag10_entries() -> list[dict[str, Any]]:
    stages = {
        "input": ["malformed", "unsupported-version", "missing-artifact", "digest-mismatch"],
        "operator": ["malformed-operator", "unsupported-phase", "unsupported-sentence-kind", "no-change"],
        "selection": ["cardinality-mismatch", "incomplete-generation", "duplicate-site", "invalid-join"],
        "patch": ["stale-precondition", "malformed-path", "unsupported-operation", "duplicate-target", "overlapping-edit", "invalid-position", "no-change"],
        "ir-validation": ["ill-sorted", "invalid-module", "invalid-import", "invalid-variable", "invalid-attribute", "invalid-sentence"],
        "lowering": ["lowering-rejected", "lowering-nontermination", "unsupported-lowering", "time-limit", "resource-limit"],
        "backend-validation": ["compile-rejected", "unsupported-backend-profile"],
        "execution": ["depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown", "backend-error"],
        "observation": ["unsupported-observation-shape", "non-conservative-observation", "provenance-mismatch", "malformed-event"],
        "pattern": ["malformed-pattern", "sort-mismatch", "invalid-side-condition", "malformed-result", "unreplayable-witness"],
        "oracle": ["baseline-mismatch", "malformed-oracle", "projection-invalid", "evaluator-unavailable", "incomparable-result"],
        "infrastructure": ["process-launch", "io", "artifact-corruption", "worker-lost", "internal"],
        "report": ["schema-violation", "canonicalization-failure", "referential-integrity"],
    }
    context_order = {name: index for index, name in enumerate(BAG10_CONTEXTS)}
    scope_order = {name: index for index, name in enumerate(["candidate", "mutant", "path", "test", "campaign"])}

    def placement(context: str, scope: str, disposition: str) -> dict[str, Any]:
        return {"context": context, "scope": scope, "consequence": {"disposition": disposition}}

    result = []
    resource_retry = {"depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown"}
    external_retry = {"process-launch", "io", "worker-lost"}
    for stage, classifications in stages.items():
        for classification in classifications:
            if stage == "input":
                placements = [placement("corpus-shared-setup", "campaign", "error")]
                if classification == "missing-artifact":
                    placements.append(placement("oracle-operand-production", "test", "error"))
            elif stage == "operator":
                placements = [placement("candidate-generation", "candidate", "rejected")]
            elif stage == "selection":
                if classification == "incomplete-generation":
                    placements = [placement("mutation-discovery", "campaign", "incomplete-generation"), placement("candidate-generation", "campaign", "incomplete-generation")]
                elif classification in {"cardinality-mismatch", "invalid-join"}:
                    placements = [placement("candidate-generation", "campaign", "selection-failed")]
                else:
                    placements = [placement("candidate-generation", "candidate", "rejected")]
            elif stage == "patch":
                placements = [placement("candidate-generation", "candidate", "rejected")]
            elif stage == "ir-validation":
                placements = [placement("mutant-validation", "mutant", "invalid")]
            elif stage == "lowering":
                disposition = "timeout" if classification == "time-limit" else "unknown" if classification == "resource-limit" else "invalid"
                placements = [placement("mutant-validation", "mutant", disposition)]
                if classification in {"time-limit", "resource-limit"}:
                    placements.append(placement("mutant-execution", "mutant", disposition))
                if classification == "lowering-nontermination":
                    placements.insert(0, placement("baseline-validation", "campaign", "baseline-invalid"))
            elif stage == "backend-validation":
                placements = [placement("baseline-validation", "campaign", "baseline-invalid"), placement("mutant-validation", "mutant", "invalid")]
            elif stage == "execution":
                pattern_outcome = "error" if classification == "backend-error" else "unknown"
                mutant_outcome = "timeout" if classification == "time-limit" else "error" if classification == "backend-error" else "unknown"
                placements = [placement("pattern-path", "path", pattern_outcome), placement("pattern-test", "test", pattern_outcome), placement("mutant-execution", "mutant", mutant_outcome)]
                if classification == "solver-unknown":
                    placements.append(placement("oracle-operand-production", "test", "unknown"))
            elif stage == "observation":
                placements = [placement("observation-installation", "test", "error")]
            elif stage == "pattern":
                placements = [placement("pattern-test", "test", "error")]
            elif stage == "oracle":
                if classification == "baseline-mismatch":
                    placements = [placement("baseline-oracle-gate", "campaign", "baseline-oracle-failed")]
                elif classification == "projection-invalid":
                    placements = [placement("oracle-operand-production", "test", "error")]
                elif classification == "evaluator-unavailable":
                    placements = [placement("oracle-operand-production", "test", "unknown")]
                else:
                    placements = [placement("oracle-comparison", "mutant", "error")]
            elif stage == "infrastructure":
                placements = [placement("baseline-execution", "campaign", "baseline-invalid"), placement("mutant-execution", "mutant", "error")]
                if classification == "internal":
                    placements.append(placement("campaign", "campaign", "error"))
            else:
                placements = [placement("report-publication", "campaign", "unpublishable-report")]
            placements.sort(key=lambda item: (context_order[item["context"]], scope_order[item["scope"]]))
            retryability = "same-input-after-resource-change" if classification in resource_retry else "after-external-repair" if classification in external_retry else "never"
            result.append({
                "stage": stage, "classification": classification, "retryability": retryability,
                "placements": placements,
                "evidencePolicy": "checked-lowering-cycle-receipt-v1" if stage == "lowering" and classification == "lowering-nontermination" else "none",
            })
    return result


def write_bag10_contract() -> None:
    entries = bag10_entries()
    taxonomy = {"schemaVersion": 1, "detailsPolicy": "diagnostic-only", "entries": entries}
    taxonomy["taxonomyId"] = digest("k-in-k/failure-taxonomy/v1", taxonomy)
    (ROOT / "failure-taxonomy.json").write_text(json.dumps(taxonomy, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    stages = list(dict.fromkeys(entry["stage"] for entry in entries))
    classifications = list(dict.fromkeys(entry["classification"] for entry in entries))
    dispositions = ["rejected", "selection-failed", "incomplete-generation", "baseline-invalid", "baseline-oracle-failed", "invalid", "timeout", "unknown", "error", "unpublishable-report"]
    taxonomy_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema", "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/failure-taxonomy.schema.json",
        "type": "object", "additionalProperties": False,
        "required": ["schemaVersion", "taxonomyId", "detailsPolicy", "entries"],
        "properties": {"schemaVersion": {"const": 1}, "taxonomyId": {"$ref": "common.schema.json#/$defs/digest"}, "detailsPolicy": {"const": "diagnostic-only"}, "entries": {"type": "array", "minItems": 1, "items": {"$ref": "#/$defs/entry"}}},
        "$defs": {
            "consequence": {"oneOf": [
                {"type": "object", "additionalProperties": False, "required": ["disposition"], "properties": {"disposition": {"enum": dispositions}}},
                {"type": "object", "additionalProperties": False, "required": ["delegation"], "properties": {"delegation": {"enum": ["generation-completeness-policy-v1"]}}},
            ]},
            "entry": {"type": "object", "additionalProperties": False, "required": ["stage", "classification", "retryability", "placements", "evidencePolicy"], "properties": {
                "stage": {"enum": stages}, "classification": {"enum": classifications}, "retryability": {"enum": ["never", "same-input-after-resource-change", "after-external-repair"]},
                "placements": {"type": "array", "minItems": 1, "items": {"type": "object", "additionalProperties": False, "required": ["context", "scope", "consequence"], "properties": {"context": {"enum": BAG10_CONTEXTS}, "scope": {"enum": ["candidate", "mutant", "path", "test", "campaign"]}, "consequence": {"$ref": "#/$defs/consequence"}}}},
                "evidencePolicy": {"enum": ["none", "checked-lowering-cycle-receipt-v1"]},
            }},
        },
    }
    (ROOT / "schemas" / "failure-taxonomy.schema.json").write_text(json.dumps(taxonomy_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    common_path = ROOT / "schemas" / "common.schema.json"
    common = json.loads(common_path.read_text(encoding="utf-8"))
    roles = common["$defs"]["artifactRole"]["enum"]
    for role in ["failure-taxonomy", "lowering-cycle-proof", "lowering-profile", "lowering-proof-check-receipt"]:
        if role not in roles:
            roles.append(role)
    roles.sort()
    failure = common["$defs"]["failure"]
    failure["required"] = ["stage", "classification", "context", "scope", "retryability", "semanticEvidence", "details"]
    failure["properties"]["classification"] = {"type": "string", "enum": classifications}
    failure["properties"]["context"] = {"enum": BAG10_CONTEXTS}
    failure["properties"]["semanticEvidence"] = {"type": "array", "uniqueItems": True, "items": {"$ref": "#/$defs/artifactKey"}}
    evidence_rule = {"if": {"properties": {"stage": {"const": "lowering"}, "classification": {"const": "lowering-nontermination"}}, "required": ["stage", "classification"]}, "then": {"properties": {"semanticEvidence": {"minItems": 1, "maxItems": 1, "items": {"type": "object", "additionalProperties": False, "required": ["role", "digest"], "properties": {"role": {"const": "lowering-proof-check-receipt"}, "digest": {"$ref": "#/$defs/digest"}}}}}}, "else": {"properties": {"semanticEvidence": {"maxItems": 0}}}}
    ordered_stages = list(dict.fromkeys(entry["stage"] for entry in entries))
    failure_pair_union = {"oneOf": [
        {"properties": {"stage": {"const": stage}, "classification": {"enum": [entry["classification"] for entry in entries if entry["stage"] == stage]}}}
        for stage in ordered_stages
    ]}
    failure["allOf"] = [failure_pair_union, evidence_rule]
    def_name = {context: "".join([context.split("-")[0], *[part.title() for part in context.split("-")[1:]]]) + "Failure" for context in BAG10_CONTEXTS}
    for context in BAG10_CONTEXTS:
        variants = []
        for entry in entries:
            for item in entry["placements"]:
                if item["context"] == context:
                    variants.append({"type": "object", "properties": {"stage": {"const": entry["stage"]}, "classification": {"const": entry["classification"]}, "context": {"const": context}, "scope": {"const": item["scope"]}, "retryability": {"const": entry["retryability"]}}, "required": ["stage", "classification", "context", "scope", "retryability"]})
        common["$defs"][def_name[context]] = {"allOf": [{"$ref": "#/$defs/failure"}, {"oneOf": variants}]}
    common_path.write_text(json.dumps(common, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    schema_dir = ROOT / "schemas"
    def set_ref(document: dict[str, Any], path: list[str], reference: str) -> None:
        value: Any = document
        for key in path[:-1]: value = value[int(key)] if isinstance(value, list) else value[key]
        if isinstance(value, list):
            value[int(path[-1])] = {"$ref": reference}
        else:
            value[path[-1]] = {"$ref": reference}
    ref_changes = {
        "observation-installation-result.schema.json": [(["properties", "failures", "items"], "common.schema.json#/$defs/observationInstallationFailure")],
        "pattern-result.schema.json": [(["properties", "failures", "items"], "common.schema.json#/$defs/patternTestFailure"), (["$defs", "pathResult", "properties", "failures", "items"], "common.schema.json#/$defs/patternPathFailure")],
        "corpus-result.schema.json": [(["properties", "failures", "items"], "common.schema.json#/$defs/corpusSharedSetupFailure"), (["properties", "components", "items", "properties", "failures", "items"], "common.schema.json#/$defs/patternTestFailure"), (["properties", "components", "items", "properties", "pathResults", "items", "properties", "failures", "items"], "common.schema.json#/$defs/patternPathFailure")],
        "mutation-site-registry.schema.json": [(["properties", "discovery", "properties", "failure", "oneOf", "1"], "common.schema.json#/$defs/mutationDiscoveryFailure")],
        "mutation-campaign.schema.json": [(["properties", "failures", "items"], "#/$defs/campaignFailure"), (["properties", "generation", "properties", "failures", "items"], "common.schema.json#/$defs/candidateGenerationFailure"), (["properties", "baseline", "properties", "failures", "items"], "#/$defs/baselineFailure"), (["$defs", "candidateRejection", "properties", "failures", "items"], "common.schema.json#/$defs/candidateGenerationFailure"), (["$defs", "mutant", "properties", "failures", "items"], "#/$defs/mutantFailure")],
    }
    for name, changes in ref_changes.items():
        path = schema_dir / name
        document = json.loads(path.read_text(encoding="utf-8"))
        for pointer_path, reference in changes: set_ref(document, pointer_path, reference)
        if name == "mutation-campaign.schema.json":
            document["$defs"].update({
                "campaignFailure": {"oneOf": [{"$ref": "common.schema.json#/$defs/campaignFailure"}, {"$ref": "common.schema.json#/$defs/reportPublicationFailure"}]},
                "baselineFailure": {"oneOf": [{"$ref": "common.schema.json#/$defs/baselineValidationFailure"}, {"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}, {"$ref": "common.schema.json#/$defs/baselineOracleGateFailure"}]},
                "mutantFailure": {"oneOf": [{"$ref": "common.schema.json#/$defs/mutantValidationFailure"}, {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}]},
                "oracleContextFailure": {"oneOf": [{"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}, {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}, {"$ref": "common.schema.json#/$defs/baselineOracleGateFailure"}, {"$ref": "common.schema.json#/$defs/oracleComparisonFailure"}]},
            })
            if "oracleFailure" in document["$defs"]:
                document["$defs"]["oracleFailure"]["required"] = ["sourceSide", "failure"]
                document["$defs"]["oracleFailure"]["properties"].pop("source", None)
                document["$defs"]["oracleFailure"]["properties"]["sourceSide"] = {"enum": ["baseline-execution", "mutant-execution", "comparison"]}
                document["$defs"]["oracleFailure"]["properties"]["failure"] = {"$ref": "#/$defs/oracleContextFailure"}
                document["$defs"]["oracleFailure"]["oneOf"] = [
                    {"properties": {"sourceSide": {"const": "baseline-execution"}, "failure": {"$ref": "common.schema.json#/$defs/baselineExecutionFailure"}}, "required": ["sourceSide", "failure"]},
                    {"properties": {"sourceSide": {"const": "mutant-execution"}, "failure": {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"}}, "required": ["sourceSide", "failure"]},
                    {"properties": {"sourceSide": {"const": "comparison"}, "failure": {"oneOf": [{"$ref": "common.schema.json#/$defs/baselineOracleGateFailure"}, {"$ref": "common.schema.json#/$defs/oracleComparisonFailure"}]}}, "required": ["sourceSide", "failure"]},
                ]
        path.write_text(json.dumps(document, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    manifest_path = schema_dir / "mutation-manifest.schema.json"
    manifest_schema = json.loads(manifest_path.read_text(encoding="utf-8"))
    if "loweringProfileDigest" not in manifest_schema["required"]: manifest_schema["required"].insert(7, "loweringProfileDigest")
    if "loweringEvidence" not in manifest_schema["required"]: manifest_schema["required"].insert(8, "loweringEvidence")
    manifest_schema["properties"]["loweringProfileDigest"] = {"$ref": "common.schema.json#/$defs/digest"}
    manifest_schema["properties"]["loweringEvidence"] = {"type": "array", "uniqueItems": True, "items": {"oneOf": [
        {"type": "object", "additionalProperties": False, "required": ["role", "digest"], "properties": {"role": {"const": "lowering-cycle-proof"}, "digest": {"$ref": "common.schema.json#/$defs/digest"}}},
        {"type": "object", "additionalProperties": False, "required": ["role", "digest"], "properties": {"role": {"const": "lowering-proof-check-receipt"}, "digest": {"$ref": "common.schema.json#/$defs/digest"}}},
    ]}}
    manifest_path.write_text(json.dumps(manifest_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    roles_path = ROOT / "artifact-role-specs.json"
    registry = json.loads(roles_path.read_text(encoding="utf-8"))
    by_role = {item["role"]: item for item in registry["specs"]}
    by_role.update({
        "failure-taxonomy": {"role": "failure-taxonomy", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "failure-taxonomy.schema.json", "digestDomain": "k-in-k/failure-taxonomy/v1", "projection": {"kind": "without-field"}, "selfIdField": "taxonomyId"},
        "lowering-cycle-proof": {"role": "lowering-cycle-proof", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "lowering-cycle-proof.schema.json", "digestDomain": "k-in-k/lowering-cycle-proof/v1", "projection": {"kind": "without-field"}, "selfIdField": "proofId"},
        "lowering-profile": {"role": "lowering-profile", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        "lowering-proof-check-receipt": {"role": "lowering-proof-check-receipt", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "lowering-proof-check-receipt.schema.json", "digestDomain": "k-in-k/lowering-proof-check-receipt/v1", "projection": {"kind": "without-field"}, "selfIdField": "receiptId"},
    })
    registry["specs"] = [by_role[key] for key in sorted(by_role)]
    roles_path.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    subject = {"oneOf": [
        {"type": "object", "additionalProperties": False, "required": ["role", "definitionDigest"], "properties": {"role": {"const": "baseline"}, "definitionDigest": {"$ref": "common.schema.json#/$defs/digest"}}},
        {"type": "object", "additionalProperties": False, "required": ["role", "baselineDefinitionDigest", "mutantId", "mutantDefinitionDigest"], "properties": {"role": {"const": "mutant"}, "baselineDefinitionDigest": {"$ref": "common.schema.json#/$defs/digest"}, "mutantId": {"$ref": "common.schema.json#/$defs/digest"}, "mutantDefinitionDigest": {"$ref": "common.schema.json#/$defs/digest"}}},
    ]}
    proof_schema = {"$schema": "https://json-schema.org/draft/2020-12/schema", "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/lowering-cycle-proof.schema.json", "type": "object", "additionalProperties": False, "required": ["schemaVersion", "proofId", "proofKind", "subject", "loweringProfileDigest", "executionProfileDigest", "relationId", "cycleStates"], "properties": {"schemaVersion": {"const": 1}, "proofId": {"$ref": "common.schema.json#/$defs/digest"}, "proofKind": {"const": "finite-cycle-witness-v1"}, "subject": {"$ref": "#/$defs/subject"}, "loweringProfileDigest": {"$ref": "common.schema.json#/$defs/digest"}, "executionProfileDigest": {"$ref": "common.schema.json#/$defs/digest"}, "relationId": {"$ref": "common.schema.json#/$defs/digest"}, "cycleStates": {"type": "array", "minItems": 3, "items": {"type": "string", "minLength": 1}}}, "$defs": {"subject": subject}}
    receipt_schema = {"$schema": "https://json-schema.org/draft/2020-12/schema", "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/lowering-proof-check-receipt.schema.json", "type": "object", "additionalProperties": False, "required": ["schemaVersion", "receiptId", "checkerId", "checkerVersion", "proof", "subject", "loweringProfileDigest", "executionProfileDigest", "relationId", "checkedResult"], "properties": {"schemaVersion": {"const": 1}, "receiptId": {"$ref": "common.schema.json#/$defs/digest"}, "checkerId": {"const": "portable-finite-cycle-checker"}, "checkerVersion": {"const": 1}, "proof": {"type": "object", "additionalProperties": False, "required": ["role", "digest"], "properties": {"role": {"const": "lowering-cycle-proof"}, "digest": {"$ref": "common.schema.json#/$defs/digest"}}}, "subject": {"$ref": "lowering-cycle-proof.schema.json#/$defs/subject"}, "loweringProfileDigest": {"$ref": "common.schema.json#/$defs/digest"}, "executionProfileDigest": {"$ref": "common.schema.json#/$defs/digest"}, "relationId": {"$ref": "common.schema.json#/$defs/digest"}, "checkedResult": {"const": "nontermination-confirmed"}}}
    (schema_dir / "lowering-cycle-proof.schema.json").write_text(json.dumps(proof_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (schema_dir / "lowering-proof-check-receipt.schema.json").write_text(json.dumps(receipt_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def write_lowering_proof_vectors(definition: dict[str, Any], campaign: dict[str, Any], lowering_profile_digest: str, execution_profile_digest: str) -> None:
    relation = {"states": ["lowering-a", "lowering-b"], "edges": [["lowering-a", "lowering-b"], ["lowering-b", "lowering-a"]]}
    relation_id = digest("k-in-k/frozen-lowering-relation/v1", relation)
    baseline_subject = {"role": "baseline", "definitionDigest": definition["definitionDigest"]}
    mutant = campaign["mutants"][0]
    mutant_subject = {"role": "mutant", "baselineDefinitionDigest": definition["definitionDigest"], "mutantId": mutant["mutantId"], "mutantDefinitionDigest": mutant["outputDefinitionDigest"]}
    artifacts = []
    cases = []
    for name, subject in (("baseline-cycle", baseline_subject), ("mutant-cycle", mutant_subject)):
        proof = {"schemaVersion": 1, "proofKind": "finite-cycle-witness-v1", "subject": subject, "loweringProfileDigest": lowering_profile_digest, "executionProfileDigest": execution_profile_digest, "relationId": relation_id, "cycleStates": ["lowering-a", "lowering-b", "lowering-a"]}
        proof["proofId"] = digest("k-in-k/lowering-cycle-proof/v1", proof)
        receipt = {"schemaVersion": 1, "checkerId": "portable-finite-cycle-checker", "checkerVersion": 1, "proof": {"role": "lowering-cycle-proof", "digest": proof["proofId"]}, "subject": subject, "loweringProfileDigest": lowering_profile_digest, "executionProfileDigest": execution_profile_digest, "relationId": relation_id, "checkedResult": "nontermination-confirmed"}
        receipt["receiptId"] = digest("k-in-k/lowering-proof-check-receipt/v1", receipt)
        artifacts.extend([{"key": {"role": "lowering-cycle-proof", "digest": proof["proofId"]}, "value": proof}, {"key": {"role": "lowering-proof-check-receipt", "digest": receipt["receiptId"]}, "value": receipt}])
        save(f"{name}-lowering-cycle-proof.json", proof)
        save(f"{name}-lowering-proof-check-receipt.json", receipt)
        cases.append({"id": name, "subjectRole": subject["role"], "proofKey": {"role": "lowering-cycle-proof", "digest": proof["proofId"]}, "receiptKey": {"role": "lowering-proof-check-receipt", "digest": receipt["receiptId"]}})
    mutant_receipt = next(case["receiptKey"] for case in cases if case["subjectRole"] == "mutant")
    failure = {"stage": "lowering", "classification": "lowering-nontermination", "context": "mutant-validation", "scope": "mutant", "retryability": "never", "semanticEvidence": [mutant_receipt], "details": {}}
    vector = {"schemaVersion": 1, "checkerRegistry": [{"checkerId": "portable-finite-cycle-checker", "checkerVersion": 1, "proofKind": "finite-cycle-witness-v1", "relationId": relation_id}], "frozenRelation": relation, "relationId": relation_id, "artifacts": artifacts, "cases": cases, "authorizedFailure": failure}
    (ROOT / "vectors" / "lowering-proof-vectors.json").write_text(json.dumps(vector, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    status_path = ROOT / "vectors" / "mutation-status-vectors.json"
    status_vectors = json.loads(status_path.read_text(encoding="utf-8"))
    migrate_bag10_value(status_vectors)
    for section in ("cases", "statusContradictionCases"):
        for case in status_vectors[section]:
            if case.get("failure", {}).get("classification") == "lowering-nontermination":
                case["failure"]["semanticEvidence"] = [deepcopy(mutant_receipt)]
    status_path.write_text(json.dumps(status_vectors, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def load(name: str) -> dict[str, Any]:
    return json.loads((FIXTURES / name).read_text(encoding="utf-8"))


def save(name: str, value: dict[str, Any]) -> None:
    (FIXTURES / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def digest(domain: str, value: Any) -> str:
    payload = unicodedata.normalize("NFC", domain).encode() + b"\0" + unicodedata.normalize("NFC", canonical(value)).encode()
    return hashlib.sha256(payload).hexdigest()


def raw_sha256(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def artifact_key_schema(role: str) -> dict[str, Any]:
    return {
        "type": "object", "additionalProperties": False,
        "required": ["role", "digest"],
        "properties": {"role": {"const": role}, "digest": {"$ref": "common.schema.json#/$defs/digest"}},
    }


def nullable_artifact_key_schema(role: str) -> dict[str, Any]:
    return {"oneOf": [artifact_key_schema(role), {"type": "null"}]}


def pattern_query_root_schema() -> dict[str, Any]:
    return {
        "type": "object", "additionalProperties": False,
        "required": ["patternSource", "patternPlan", "patternQuery"],
        "properties": {
            "patternSource": artifact_key_schema("pattern-source"),
            "patternPlan": artifact_key_schema("pattern-plan"),
            "patternQuery": artifact_key_schema("pattern-query"),
        },
    }


def pattern_variable_name_schema() -> dict[str, Any]:
    """Use exactly the public witness-binding variable grammar."""
    return {"$ref": "common.schema.json#/$defs/binding/properties/name"}


def write_bag11_schemas_and_roles() -> None:
    """Freeze BAG-11's closed interchange schemas before refreshing identities."""
    schema_dir = ROOT / "schemas"
    common_path = schema_dir / "common.schema.json"
    common = json.loads(common_path.read_text(encoding="utf-8"))
    roles = common["$defs"]["artifactRole"]["enum"]
    roles = [role for role in roles if role != "pattern"]
    roles.extend(role for role in [
        "pattern-source", "pattern-plan", "pattern-query",
        "side-condition-conformance-table", "pattern-side-condition",
        "pattern-compiler-profile",
    ] if role not in roles)
    common["$defs"]["artifactRole"]["enum"] = sorted(roles)
    common["$defs"]["patternQueryRoot"] = pattern_query_root_schema()
    common_path.write_text(json.dumps(common, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    plan_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/pattern-plan.schema.json",
        "title": "Closed normalized flat DNF pattern plan v1",
        "type": "object", "additionalProperties": False,
        "required": ["schemaVersion", "patternPlanDigest", "eventVocabularyDigest", "variables", "arms", "sideCondition"],
        "properties": {
            "schemaVersion": {"const": 1},
            "patternPlanDigest": {"$ref": "common.schema.json#/$defs/digest"},
            "eventVocabularyDigest": {"$ref": "common.schema.json#/$defs/digest"},
            "variables": {"type": "array", "items": {"$ref": "#/$defs/variable"}},
            "arms": {"type": "array", "minItems": 1, "items": {"$ref": "#/$defs/arm"}},
            "sideCondition": {"oneOf": [{"type": "null"}, {"$ref": "#/$defs/sideCondition"}]},
        },
        "$defs": {
            "variable": {
                "type": "object", "additionalProperties": False,
                "required": ["name", "sort"],
                "properties": {"name": pattern_variable_name_schema(), "sort": {"type": "string", "minLength": 1}},
            },
            "payload": {
                "type": "object", "additionalProperties": False,
                "required": ["position", "mode", "variable"],
                "properties": {
                    "position": {"type": "integer", "minimum": 0},
                    "mode": {"enum": ["bind", "use"]},
                    "variable": pattern_variable_name_schema(),
                },
            },
            "atom": {
                "type": "object", "additionalProperties": False,
                "required": ["constructor", "payload"],
                "properties": {
                    "constructor": {"type": "string", "minLength": 1},
                    "payload": {"type": "array", "items": {"$ref": "#/$defs/payload"}},
                },
            },
            "arm": {
                "type": "object", "additionalProperties": False,
                "required": ["atoms", "relations"],
                "properties": {
                    "atoms": {"type": "array", "minItems": 1, "items": {"$ref": "#/$defs/atom"}},
                    "relations": {"type": "array", "items": {"enum": ["next-event", "eventually-after"]}},
                },
            },
            "sideCondition": {
                "type": "object", "additionalProperties": False,
                "required": ["artifact", "resultSort", "inputVariables"],
                "properties": {
                    "artifact": artifact_key_schema("pattern-side-condition"),
                    "resultSort": {"const": "Bool"},
                    "inputVariables": {"type": "array", "uniqueItems": True, "items": pattern_variable_name_schema()},
                },
            },
        },
    }
    (schema_dir / "pattern-plan.schema.json").write_text(json.dumps(plan_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    query_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/pattern-query.schema.json",
        "title": "Self-identified named K-authored pattern query v1",
        "type": "object", "additionalProperties": False,
        "required": ["patternSource", "patternPlan", "entryModule", "exportedName", "queryId"],
        "properties": {
            "patternSource": artifact_key_schema("pattern-source"),
            "patternPlan": artifact_key_schema("pattern-plan"),
            "entryModule": {"type": "string", "minLength": 1},
            "exportedName": {"type": "string", "minLength": 1},
            "queryId": {"$ref": "common.schema.json#/$defs/digest"},
        },
    }
    (schema_dir / "pattern-query.schema.json").write_text(json.dumps(query_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    table_schema = {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/side-condition-conformance-table.schema.json",
        "title": "Finite side-condition conformance oracle table v1",
        "type": "object", "additionalProperties": False,
        "required": ["schemaVersion", "tableDigest", "rows"],
        "properties": {
            "schemaVersion": {"const": 1},
            "tableDigest": {"$ref": "common.schema.json#/$defs/digest"},
            "rows": {"type": "array", "minItems": 1, "items": {"$ref": "#/$defs/row"}},
        },
        "$defs": {
            "row": {
                "type": "object", "additionalProperties": False,
                "required": ["condition", "bindingsDigest", "pathPredicateDigest", "result"],
                "properties": {
                    "condition": artifact_key_schema("pattern-side-condition"),
                    "bindingsDigest": {"$ref": "common.schema.json#/$defs/digest"},
                    "pathPredicateDigest": {"$ref": "common.schema.json#/$defs/digest"},
                    "result": {"enum": ["true", "false", "unknown"]},
                },
            },
        },
    }
    (schema_dir / "side-condition-conformance-table.schema.json").write_text(json.dumps(table_schema, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    observation_path = schema_dir / "observation-manifest.schema.json"
    observation = json.loads(observation_path.read_text(encoding="utf-8"))
    if "eventVocabularyDigest" not in observation["required"]:
        observation["required"].insert(observation["required"].index("eventVocabulary") + 1, "eventVocabularyDigest")
    observation["properties"]["eventVocabularyDigest"] = {"$ref": "common.schema.json#/$defs/digest"}
    observation_path.write_text(json.dumps(observation, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    result_path = schema_dir / "pattern-result.schema.json"
    result = json.loads(result_path.read_text(encoding="utf-8"))
    result["properties"]["queryId"] = {"$ref": "common.schema.json#/$defs/digest"}
    inputs = result["properties"]["inputs"]
    inputs["required"] = [field for field in inputs["required"] if field != "patternDigest"]
    insert_at = inputs["required"].index("observationManifestDigest") + 1
    for field in reversed(["patternSource", "patternPlan", "patternQuery"]):
        if field not in inputs["required"]:
            inputs["required"].insert(insert_at, field)
    inputs["properties"].pop("patternDigest", None)
    inputs["properties"].update({
        "patternSource": artifact_key_schema("pattern-source"),
        "patternPlan": artifact_key_schema("pattern-plan"),
        "patternQuery": artifact_key_schema("pattern-query"),
    })
    witness = result["$defs"]["witness"]
    if "armOrdinal" not in witness["required"]:
        witness["required"].insert(witness["required"].index("eventIndices"), "armOrdinal")
    witness["properties"].pop("alternativeArm", None)
    witness["properties"]["armOrdinal"] = {"type": "integer", "minimum": 0}
    result_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    replay_path = schema_dir / "replay-manifest.schema.json"
    replay = json.loads(replay_path.read_text(encoding="utf-8"))
    replay["required"] = [field for field in replay["required"] if field != "patternDigest"]
    insert_at = replay["required"].index("observationManifestDigest") + 1
    for field in reversed(["patternSource", "patternPlan", "patternQuery"]):
        if field not in replay["required"]:
            replay["required"].insert(insert_at, field)
    replay["properties"].pop("patternDigest", None)
    replay["properties"]["queryId"] = {"oneOf": [{"$ref": "common.schema.json#/$defs/digest"}, {"type": "null"}]}
    replay["properties"].update({
        "patternSource": nullable_artifact_key_schema("pattern-source"),
        "patternPlan": nullable_artifact_key_schema("pattern-plan"),
        "patternQuery": nullable_artifact_key_schema("pattern-query"),
    })
    replay_path.write_text(json.dumps(replay, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    corpus_path = schema_dir / "corpus-manifest.schema.json"
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    corpus["required"] = [field for field in corpus["required"] if field != "patternDigest"]
    if "patternQueries" not in corpus["required"]:
        corpus["required"].insert(corpus["required"].index("observationManifestDigest") + 1, "patternQueries")
    corpus["properties"].pop("patternDigest", None)
    corpus["properties"]["patternQueries"] = {"type": "array", "minItems": 1, "items": {"$ref": "common.schema.json#/$defs/patternQueryRoot"}}
    test = corpus["properties"]["tests"]["items"]
    test["required"] = [field for field in test["required"] if field != "patternQuery"]
    if "patternQueries" not in test["required"]:
        test["required"].append("patternQueries")
    test["properties"].pop("patternQuery", None)
    test["properties"]["patternQueries"] = {"type": "array", "minItems": 1, "items": {"$ref": "common.schema.json#/$defs/patternQueryRoot"}}
    corpus_path.write_text(json.dumps(corpus, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    mutation_path = schema_dir / "mutation-manifest.schema.json"
    mutation = json.loads(mutation_path.read_text(encoding="utf-8"))
    if "oracles" in mutation["properties"]:
        oracle = mutation["properties"]["oracles"]["items"]
        oracle["properties"].update({
            "patternSource": artifact_key_schema("pattern-source"),
            "patternPlan": artifact_key_schema("pattern-plan"),
            "patternQuery": artifact_key_schema("pattern-query"),
        })
        oracle["allOf"] = [{
            "if": {"properties": {"kind": {"const": "execution-pattern"}}, "required": ["kind"]},
            "then": {"required": ["patternSource", "patternPlan", "patternQuery"]},
            "else": {"allOf": [{"not": {"required": [field]}} for field in ["patternSource", "patternPlan", "patternQuery"]]},
        }]
    mutation_test = mutation["properties"]["tests"]["items"]
    if "patternQueries" not in mutation_test["required"]:
        mutation_test["required"].append("patternQueries")
    mutation_test["properties"]["patternQueries"] = {"type": "array", "items": {"$ref": "common.schema.json#/$defs/patternQueryRoot"}}
    mutation_path.write_text(json.dumps(mutation, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    policy_path = schema_dir / "mutation-execution-policy.schema.json"
    policy = json.loads(policy_path.read_text(encoding="utf-8"))
    cache = policy["properties"].get("cacheKey")
    if cache is not None:
        if "patternQueries" not in cache["required"]:
            cache["required"].insert(cache["required"].index("testManifestDigest"), "patternQueries")
        cache["properties"]["patternQueries"] = {"type": "array", "items": {"$ref": "common.schema.json#/$defs/patternQueryRoot"}}
    policy_path.write_text(json.dumps(policy, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    registry_path = ROOT / "artifact-role-specs.json"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    registry["specs"] = [spec for spec in registry["specs"] if spec["role"] != "pattern"]
    additions = [
        {"role": "pattern-source", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        {"role": "pattern-side-condition", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        {"role": "pattern-compiler-profile", "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "schema": None, "digestDomain": "k-in-k/opaque-artifact/v1", "projection": {"kind": "opaque-envelope"}, "selfIdField": None},
        {"role": "pattern-plan", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "pattern-plan.schema.json", "digestDomain": "k-in-k/pattern-plan/v1", "projection": {"kind": "without-field"}, "selfIdField": "patternPlanDigest"},
        {"role": "pattern-query", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "pattern-query.schema.json", "digestDomain": "k-in-k/pattern-query/v1", "projection": {"kind": "without-field"}, "selfIdField": "queryId"},
        {"role": "side-condition-conformance-table", "contentModel": "canonical-json", "mediaType": "application/json", "schema": "side-condition-conformance-table.schema.json", "digestDomain": "k-in-k/side-condition-conformance-table/v1", "projection": {"kind": "without-field"}, "selfIdField": "tableDigest"},
    ]
    existing = {spec["role"] for spec in registry["specs"]}
    registry["specs"].extend(spec for spec in additions if spec["role"] not in existing)
    registry["specs"].sort(key=lambda spec: spec["role"])
    registry_path.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def bag11_plan(event_vocabulary_digest: str, variables: list[dict[str, str]], arms: list[dict[str, Any]], side_condition: dict[str, Any] | None = None) -> dict[str, Any]:
    value = {
        "schemaVersion": 1,
        "patternPlanDigest": "0" * 64,
        "eventVocabularyDigest": event_vocabulary_digest,
        "variables": variables,
        "arms": arms,
        "sideCondition": side_condition,
    }
    value["patternPlanDigest"] = digest("k-in-k/pattern-plan/v1", without(value, "patternPlanDigest"))
    return value


def bag11_atom(constructor: str, *payload: tuple[int, str, str]) -> dict[str, Any]:
    return {"constructor": constructor, "payload": [{"position": position, "mode": mode, "variable": variable} for position, mode, variable in payload]}


def bag11_query(source: dict[str, str], plan: dict[str, Any], exported_name: str) -> dict[str, Any]:
    value = {
        "patternSource": deepcopy(source),
        "patternPlan": {"role": "pattern-plan", "digest": plan["patternPlanDigest"]},
        "entryModule": "PATTERN-QUERIES",
        "exportedName": exported_name,
        "queryId": "0" * 64,
    }
    value["queryId"] = digest("k-in-k/pattern-query/v1", without(value, "queryId"))
    return value


def bag11_query_root(query: dict[str, Any]) -> dict[str, Any]:
    return {
        "patternSource": deepcopy(query["patternSource"]),
        "patternPlan": deepcopy(query["patternPlan"]),
        "patternQuery": {"role": "pattern-query", "digest": query["queryId"]},
    }


def mutation_test_pattern_queries(manifest: dict[str, Any], test: dict[str, Any]) -> list[dict[str, Any]]:
    """Select execution-pattern roots in oracleIds order, retaining repeated roots."""
    declarations = {declaration["oracleId"]: declaration for declaration in manifest["oracles"]}
    return [
        {field: deepcopy(declarations[oracle_id][field]) for field in ("patternSource", "patternPlan", "patternQuery")}
        for oracle_id in test["oracleIds"]
        if declarations[oracle_id]["kind"] == "execution-pattern"
    ]


def flatten_test_pattern_queries(tests: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Flatten test declaration order, then each test's oracle-selection order."""
    return [deepcopy(root) for test in tests for root in test["patternQueries"]]


def ensure_bag11_memory_vocabulary(observation: dict[str, Any]) -> None:
    declarations = {item["constructor"]: item for item in observation["eventVocabulary"]}
    declarations.setdefault("Other", {"constructor": "Other", "payloadSorts": [], "originMode": "emitting-sentence"})
    declarations.setdefault("memoryFree", {"constructor": "memoryFree", "payloadSorts": ["Address"], "originMode": "emitting-sentence-and-semantic-site"})
    observation["eventVocabulary"] = sorted(declarations.values(), key=lambda item: item["constructor"])


def write_bag11_assets(observation: dict[str, Any], opaque: dict[str, dict[str, str]]) -> dict[str, Any]:
    """Build the normalized plans, self-identified queries, and finite table."""
    source = {"role": "pattern-source", "digest": opaque["pattern-source"]["digest"]}
    side_artifact = {"role": "pattern-side-condition", "digest": opaque["pattern-side-condition"]["digest"]}
    memory_vocabulary = deepcopy(observation["eventVocabulary"])
    memory_digest = observation["eventVocabularyDigest"]
    counter_vocabulary = [
        {"constructor": "branchTaken", "payloadSorts": ["Int"], "originMode": "emitting-sentence"},
        {"constructor": "counterIncrement", "payloadSorts": ["Int", "Int"], "originMode": "emitting-sentence"},
    ]
    counter_digest = digest("k-in-k/event-vocabulary/v1", counter_vocabulary)
    variable_a = [{"name": "A", "sort": "Address"}]
    variable_n = [{"name": "N", "sort": "Int"}]
    nonlexical_variables = [{"name": "VALUE", "sort": "Int"}, {"name": "ADDRESS", "sort": "Address"}]

    def sequence(second: str, relation: str = "eventually-after") -> dict[str, Any]:
        return {"atoms": [bag11_atom("memoryWrite", (0, "bind", "A")), bag11_atom(second, (0, "use", "A"))], "relations": [relation]}

    plans = {
        "single-write": bag11_plan(memory_digest, variable_a, [{"atoms": [bag11_atom("memoryWrite", (0, "bind", "A"))], "relations": []}]),
        "write-next-load": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad", "next-event")]),
        "write-eventually-load": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad")]),
        "write-eventually-load-or-free": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad"), sequence("memoryFree")]),
        "overlapping-load-alternatives": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad"), sequence("memoryLoad")]),
        "increment-eventually-branch": bag11_plan(counter_digest, variable_n, [{"atoms": [bag11_atom("counterIncrement", (1, "bind", "N")), bag11_atom("branchTaken", (0, "use", "N"))], "relations": ["eventually-after"]}]),
        "write-then-load-side-condition": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad")], {"artifact": deepcopy(side_artifact), "resultSort": "Bool", "inputVariables": ["A"]}),
        "write-then-load-constant-side-condition": bag11_plan(memory_digest, variable_a, [sequence("memoryLoad")], {"artifact": deepcopy(side_artifact), "resultSort": "Bool", "inputVariables": []}),
        "nonlexical-subset-side-condition": bag11_plan(memory_digest, nonlexical_variables, [{
            "atoms": [
                bag11_atom("memoryWrite", (0, "bind", "ADDRESS"), (1, "bind", "VALUE")),
                bag11_atom("memoryLoad", (0, "use", "ADDRESS"), (1, "use", "VALUE")),
            ],
            "relations": ["eventually-after"],
        }], {"artifact": deepcopy(side_artifact), "resultSort": "Bool", "inputVariables": ["VALUE"]}),
    }
    queries = {name: bag11_query(source, plan, name) for name, plan in plans.items()}

    vector_path = ROOT / "vectors" / "execution-pattern-vectors.json"
    vectors = json.loads(vector_path.read_text(encoding="utf-8"))
    vectors["terms"].setdefault("false", {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "token", "text": "false"}})
    retired_ids = {"accepted-r3-g-04-exact-pair", "accepted-r3-three-events-was-exact-pattern-only"}
    vectors["cases"] = [case for case in vectors["cases"] if case["id"] not in retired_ids]
    for case in vectors["cases"]:
        witness = case.get("expected", {}).get("witness")
        if witness is not None and "alternativeArm" in witness:
            witness["armOrdinal"] = witness.pop("alternativeArm")
        case.pop("sideConditionResult", None)
        if case["id"] == "side-condition-false":
            case["paths"][0]["eventRefs"] = ["wb", "lb"]
        elif case["id"] == "side-condition-indeterminate":
            case["paths"][0]["eventRefs"] = ["wSymbolic", "lSymbolic"]
            case["paths"][0]["pathPredicate"] = "true"

    new_case_ids = {"constant-side-condition-true", "subset-side-condition-preserves-nonlexical-declaration-order"}
    vectors["cases"] = [case for case in vectors["cases"] if case["id"] not in new_case_ids]
    vectors["cases"].extend([
        {
            "id": "constant-side-condition-true",
            "paths": [{"pathKey": "p0", "complete": True, "stopReason": "terminal", "eventRefs": ["wa", "la"]}],
            "query": "write-then-load-constant-side-condition",
            "expected": {"outcome": "match", "completeCoverage": True, "witness": {"pathKey": "p0", "eventIndices": [0, 1], "bindings": {"A": "a"}}},
        },
        {
            "id": "subset-side-condition-preserves-nonlexical-declaration-order",
            "paths": [{"pathKey": "p0", "complete": True, "stopReason": "terminal", "eventRefs": ["wa", "la"]}],
            "query": "nonlexical-subset-side-condition",
            "expected": {"outcome": "match", "completeCoverage": True, "witness": {"pathKey": "p0", "eventIndices": [0, 1], "bindings": {"VALUE": "v7", "ADDRESS": "a"}}},
        },
    ])

    def binding_digest(*bindings: tuple[str, str]) -> str:
        value = [{"name": name, "term": vectors["terms"][term_name]} for name, term_name in bindings]
        return digest("k-in-k/bindings/v1", value)

    predicate_digest = digest("k-in-k/path-predicate/v1", vectors["terms"]["true"])
    rows = [
        {"condition": deepcopy(side_artifact), "bindingsDigest": binding_digest(("A", "a")), "pathPredicateDigest": predicate_digest, "result": "true"},
        {"condition": deepcopy(side_artifact), "bindingsDigest": binding_digest(("A", "b")), "pathPredicateDigest": predicate_digest, "result": "false"},
        {"condition": deepcopy(side_artifact), "bindingsDigest": binding_digest(("A", "symbolicA")), "pathPredicateDigest": predicate_digest, "result": "unknown"},
        {"condition": deepcopy(side_artifact), "bindingsDigest": binding_digest(), "pathPredicateDigest": predicate_digest, "result": "true"},
        {"condition": deepcopy(side_artifact), "bindingsDigest": binding_digest(("VALUE", "v7")), "pathPredicateDigest": predicate_digest, "result": "true"},
    ]
    rows.sort(key=lambda row: (row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]))
    table = {"schemaVersion": 1, "tableDigest": "0" * 64, "rows": rows}
    table["tableDigest"] = digest("k-in-k/side-condition-conformance-table/v1", without(table, "tableDigest"))
    vectors.pop("patternDefinitionCases", None)
    vectors["eventVocabularies"] = {
        "memory": {"eventVocabularyDigest": memory_digest, "constructors": memory_vocabulary},
        "counter": {"eventVocabularyDigest": counter_digest, "constructors": counter_vocabulary},
    }
    vectors["patternSource"] = deepcopy(source)
    vectors["plans"] = plans
    vectors["queries"] = queries
    vectors["sideConditionTable"] = table
    vectors["compilerConformance"] = {"status": "not-proven", "futureRequirement": "rust-k-pattern-compiler-receipt"}
    vectors["historicalRetiredWholeTraceEvidence"] = [
        {"id": "accepted-r3-g-04-exact-pair", "status": "historical-only", "retiredSemantics": "legacy-exact-trace", "evidence": "bounded-retired-stack"},
        {"id": "accepted-r3-three-events-was-exact-pattern-only", "status": "historical-only", "retiredSemantics": "legacy-exact-trace", "evidence": "bounded-retired-stack"},
    ]
    vector_path.write_text(json.dumps(vectors, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    for name, plan in plans.items():
        save(f"pattern-plan-{name}.json", plan)
        save(f"pattern-query-{name}.json", queries[name])
    save("side-condition-conformance-table.json", table)
    return {"source": source, "sideArtifact": side_artifact, "plans": plans, "queries": queries, "table": table}


def bag11_fixture_witnesses(plan: dict[str, Any], trace: dict[str, Any], path_record: dict[str, Any]) -> list[dict[str, Any]]:
    """Derive the complete finite denotation for the persisted single-path fixtures."""
    derived: list[dict[str, Any]] = []

    def match_atom(atom: dict[str, Any], event: dict[str, Any], bindings: dict[str, Any]) -> dict[str, Any] | None:
        if atom["constructor"] != event["constructor"]:
            return None
        result = deepcopy(bindings)
        for clause in atom["payload"]:
            if clause["position"] >= len(event["payload"]):
                return None
            term = event["payload"][clause["position"]]
            variable = clause["variable"]
            if clause["mode"] == "bind":
                if variable in result:
                    return None
                result[variable] = term
            elif variable not in result or canonical(result[variable]) != canonical(term):
                return None
        return result

    def extend(arm: dict[str, Any], atom_ordinal: int, indices: list[int], bindings: dict[str, Any]) -> None:
        if atom_ordinal == len(arm["atoms"]):
            ordered_bindings = [{"name": variable["name"], "term": deepcopy(bindings[variable["name"]])} for variable in plan["variables"]]
            derived.append({"eventIndices": indices, "bindings": ordered_bindings})
            return
        if not indices:
            candidates = range(len(trace["events"]))
        elif arm["relations"][atom_ordinal - 1] == "next-event":
            candidates = [indices[-1] + 1]
        else:
            candidates = range(indices[-1] + 1, len(trace["events"]))
        for index in candidates:
            if index >= len(trace["events"]):
                continue
            matched = match_atom(arm["atoms"][atom_ordinal], trace["events"][index], bindings)
            if matched is not None:
                extend(arm, atom_ordinal + 1, [*indices, index], matched)

    for arm_ordinal, arm in enumerate(plan["arms"]):
        before = len(derived)
        extend(arm, 0, [], {})
        for witness in derived[before:]:
            witness["armOrdinal"] = arm_ordinal
    path_key = trace.get("pathKey")
    for witness in derived:
        indices = witness["eventIndices"]
        witness.update({
            "pathOrdinal": path_record["pathOrdinal"],
            "events": [deepcopy(trace["events"][index]) for index in indices],
            "pathPredicate": deepcopy(trace["pathPredicate"]),
            "stopReason": path_record["stopReason"],
            "executionStopReason": trace["stopReason"],
        })
        if path_key is not None:
            witness["pathKey"] = path_key
            witness["replayKey"] = digest("k-in-k/witness-replay-key/v1", {"testId": trace["testId"], "pathKey": path_key, "eventIndices": indices})
    derived.sort(key=lambda witness: (witness.get("pathKey", ""), tuple(witness["eventIndices"]), digest("k-in-k/bindings/v1", witness["bindings"]), witness["armOrdinal"]))
    return derived


def migrate_bag13_value(value: Any) -> None:
    """Close the portable semantic slice without inventing native K declarations."""
    if isinstance(value, list):
        for item in value:
            migrate_bag13_value(item)
        return
    if not isinstance(value, dict):
        return
    if value.get("encoding") == "portable-term-v1":
        node = value["node"]
        for child in node.get("args", []):
            migrate_bag13_value(child)
        for child_name in ("left", "right", "term"):
            if child_name in node:
                migrate_bag13_value(node[child_name])
        for child in node.get("items", []):
            migrate_bag13_value(child)
        if node.get("kind") == "application" and "symbolId" not in node:
            node["symbolId"] = digest("k-in-k/test-symbol/v1", {
                "displayLabel": node["label"], "resultSort": value["sort"],
                "argumentSorts": [argument["sort"] for argument in node["args"]],
            })
        return
    if {"family", "modules", "definitionDigest"} <= value.keys():
        value["representation"] = "portable-mutation-semantic-slice-v1"
    if "occurrenceOrdinal" in value and "provenance" in value and "value" in value:
        value["sourceOccurrenceOrdinal"] = value.pop("occurrenceOrdinal") if not value["provenance"]["generated"] else None
    elif "occurrenceOrdinal" in value and {"module", "source", "location", "kind"} <= value.keys():
        value["sourceOccurrenceOrdinal"] = value.pop("occurrenceOrdinal")
    if value.get("kind") == "generated-rule":
        value["kind"] = "rule"
    for item in value.values():
        migrate_bag13_value(item)


def replace_known_ids(value: Any, replacements: dict[str, str]) -> Any:
    if isinstance(value, str):
        seen: set[str] = set()
        while value in replacements and replacements[value] != value and value not in seen:
            seen.add(value)
            value = replacements[value]
        return value
    if isinstance(value, list):
        return [replace_known_ids(item, replacements) for item in value]
    if isinstance(value, dict):
        return {key: replace_known_ids(item, replacements) for key, item in value.items()}
    return value


def refresh_bag13_embedded_ids(value: Any, replacements: dict[str, str]) -> None:
    if isinstance(value, list):
        for item in value:
            refresh_bag13_embedded_ids(item, replacements)
        return
    if not isinstance(value, dict):
        return
    for item in value.values():
        refresh_bag13_embedded_ids(item, replacements)
    if {"patchId", "operatorId", "operatorVersion", "edits"} <= value.keys():
        for edit in value["edits"]:
            old_edit = edit["editId"]
            edit["editId"] = digest("k-in-k/edit/v1", without(edit, "editId"))
            replacements[old_edit] = edit["editId"]
        value["edits"].sort(key=lambda edit: (edit["targetLineage"] or "", canonical(edit["targetPath"]), edit["operation"], edit["editId"]))
        old_patch = value["patchId"]
        value["patchId"] = digest("k-in-k/patch/v1", {"schemaVersion": value["schemaVersion"], "edits": value["edits"]})
        replacements[old_patch] = value["patchId"]
    if {"diffId", "baselineDefinitionDigest", "mutantDefinitionDigest", "entries"} <= value.keys():
        value["portableApplication"] = "applied-and-locally-well-formed"
        value["nativeIrValidation"] = "rust-proof-pending"
        old_diff = value["diffId"]
        value["diffId"] = digest("k-in-k/structural-diff/v1", without(value, "diffId"))
        replacements[old_diff] = value["diffId"]


def refresh_bag13_definition(definition: dict[str, Any], replacements: dict[str, str]) -> None:
    migrate_bag13_value(definition)
    old_family = definition["baselineFamilyId"]
    definition["baselineFamilyId"] = digest("k-in-k/baseline-family/v1", definition["family"])
    replacements[old_family] = definition["baselineFamilyId"]
    for module in definition["modules"]:
        for sentence in module["sentences"]:
            value, provenance = sentence["value"], sentence["provenance"]
            if not provenance["generated"]:
                old_lineage = provenance["lineageId"]
                lineage_payload = {
                    "baselineFamilyId": definition["baselineFamilyId"], "module": module["name"],
                    "source": value["source"], "location": value["location"], "kind": value["kind"],
                    "sourceOccurrenceOrdinal": sentence["sourceOccurrenceOrdinal"],
                }
                provenance["lineageId"] = digest("k-in-k/input-lineage/v1", lineage_payload)
                replacements[old_lineage] = provenance["lineageId"]
    for module in definition["modules"]:
        for sentence in module["sentences"]:
            if sentence["provenance"]["generated"]:
                identity = replace_known_ids(sentence["generatedIdentity"], replacements)
                identity["parentLineages"] = sorted(set(identity["parentLineages"]))
                sentence["generatedIdentity"] = identity
                old_lineage = sentence["provenance"]["lineageId"]
                sentence["provenance"]["lineageId"] = digest("k-in-k/generated-lineage/v1", identity)
                replacements[old_lineage] = sentence["provenance"]["lineageId"]
    module_payloads = []
    for module in definition["modules"]:
        contents = []
        for sentence in module["sentences"]:
            value, provenance = sentence["value"], sentence["provenance"]
            provenance.update({"module": value["module"], "label": value["label"], "kind": value["kind"], "source": value["source"], "location": value["location"]})
            body_id = digest("k-in-k/sentence-body/v1", {"body": value["body"], "requires": value["requires"], "ensures": value["ensures"]})
            replacements[provenance["bodyFingerprint"]] = body_id
            provenance["bodyFingerprint"] = body_id
            content_payload = {"lineageId": provenance["lineageId"], "module": value["module"], "label": value["label"], "kind": value["kind"], "source": value["source"], "location": value["location"], "generated": provenance["generated"], "bodyFingerprint": body_id, "attributes": value["attributes"], "transformationChain": provenance["transformationChain"]}
            content_id = digest("k-in-k/sentence-content/v1", content_payload)
            replacements[provenance["contentFingerprint"]] = content_id
            provenance["contentFingerprint"] = content_id
            contents.append(content_id)
        module_payload = {"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": contents}
        old_module = module["fingerprint"]
        module["fingerprint"] = digest("k-in-k/module/v1", module_payload)
        replacements[old_module] = module["fingerprint"]
        module_payloads.append(module_payload)
    old_definition = definition["definitionDigest"]
    definition["definitionDigest"] = digest("k-in-k/definition/v1", {"schemaVersion": 1, "representation": definition["representation"], "baselineFamilyId": definition["baselineFamilyId"], "modules": module_payloads})
    replacements[old_definition] = definition["definitionDigest"]


def refresh_bag13_identity_fixture() -> None:
    verifier = load_portable_verifier()
    baseline = load("semantic-definition-memory.json")
    vector_data = json.loads((ROOT / "vectors" / "patch-application-vectors.json").read_text(encoding="utf-8"))
    case = next(item for item in vector_data["cases"] if item["id"] == "before-and-module-end-insertion")
    patch = verifier.materialize_vector_patch(vector_data, case)
    output, _diff, failure = verifier.apply_portable_patch(baseline, patch)
    if failure is not None or output is None:
        raise AssertionError(f"standalone identity output definition could not be reviewed: {failure}")
    save("semantic-definition-identity-output.json", output)
    source = baseline["modules"][0]["sentences"][0]
    value = source["value"]
    provenance = source["provenance"]
    generated = next(sentence for module in output["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None and sentence["generatedIdentity"]["role"] == "insert-module-end")
    definition_summary = {
        "schemaVersion": baseline["schemaVersion"], "representation": baseline["representation"], "baselineFamilyId": baseline["baselineFamilyId"],
        "modules": [{"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": [sentence["provenance"]["contentFingerprint"] for sentence in module["sentences"]]} for module in baseline["modules"]],
    }
    transformation = {"kind": "mutation", "operatorId": patch["operatorId"], "operatorVersion": patch["operatorVersion"], "inputDefinitionDigest": baseline["definitionDigest"], "manifestDigest": patch["patchId"]}
    identity = {
        "schemaVersion": 1,
        "baselineFamilyId": baseline["baselineFamilyId"],
        "definitionDigest": baseline["definitionDigest"],
        "transformationId": generated["generatedIdentity"]["transformationId"],
        "generatedLineageId": generated["provenance"]["lineageId"],
        "digestInputs": {
            "baselineFamily": deepcopy(baseline["family"]),
            "inputLineage": {"baselineFamilyId": baseline["baselineFamilyId"], "module": value["module"], "source": value["source"], "location": deepcopy(value["location"]), "kind": value["kind"], "sourceOccurrenceOrdinal": source["sourceOccurrenceOrdinal"]},
            "sentenceBody": {"body": deepcopy(value["body"]), "requires": deepcopy(value["requires"]), "ensures": deepcopy(value["ensures"])},
            "sentenceContent": {"lineageId": provenance["lineageId"], "module": provenance["module"], "label": provenance["label"], "kind": provenance["kind"], "source": provenance["source"], "location": deepcopy(provenance["location"]), "generated": provenance["generated"], "bodyFingerprint": provenance["bodyFingerprint"], "attributes": deepcopy(value["attributes"]), "transformationChain": deepcopy(provenance["transformationChain"])},
            "definition": definition_summary,
            "transformation": transformation,
            "generatedLineage": deepcopy(generated["generatedIdentity"]),
        },
        "transformationEvidence": {"inputDefinition": {"role": "definition", "digest": baseline["definitionDigest"]}, "outputDefinition": {"role": "mutant-definition", "digest": output["definitionDigest"]}},
        "sentences": [deepcopy(provenance)],
    }
    save("semantic-identity.json", identity)


def migrate_bag13_inputs() -> None:
    replacements: dict[str, str] = {}
    definitions = ["semantic-definition-memory.json", "semantic-definition-counter.json", "semantic-definition-generated.json"]
    loaded = [(name, load(name)) for name in definitions]
    for _, definition in loaded:
        refresh_bag13_definition(definition, replacements)
    for name, definition in loaded:
        refresh_bag13_definition(definition, replacements)
        save(name, definition)
    for base in (FIXTURES, ROOT / "vectors"):
        for path in sorted(base.glob("*.json")):
            if path.name in definitions:
                continue
            value = json.loads(path.read_text(encoding="utf-8"))
            value = replace_known_ids(value, replacements)
            migrate_bag13_value(value)
            refresh_bag13_embedded_ids(value, replacements)
            path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    campaign = load("mutation-campaign.json")
    baseline = load("semantic-definition-memory.json")
    candidate_patch = campaign["generation"]["candidates"][0]["patch"]
    migrated_mutant = materialize_mutant_definition(baseline, candidate_patch)
    for mutant in campaign["mutants"]:
        replacements[mutant["outputDefinitionDigest"]] = migrated_mutant["definitionDigest"]
    for base in (FIXTURES, ROOT / "vectors"):
        for path in sorted(base.glob("*.json")):
            if path.name in definitions:
                continue
            value = replace_known_ids(json.loads(path.read_text(encoding="utf-8")), replacements)
            refresh_bag13_embedded_ids(value, replacements)
            path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    refresh_bag13_identity_fixture()


def load_portable_verifier() -> Any:
    verifier_path = ROOT / "verify.py"
    verifier = ModuleType("bag13_portable_verifier")
    verifier.__file__ = str(verifier_path)
    verifier.__package__ = None
    code = compile(verifier_path.read_bytes(), str(verifier_path), "exec")
    exec(code, verifier.__dict__)
    return verifier


def refresh_bag13_patch_vector_outputs() -> None:
    verifier = load_portable_verifier()
    path = ROOT / "vectors" / "patch-application-vectors.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    data["portableApplicationBoundary"] = {"portableApplication": "applied-and-locally-well-formed", "nativeIrValidation": "rust-proof-pending"}
    for case in data["cases"]:
        definition = load(case["definitionFixture"])
        patch = verifier.materialize_vector_patch(data, case)
        output, diff_value, failure = verifier.apply_portable_patch(definition, patch)
        if not case["expected"]["valid"]:
            if failure is None or output is not None or diff_value is not None:
                raise AssertionError(f"BAG-13 made rejecting patch vector {case['id']} succeed")
            case["expected"]["failure"] = failure
            case["expected"]["appliedEditCount"] = 0
            continue
        if failure is not None or output is None or diff_value is None:
            raise AssertionError(f"BAG-13 made accepted patch vector {case['id']} fail: {failure}")
        case["expected"]["outputDefinitionDigest"] = output["definitionDigest"]
        case["expected"]["diffId"] = diff_value["diffId"]
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def opaque_material(role: str, file_name: str) -> dict[str, str]:
    content_sha256 = raw_sha256((MATERIAL / file_name).read_bytes())
    return {
        "role": role,
        "digest": digest("k-in-k/opaque-artifact/v1", {"role": role, "mediaType": "application/octet-stream", "contentSha256": content_sha256}),
        "contentSha256": content_sha256,
        "fileName": file_name,
    }


def artifact_keys_only(value: Any) -> None:
    if isinstance(value, list):
        for item in value:
            artifact_keys_only(item)
    elif isinstance(value, dict):
        if "role" in value and "digest" in value and any(key in value for key in ("mediaType", "logicalPath", "contentModel", "resolverId", "availability")):
            value["role"] = {"projection": "oracle-projection", "comparison": "oracle-comparison", "baseline-value": "oracle-value", "mutant-value": "oracle-value"}.get(value["role"], value["role"])
            for key in ("mediaType", "logicalPath", "contentModel", "resolverId", "availability"):
                value.pop(key, None)
        for item in value.values():
            artifact_keys_only(item)


def without(value: dict[str, Any], *keys: str) -> dict[str, Any]:
    result = deepcopy(value)
    for key in keys:
        result.pop(key, None)
    return result


def normal_operand(side: str, role: str, artifact_digest: str) -> dict[str, Any]:
    return {"side": side, "terminal": {"kind": "normal", "artifact": {"role": role, "digest": artifact_digest}}}


def campaign_oracles_to_legacy(campaign: dict[str, Any]) -> None:
    """Normalize either report shape for the pre-BAG-09 mechanical refresh steps."""
    for oracle in campaign["baseline"]["oracleResults"]:
        if "operand" not in oracle:
            continue
        terminal = oracle.pop("operand")["terminal"]
        value_digest = terminal["artifact"]["digest"] if terminal is not None else None
        oracle["outcome"] = "agree" if oracle["outcome"] == "accepted" else oracle["outcome"]
        oracle["baselineValueDigest"] = value_digest
        oracle["mutantValueDigest"] = value_digest
        oracle["valueArtifacts"] = [] if terminal is None else [terminal["artifact"], terminal["artifact"]]
        oracle["witnessDigest"] = None
        if oracle["failure"] is not None:
            oracle["failure"] = oracle["failure"]["failure"]
    for mutant in campaign["mutants"]:
        for oracle in mutant["oracleResults"]:
            if "operands" not in oracle:
                continue
            terminals = [operand["terminal"] for operand in oracle.pop("operands")]
            digests = [terminal["artifact"]["digest"] if terminal is not None else None for terminal in terminals]
            oracle["baselineValueDigest"], oracle["mutantValueDigest"] = digests
            oracle["valueArtifacts"] = [terminal["artifact"] for terminal in terminals if terminal is not None]
            if oracle["failure"] is not None:
                oracle["failure"] = oracle["failure"]["failure"]


def campaign_oracles_to_bag09(campaign: dict[str, Any]) -> None:
    for oracle in campaign["baseline"]["oracleResults"]:
        role = "pattern-result" if oracle["kind"] == "execution-pattern" else "oracle-value"
        value_digest = oracle.pop("baselineValueDigest")
        oracle.pop("mutantValueDigest")
        oracle.pop("valueArtifacts")
        oracle.pop("witnessDigest")
        oracle["outcome"] = "accepted" if oracle["outcome"] == "agree" else oracle["outcome"]
        oracle["operand"] = {"side": "baseline", "terminal": None if value_digest is None else normal_operand("baseline", role, value_digest)["terminal"]}
        if oracle["failure"] is not None:
            oracle["failure"] = {"sourceSide": "baseline-execution", "failure": oracle["failure"]}
    for mutant in campaign["mutants"]:
        for oracle in mutant["oracleResults"]:
            role = "pattern-result" if oracle["kind"] == "execution-pattern" else "oracle-value"
            baseline_digest = oracle.pop("baselineValueDigest")
            mutant_digest = oracle.pop("mutantValueDigest")
            oracle.pop("valueArtifacts")
            oracle["operands"] = [
                {"side": "baseline", "terminal": None if baseline_digest is None else normal_operand("baseline", role, baseline_digest)["terminal"]},
                {"side": "mutant", "terminal": None if mutant_digest is None else normal_operand("mutant", role, mutant_digest)["terminal"]},
            ]
            if oracle["failure"] is not None:
                source = "comparison" if baseline_digest is not None and mutant_digest is not None else "mutant-execution" if baseline_digest is not None else "baseline-execution"
                oracle["failure"] = {"sourceSide": source, "failure": oracle["failure"]}


def path_get(value: Any, path: list[dict[str, Any]]) -> Any:
    current = value
    for segment in path:
        kind = segment["kind"]
        if kind == "field":
            name = {"lhs": "left", "rhs": "right"}.get(segment["name"], segment["name"])
            if name == "body" and isinstance(current, dict) and "value" in current:
                current = current["value"]
            current = current[name] if name in current else current["node"][name]
        elif kind == "argument":
            current = current["node"]["args"][segment["index"]]
        elif kind == "sequence-item":
            current = current["node"]["items"][segment["index"]]
        elif kind == "injection-term":
            current = current["node"]["term"]
        else:
            raise ValueError(f"unsupported fixture path segment: {kind}")
    return current


def path_replace(sentence_value: dict[str, Any], path: list[dict[str, Any]], replacement: Any) -> None:
    parent = path_get(sentence_value, path[:-1]) if len(path) > 1 else sentence_value
    step = path[-1]
    if step["kind"] == "field":
        name = step["name"]
        if parent is sentence_value:
            parent[name] = replacement
        else:
            parent["node"]["left" if name == "lhs" else "right"] = replacement
    elif step["kind"] == "argument":
        parent["node"]["args"][step["index"]] = replacement
    elif step["kind"] == "sequence-item":
        parent["node"]["items"][step["index"]] = replacement
    elif step["kind"] == "injection-term":
        parent["node"]["term"] = replacement
    else:
        raise AssertionError("unsupported synthetic fixture patch path")


def materialize_mutant_definition(definition: dict[str, Any], patch: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(definition)
    sentences = {sentence["provenance"]["lineageId"]: sentence for module in result["modules"] for sentence in module["sentences"]}
    for edit in patch["edits"]:
        if edit["operation"] != "replace-term":
            raise AssertionError("BAG-08 material fixture only admits the existing replace-term patch")
        path_replace(sentences[edit["targetLineage"]]["value"], edit["targetPath"], deepcopy(edit["value"]["term"]))
    module_payloads = []
    for module in result["modules"]:
        contents = []
        for sentence in module["sentences"]:
            value, provenance = sentence["value"], sentence["provenance"]
            body_id = digest("k-in-k/sentence-body/v1", {"body": value["body"], "requires": value["requires"], "ensures": value["ensures"]})
            provenance["bodyFingerprint"] = body_id
            provenance["contentFingerprint"] = digest("k-in-k/sentence-content/v1", {"lineageId": provenance["lineageId"], "module": value["module"], "label": value["label"], "kind": value["kind"], "source": value["source"], "location": value["location"], "generated": provenance["generated"], "bodyFingerprint": body_id, "attributes": value["attributes"], "transformationChain": provenance["transformationChain"]})
            contents.append(provenance["contentFingerprint"])
        module_payload = {"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": contents}
        module["fingerprint"] = digest("k-in-k/module/v1", module_payload)
        module_payloads.append(module_payload)
    result["definitionDigest"] = digest("k-in-k/definition/v1", {"schemaVersion": result["schemaVersion"], "representation": result["representation"], "baselineFamilyId": result["baselineFamilyId"], "modules": module_payloads})
    return result


def refresh_observation(value: dict[str, Any]) -> None:
    for selection in value["selections"]:
        selector = selection["selector"]
        if selector["kind"] == "lineage" and "valueDigest" in selector:
            selection["selector"] = {"kind": "lineage", "lineageId": selector["valueDigest"]}
        for emission in selection["emissions"]:
            if emission["semanticSite"] is not None:
                emission["semanticSite"].pop("siteId", None)
    value["eventVocabulary"].sort(key=lambda declaration: declaration["constructor"])
    value["eventVocabularyDigest"] = digest("k-in-k/event-vocabulary/v1", value["eventVocabulary"])
    request = without(value, "manifestId", "transformationId", "outputDefinitionDigest")
    request_digest = digest("k-in-k/observation-request/v1", request)
    transformation = {
        "kind": "observation-installation",
        "operatorId": value["observerDigest"],
        "operatorVersion": 1,
        "inputDefinitionDigest": value["inputDefinitionDigest"],
        "manifestDigest": request_digest,
    }
    value["transformationId"] = digest("k-in-k/transformation/v1", transformation)
    value["manifestId"] = digest("k-in-k/observation-manifest/v1", without(value, "manifestId"))


def derive_structural_matches(selector: dict[str, Any], definition: dict[str, Any]) -> list[str]:
    matches: list[str] = []
    for module in sorted(definition["modules"], key=lambda item: item["ordinal"]):
        for sentence in module["sentences"]:
            if sentence["value"]["kind"] not in selector["sentenceKinds"]:
                continue
            if selector["label"] is not None and sentence["provenance"]["label"] != selector["label"]:
                continue
            try:
                term = path_get(sentence["value"], selector["termPath"])
            except (KeyError, IndexError, TypeError, ValueError):
                continue
            if not isinstance(term, dict) or term.get("encoding") != "portable-term-v1" or term.get("sort") != selector["termSort"]:
                continue
            head = selector["termHeadLabel"]
            if head is not None and not (term["node"]["kind"] == "application" and term["node"]["label"] == head):
                continue
            matches.append(sentence["provenance"]["lineageId"])
    return matches


def concrete_observation_site(observation: dict[str, Any], lineage: str, template: dict[str, Any]) -> dict[str, Any]:
    payload = {
        "observerDigest": observation["observerDigest"],
        "observerVersion": 1,
        "definitionDigest": observation["inputDefinitionDigest"],
        "targetLineage": lineage,
        "role": template["role"],
        "termPath": template["termPath"],
    }
    return {"siteId": digest("k-in-k/observation-site/v1", payload), "role": template["role"], "termPath": template["termPath"]}


def refresh_structural_observation_cases() -> None:
    definition = load("semantic-definition-counter.json")
    cases = load("structural-observation-cases.json")
    compatibility_digest = digest("k-in-k/compatibility-profile/v1", {"profile": definition["family"]["compatibilityProfile"]})
    for case in cases["cases"]:
        observation = case["manifest"]
        observation["inputDefinitionDigest"] = definition["definitionDigest"]
        observation["compatibilityProfileDigest"] = compatibility_digest
        for selection in observation["selections"]:
            matches = derive_structural_matches(selection["selector"], definition)
            selection["matchedLineages"] = matches
            selection["expectedCardinality"] = len(matches)
        refresh_observation(observation)
        case["expectedSiteIds"] = [
            concrete_observation_site(observation, lineage, emission["semanticSite"])["siteId"]
            for selection in observation["selections"]
            for lineage in selection["matchedLineages"]
            for emission in selection["emissions"]
            if emission["semanticSite"] is not None
        ]
    save("structural-observation-cases.json", cases)


def refresh_baseline_observation_only() -> None:
    observation = load("observation-manifest.json")
    refresh_observation(observation)
    save("observation-manifest.json", observation)
    installation = load("observation-installation-result.json")
    installation["manifestDigest"] = observation["manifestId"]
    installation["outputDefinitionDigest"] = observation["outputDefinitionDigest"]
    installation["installedSelectionIds"] = [item["selectionId"] for item in observation["selections"]]
    installation["appliedSelectionCount"] = len(observation["selections"])
    installation["resultId"] = digest("k-in-k/observation-installation-result/v1", without(installation, "resultId"))
    save("observation-installation-result.json", installation)


def replay_invocation(value: dict[str, Any]) -> dict[str, Any]:
    payload = {key: deepcopy(item) for key, item in value.items() if key not in {"replayId", "invocationDigest", "expectedResultDigest"}}
    payload["steps"] = [{key: deepcopy(item) for key, item in step.items() if key != "expectedArtifacts"} for step in value["steps"]]
    return payload


def refresh_replay(value: dict[str, Any]) -> None:
    if value["kind"] == "pattern-query":
        role_pairs = [
            (["definition"], ["definition"]),
            (["definition", "transformation"], ["instrumented-definition"]),
            (["instrumented-definition", "program"], ["event-trace"]),
            (["event-trace", "pattern-source", "pattern-plan", "pattern-query"], ["pattern-result"]),
        ]
    else:
        diff_digest = next(artifact["digest"] for artifact in value["artifacts"] if artifact["role"] == "structural-diff")
        output_digest = value["mutation"]["outputDefinitionDigest"]
        value["steps"][1]["expectedArtifacts"] = [{"role": "mutant-definition", "digest": output_digest}, {"role": "structural-diff", "digest": diff_digest}]
        value["steps"][2]["inputArtifacts"] = [{"role": "mutant-definition", "digest": output_digest}, {"role": "structural-diff", "digest": diff_digest}]
        value["steps"][2]["expectedArtifacts"] = [{"role": "mutant-definition", "digest": output_digest}, {"role": "structural-diff", "digest": diff_digest}]
        for step in value["steps"][1:]:
            step.pop("expectedArtifactDigests", None)
        value["steps"][2].pop("inputDigests", None)
        role_pairs = [
            (["definition"], ["definition"]),
            (["definition", "patch"], ["mutant-definition", "structural-diff"]),
            (["mutant-definition", "structural-diff"], ["mutant-definition", "structural-diff"]),
        ]
    for step, (input_roles, output_roles) in zip(value["steps"], role_pairs):
        input_digests = step.pop("inputDigests", [item["digest"] for item in step.get("inputArtifacts", [])])
        output_digests = step.pop("expectedArtifactDigests", [item["digest"] for item in step.get("expectedArtifacts", [])])
        step.pop("inputRoles", None)
        step.pop("expectedArtifactRoles", None)
        step["inputArtifacts"] = [{"role": role, "digest": item} for role, item in zip(input_roles, input_digests)]
        step["expectedArtifacts"] = [{"role": role, "digest": item} for role, item in zip(output_roles, output_digests)]
        step["optionsDigest"] = value["optionsDigest"]
    if value["kind"] == "pattern-query":
        value["steps"][0]["inputArtifacts"] = [{"role": "definition", "digest": value["definitionDigest"]}]
        value["steps"][0]["expectedArtifacts"] = deepcopy(value["steps"][0]["inputArtifacts"])
        value["steps"][1]["inputArtifacts"] = [{"role": "definition", "digest": value["definitionDigest"]}, *({"role": "transformation", "digest": item} for item in value["transformationDigests"])]
        value["steps"][2]["inputArtifacts"] = [deepcopy(value["steps"][1]["expectedArtifacts"][0]), {"role": "program", "digest": value["programDigest"]}]
        value["steps"][3]["inputArtifacts"] = [
            deepcopy(value["steps"][2]["expectedArtifacts"][0]),
            deepcopy(value["patternSource"]), deepcopy(value["patternPlan"]), deepcopy(value["patternQuery"]),
        ]
    else:
        value["steps"][0]["inputArtifacts"] = [{"role": "definition", "digest": value["definitionDigest"]}]
        value["steps"][0]["expectedArtifacts"] = deepcopy(value["steps"][0]["inputArtifacts"])
        value["steps"][1]["inputArtifacts"] = [{"role": "definition", "digest": value["definitionDigest"]}, {"role": "patch", "digest": value["mutation"]["patchId"]}]
    artifact_keys_only(value)
    value["invocationDigest"] = digest("k-in-k/replay-invocation/v1", replay_invocation(value))
    value["replayId"] = digest("k-in-k/replay-manifest/v1", without(value, "replayId"))


def set_step_digest(step: dict[str, Any], legacy_name: str, paired_name: str, index: int, artifact_digest: str) -> None:
    if legacy_name in step:
        step[legacy_name][index] = artifact_digest
    else:
        step[paired_name][index]["digest"] = artifact_digest


def replay_closure_record(replay: dict[str, Any], catalog: dict[str, Any]) -> dict[str, Any]:
    requirements = {("definition", replay["definitionDigest"]), ("compatibility-profile", replay["compatibilityProfileDigest"]), ("execution-profile", replay["executionProfileDigest"]), ("options", replay["optionsDigest"])}
    requirements.update(("transformation", item) for item in replay["transformationDigests"])
    for role, field in (("program", "programDigest"), ("parser", "parserDigest"), ("observer", "observerDigest"), ("observation-manifest", "observationManifestDigest"), ("solver-profile", "solverProfileDigest")):
        if replay[field] is not None:
            requirements.add((role, replay[field]))
    for field in ("patternSource", "patternPlan", "patternQuery"):
        if replay[field] is not None:
            requirements.add((replay[field]["role"], replay[field]["digest"]))
    if replay["kind"] == "mutation-instance":
        requirements.update({("mutation-operator", replay["mutation"]["operatorDigest"]), ("patch", replay["mutation"]["patchId"]), *( (item["role"], item["digest"]) for item in replay["artifacts"] )})
    produced: set[tuple[str, str]] = set()
    for step in replay["steps"]:
        requirements.update((item["role"], item["digest"]) for item in step["inputArtifacts"] if (item["role"], item["digest"]) not in produced)
        produced.update((item["role"], item["digest"]) for item in step["expectedArtifacts"])
    by_key = {(entry["role"], entry["digest"]): entry for entry in catalog["entries"]}
    unresolved = sorted(requirements - set(by_key))
    external = sorted(key for key in requirements if key in by_key and by_key[key]["availability"] == "external-required")
    keys = lambda values: [{"role": role, "digest": value} for role, value in values]
    return {"replayId": replay["replayId"], "referentialClosure": not unresolved, "materialClosure": not unresolved and not external, "unresolvedConcreteKeys": keys(unresolved), "externalRequiredInputs": keys(external), "unboundInputs": [], "executionConformance": "not-proven"}


def policy_failure(classification: str, context: str = "candidate-generation") -> dict[str, Any]:
    return {"stage": "selection", "classification": classification, "context": context, "scope": "campaign", "retryability": "never", "semanticEvidence": [], "details": {}}


def build_edit_receipts(operator: dict[str, Any], registry: dict[str, Any], origin: dict[str, Any], patch: dict[str, Any], operator_ref: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    sites = {site["siteId"]: site for site in registry["sites"]}
    operator_ref = operator_ref or {"id": operator["operatorId"], "version": operator["operatorVersion"], "digest": operator["operatorDigest"]}
    receipts: list[dict[str, Any]] = []
    for edit in patch["edits"]:
        affected = edit["position"]["anchorLineage"] if edit["operation"] == "insert-sentence" and edit["position"]["kind"] in ("before-lineage", "after-lineage") else edit["targetLineage"]
        choices = [role for role in operator["patchTemplateRoles"] if role["operation"] == edit["operation"]]
        selected_role = None
        selected_sources = None
        for role in choices:
            available: dict[str, list[tuple[int, int, str]]] = {name: [] for name in role["sourceSelectorRoles"]}
            for tuple_index, discovery_tuple in enumerate(origin["discoveryTuples"]):
                for site_position, site_id in enumerate(discovery_tuple["siteTuple"]):
                    selector_role = sites[site_id]["selectorRole"]
                    if selector_role in available:
                        available[selector_role].append((tuple_index, site_position, site_id))
            if not all(available.values()):
                continue
            selected = [available[name][0] for name in role["sourceSelectorRoles"]]
            if affected not in {sites[item[2]]["sentenceLineage"] for item in selected}:
                for source_index, name in enumerate(role["sourceSelectorRoles"]):
                    matching = [item for item in available[name] if sites[item[2]]["sentenceLineage"] == affected]
                    if matching:
                        selected[source_index] = matching[0]
                        break
            if affected in {sites[item[2]]["sentenceLineage"] for item in selected}:
                selected_role, selected_sources = role, sorted(selected)
                break
        if selected_role is None or selected_sources is None:
            raise AssertionError("no patch-template role authorizes generated edit")
        sources = []
        for tuple_index, _site_position, site_id in selected_sources:
            discovery_tuple = origin["discoveryTuples"][tuple_index]
            sources.append({"discoveryTupleIndex": tuple_index, "siteId": site_id, "selectorRole": sites[site_id]["selectorRole"], "tupleBindings": deepcopy(discovery_tuple["bindings"])})
        receipts.append({"editId": edit["editId"], "operator": deepcopy(operator_ref), "patchTemplateDigest": operator["patchTemplateDigest"], "templateRole": selected_role["name"], "sources": sources})
    return receipts


def instance_payload(operator_ref: dict[str, Any], baseline_digest: str, policy: str, origin: dict[str, Any], patch_id: str) -> dict[str, Any]:
    return {"operatorId": operator_ref["id"], "operatorVersion": operator_ref["version"], "baselineDefinitionDigest": baseline_digest, "policy": policy, "siteTuple": origin["siteTuple"], "discoveryTuples": origin["discoveryTuples"], "patchId": patch_id, "editReceipts": origin["editReceipts"]}


def policy_support(operator: dict[str, Any], registry: dict[str, Any], definition_digest: str) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    def policy_opaque(role: str, label: str) -> str:
        content_hash = raw_sha256(f"BAG-08 synthetic policy {label}\n".encode("ascii"))
        return digest("k-in-k/opaque-artifact/v1", {"role": role, "mediaType": "application/octet-stream", "contentSha256": content_hash})
    requirements = [
        ("definition", definition_digest), ("mutation-operator", operator["operatorDigest"]),
        ("mutation-site-registry", registry["registryId"]),
        ("mutation-module", operator["moduleDigest"]), ("mutation-selector", operator["selectorDigest"]),
        ("precondition", operator["preconditionDigest"]), ("postcondition", operator["postconditionDigest"]),
        ("patch-template", operator["patchTemplateDigest"]),
    ]
    if operator["joinDigest"] is not None:
        requirements.append(("mutation-join", operator["joinDigest"]))
    projection_digest = policy_opaque("oracle-projection", "projection")
    comparison_digest = policy_opaque("oracle-comparison", "comparison")
    program_digest = policy_opaque("program", "program")
    parser_digest = policy_opaque("parser", "parser")
    options_digest = policy_opaque("options", "options")
    oracle_value = {"schemaVersion": 1, "definitionDigest": definition_digest, "value": {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "token", "text": "policy-value"}}}
    oracle_value_digest = digest("k-in-k/oracle-value/v1", oracle_value)
    oracle_value["oracleValueDigest"] = oracle_value_digest
    lowering_profile_digest = policy_opaque("lowering-profile", "lowering-profile")
    requirements.extend([("oracle-projection", projection_digest), ("oracle-comparison", comparison_digest), ("oracle-value", oracle_value_digest), ("program", program_digest), ("parser", parser_digest), ("options", options_digest), ("lowering-profile", lowering_profile_digest)])
    structured = {"definition", "mutation-operator", "mutation-site-registry", "mutation-selector", "mutation-join", "oracle-value"}
    case_id = operator["operatorId"].removeprefix("policy-")
    opaque_labels = {
        operator["moduleDigest"]: f"{case_id}:module", operator["preconditionDigest"]: f"{case_id}:precondition",
        operator["postconditionDigest"]: f"{case_id}:postcondition", operator["patchTemplateDigest"]: f"{case_id}:template",
        projection_digest: "projection", comparison_digest: "comparison", oracle_value_digest: "oracle-value", program_digest: "program", parser_digest: "parser", options_digest: "options", lowering_profile_digest: "lowering-profile",
    }
    entries = []
    for role, value in sorted(requirements):
        model = "canonical-json" if role in structured else "opaque-bytes"
        media_type = "application/json" if model == "canonical-json" else "application/octet-stream"
        content_hash = raw_sha256(canonical(oracle_value).encode("utf-8")) if role == "oracle-value" else raw_sha256((f"BAG-08 synthetic policy {opaque_labels[value]}\n" if value in opaque_labels else f"BAG-08 reviewed synthetic policy pin {role}:{value}\n").encode("ascii"))
        entries.append({"role": role, "digest": value, "contentModel": model, "mediaType": media_type, "contentSha256": content_hash, "availability": "external-required", "logicalPath": f"artifact://policy/{role}/{value}", "resolverId": "rust-artifact-store-v1"})
    catalog = {"schemaVersion": 1, "entries": entries, "unboundRequirements": []}
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(catalog, "catalogId"))
    corpus = {"definitionDigest": definition_digest, "artifactCatalogDigest": catalog["catalogId"], "tests": [], "bounds": {"depth": 1, "timeMs": 1, "branches": 1, "results": 1}}
    corpus["manifestId"] = digest("k-in-k/policy-corpus/v1", without(corpus, "manifestId"))
    oracle = {"oracleId": "policy-oracle", "kind": "final-result", "projectionDigest": projection_digest, "comparisonDigest": comparison_digest, "crashPolicy": "semantic-crash-distinguishes", "baselineTerminalPolicy": "normal-required", "artifacts": [{"role": "oracle-projection", "digest": projection_digest}, {"role": "oracle-comparison", "digest": comparison_digest}]}
    test = {"testId": "policy-test", "programDigest": program_digest, "parserDigest": parser_digest, "startSymbol": "PolicyStart", "optionsDigest": options_digest, "boundsDigest": "76" * 32, "invocationDigest": "77" * 32, "oracleIds": ["policy-oracle"], "patternQueries": []}
    manifest = {"artifactCatalogDigest": catalog["catalogId"], "definitionDigest": definition_digest, "operatorDigest": operator["operatorDigest"], "siteRegistryDigest": registry["registryId"], "corpusManifestDigest": corpus["manifestId"], "loweringProfileDigest": lowering_profile_digest, "loweringEvidence": [], "tests": [test], "oracles": [oracle]}
    manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", manifest)
    return catalog, corpus, manifest


def build_policy_cases(definition_digest: str, base_campaign: dict[str, Any], base_operator: dict[str, Any]) -> dict[str, Any]:
    base_edits = base_campaign["generation"]["candidates"][0]["patch"]["edits"]
    write_lineage, load_lineage = (edit["targetLineage"] for edit in base_edits)
    write_path, load_path = (edit["targetPath"] for edit in base_edits)

    def make_operator(case_id: str, policy: str, join: bool, expected_count: int | None, arity: int, cap: int) -> dict[str, Any]:
        def policy_opaque(role: str, suffix: str) -> str:
            content_hash = raw_sha256(f"BAG-08 synthetic policy {case_id}:{suffix}\n".encode("ascii"))
            return digest("k-in-k/opaque-artifact/v1", {"role": role, "mediaType": "application/octet-stream", "contentSha256": content_hash})
        value = deepcopy(base_operator)
        value.update({"operatorId": f"policy-{case_id}", "policy": policy, "expectedTupleCount": expected_count, "expectedTupleArity": arity, "candidateCap": cap})
        value["moduleDigest"] = policy_opaque("mutation-module", "module")
        value["preconditionDigest"] = policy_opaque("precondition", "precondition")
        value["postconditionDigest"] = policy_opaque("postcondition", "postcondition")
        value["patchTemplateDigest"] = policy_opaque("patch-template", "template")
        value["joinDigest"] = "00" * 32 if join else None
        return value

    def make_site(operator: dict[str, Any], role: str, lineage: str, term_path: list[dict[str, Any]], token: str) -> dict[str, Any]:
        binding = {"name": "X", "term": {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "token", "text": token}}}
        site = {"selectorRole": role, "sentenceLineage": lineage, "termPath": term_path, "bindings": [binding]}
        site["siteId"] = digest("k-in-k/site/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": definition_digest, "targetLineage": lineage, "selectorRole": role, "termPath": term_path, "bindings": [binding]})
        return site

    def make_registry(operator: dict[str, Any], site_specs: list[tuple[str, str, list[dict[str, Any]], str]], tuple_indices: list[list[int]] | None, exhaustive: bool) -> dict[str, Any]:
        roles = list(dict.fromkeys(spec[0] for spec in site_specs)) or ["site"]
        clauses = [{"role": role, "sentenceKinds": ["rule"], "label": role, "termPath": write_path, "termSort": "Int", "termHeadLabel": None, "bindingName": "X"} for role in roles]
        selector = {"selectorDigest": digest("k-in-k/mutation-selector/v1", clauses), "clauses": clauses}
        join = None
        if operator["joinDigest"] is not None:
            join = {"joinDigest": "00" * 32, "kind": "ordered-shared-term", "orderedRoles": roles, "bindingName": "X", "bindingSort": "Int"}
            join["joinDigest"] = digest("k-in-k/mutation-join/v1", without(join, "joinDigest"))
            operator["joinDigest"] = join["joinDigest"]
        operator["selectorDigest"] = selector["selectorDigest"]
        operator["patchTemplateRoles"] = [{"name": "coupled-replacement", "operation": "replace-term", "sourceSelectorRoles": roles}] if len(roles) > 1 else [{"name": "site-replacement", "operation": "replace-term", "sourceSelectorRoles": roles}]
        operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", without(operator, "operatorDigest"))
        sites = [make_site(operator, *spec) for spec in site_specs]
        tuples = [[sites[index]["siteId"] for index in indices] for indices in (tuple_indices if tuple_indices is not None else [[index] for index in range(len(sites))])]
        registry = {"schemaVersion": 1, "registryId": "00" * 32, "definitionDigest": definition_digest, "operatorDigest": operator["operatorDigest"], "selector": selector, "join": join, "discovery": {"exhaustive": exhaustive, "failure": None if exhaustive else policy_failure("incomplete-generation", "mutation-discovery")}, "sites": sites, "tuples": tuples}
        registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", without(registry, "registryId"))
        return registry

    def make_patch(operator: dict[str, Any], edit_indices: list[int]) -> dict[str, Any]:
        edits = [deepcopy(base_edits[index]) for index in edit_indices]
        edits.sort(key=lambda edit: (edit["targetLineage"] or "", canonical(edit["targetPath"]), edit["operation"], edit["editId"]))
        patch = {"schemaVersion": 1, "patchId": "00" * 32, "operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "edits": edits}
        patch["patchId"] = digest("k-in-k/patch/v1", {"schemaVersion": 1, "edits": edits})
        return patch

    def bindings(site_tuple: list[str], registry: dict[str, Any]) -> list[dict[str, Any]]:
        sites = {site["siteId"]: site for site in registry["sites"]}
        by_name = {binding["name"]: binding for site_id in site_tuple for binding in sites[site_id]["bindings"]}
        return [by_name[name] for name in sorted(by_name)]

    def selections(operator: dict[str, Any], registry: dict[str, Any], failed: bool) -> list[dict[str, Any]]:
        if failed:
            return []
        if operator["policy"] == "all-matches":
            return [] if not registry["tuples"] else [{"siteTuple": [item[0] for item in registry["tuples"]], "discoveryTuples": [{"siteTuple": item, "bindings": bindings(item, registry)} for item in registry["tuples"]]}]
        return [{"siteTuple": item, "discoveryTuples": [{"siteTuple": item, "bindings": bindings(item, registry)}]} for item in registry["tuples"]]

    def make_campaign(case_id: str, operator: dict[str, Any], registry: dict[str, Any], patch_choices: list[list[int]], failure: str | None) -> dict[str, Any]:
        derived = selections(operator, registry, failure is not None)
        retained = derived[:operator["candidateCap"]]
        complete = failure is None and registry["discovery"]["exhaustive"] and len(retained) == len(derived)
        groups: dict[str, dict[str, Any]] = {}
        for index, selected in enumerate(retained):
            patch = make_patch(operator, patch_choices[index])
            origin = {"instanceId": "00" * 32, **deepcopy(selected), "editReceipts": []}
            operator_ref = {"id": operator["operatorId"], "version": operator["operatorVersion"], "digest": operator["operatorDigest"]}
            origin["editReceipts"] = build_edit_receipts(operator, registry, origin, patch, operator_ref)
            origin["instanceId"] = digest("k-in-k/instance/v1", instance_payload(operator_ref, definition_digest, operator["policy"], origin, patch["patchId"]))
            candidate = groups.setdefault(patch["patchId"], {"candidateId": digest("k-in-k/candidate/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": definition_digest, "patchId": patch["patchId"]}), "originInstances": [], "patch": patch})
            candidate["originInstances"].append(origin)
        candidates = list(groups.values())
        if failure is not None:
            status = "selection-failed"
            generation_failures = [policy_failure(failure)]
        elif complete:
            status = "complete"
            generation_failures = []
        else:
            status = "incomplete-generation"
            generation_failures = [policy_failure("incomplete-generation")]
        campaign = {
            "schemaVersion": 1, "campaignId": "00" * 32, "reportId": "00" * 32, "manifestDigest": "00" * 32,
            "operator": {"id": operator["operatorId"], "version": operator["operatorVersion"], "digest": operator["operatorDigest"]},
            "schemas": {"identity": 1, "operator": 1, "siteRegistry": 1, "patch": 1, "structuralDiff": 1, "replay": 1, "eventTrace": 1, "patternResult": 1, "mutationCampaign": 1, "failureTaxonomy": 1},
            "scheduleMode": "full", "selectedTestIds": ["policy-test"], "campaignStatus": status, "failures": [],
            "generation": {"siteRegistryDigest": registry["registryId"], "policy": operator["policy"], "complete": complete, "candidateCap": operator["candidateCap"], "derivedInstanceCount": len(derived), "retainedInstanceCount": len(retained), "candidates": candidates, "failures": generation_failures},
            "baseline": {"definitionDigest": definition_digest, "status": "valid", "tests": [{"id": "policy-test", "status": "agree", "oracleIds": ["policy-oracle"]}], "oracleResults": [{"oracleId": "policy-oracle", "kind": "final-result", "projectionDigest": "71" * 32, "comparisonDigest": "72" * 32, "outcome": "agree", "baselineValueDigest": "78" * 32, "mutantValueDigest": "78" * 32, "valueArtifacts": [{"role": "oracle-value", "digest": "78" * 32}, {"role": "oracle-value", "digest": "78" * 32}], "witnessDigest": None, "failure": None}], "failures": []},
            "candidateRejections": [], "mutants": [],
        }
        if complete:
            no_change = policy_failure("incomplete-generation")
            no_change.update({"stage": "operator", "classification": "no-change", "scope": "candidate"})
            campaign["candidateRejections"] = [{"status": "no-change", "patchId": candidate["patch"]["patchId"], "originInstanceIds": [origin["instanceId"] for origin in candidate["originInstances"]], "failures": [deepcopy(no_change)]} for candidate in candidates]
            campaign["score"] = {"killed": 0, "survived": 0, "denominator": 0, "ratio": None, "excluded": {"invalid": 0, "timeout": 0, "unknown": 0, "error": 0, "duplicate": 0, "no-change": len(candidates)}}
        policy_catalog, _, manifest = policy_support(operator, registry, definition_digest)
        declaration = manifest["oracles"][0]
        for oracle_result in campaign["baseline"]["oracleResults"]:
            oracle_result["projectionDigest"] = declaration["projectionDigest"]
            oracle_result["comparisonDigest"] = declaration["comparisonDigest"]
            value_digest = next(entry["digest"] for entry in policy_catalog["entries"] if entry["role"] == "oracle-value")
            oracle_result["baselineValueDigest"] = value_digest
            oracle_result["mutantValueDigest"] = value_digest
            oracle_result["valueArtifacts"] = [{"role": "oracle-value", "digest": value_digest}, {"role": "oracle-value", "digest": value_digest}]
        campaign["manifestDigest"] = manifest["manifestId"]
        campaign_oracles_to_bag09(campaign)
        campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
        campaign["reportId"] = digest("k-in-k/mutation-report/v1", without(campaign, "reportId"))
        return campaign

    specs = [
        ("exact-unary", "exact", False, 1, 1, 4, [("site", write_lineage, write_path, "0")], None, True, [[0]]),
        ("each-multi", "each", False, None, 1, 4, [("site", write_lineage, write_path, "0"), ("site", load_lineage, load_path, "1"), ("site", write_lineage, load_path, "2")], None, True, [[0], [1], [0]]),
        ("tuple-each-supplied", "tuple-each", True, None, 2, 4, [("left", write_lineage, write_path, "0"), ("left", write_lineage, load_path, "1"), ("right", load_lineage, load_path, "0"), ("right", load_lineage, write_path, "1")], [[0, 2], [1, 3]], True, [[0, 1], [0, 1]]),
        ("all-matches-aggregate", "all-matches", False, None, 1, 4, [("site", write_lineage, write_path, "0"), ("site", load_lineage, load_path, "1")], None, True, [[0, 1]]),
        ("deduplicated-patch-origins", "each", False, None, 1, 4, [("site", write_lineage, write_path, "0"), ("site", write_lineage, load_path, "1")], None, True, [[0], [0]]),
        ("exact-zero", "exact", False, 1, 1, 4, [], None, True, []),
        ("exact-excess", "exact", False, 1, 1, 4, [("site", write_lineage, write_path, "0"), ("site", load_lineage, load_path, "1")], None, True, []),
        ("exact-wrong-arity", "exact", False, 1, 2, 4, [("site", write_lineage, write_path, "0")], None, True, []),
        ("cap-prefix", "each", False, None, 1, 2, [("site", write_lineage, write_path, "0"), ("site", load_lineage, load_path, "1"), ("site", write_lineage, load_path, "2")], None, True, [[0], [1]]),
        ("nonexhaustive-prefix", "each", False, None, 1, 4, [("site", write_lineage, write_path, "0"), ("site", load_lineage, load_path, "1")], None, False, [[0], [1]]),
    ]
    cases = []
    for case_id, policy, has_join, count, arity, cap, site_specs, tuple_indices, exhaustive, patches in specs:
        operator = make_operator(case_id, policy, has_join, count, arity, cap)
        registry = make_registry(operator, site_specs, tuple_indices, exhaustive)
        failure = "invalid-join" if case_id == "exact-wrong-arity" else "cardinality-mismatch" if case_id in ("exact-zero", "exact-excess") else None
        campaign = make_campaign(case_id, operator, registry, patches, failure)
        cases.append({"id": case_id, "operator": operator, "siteRegistry": registry, "campaign": campaign})
    return {"schemaVersion": 1, "cases": cases}


def main() -> None:
    prepare_bag12_refresh(ROOT)
    migrate_bag13_inputs()
    refresh_structural_observation_cases()
    write_bag10_contract()
    write_bag11_schemas_and_roles()
    migrate_bag10_inputs()
    opaque = {
        "observer": opaque_material("observer", "observer.bin"),
        "execution-profile": opaque_material("execution-profile", "execution-profile.bin"),
        "lowering-profile": opaque_material("lowering-profile", "lowering-profile.bin"),
        "solver-profile": opaque_material("solver-profile", "solver-profile.bin"),
        "options-default": opaque_material("options", "options-default.bin"),
        "options-write-only": opaque_material("options", "options-write-only.bin"),
        "program-write-load": opaque_material("program", "program-write-load.bin"),
        "program-write-only": opaque_material("program", "program-write-only.bin"),
        "parser": opaque_material("parser", "parser.bin"),
        "pattern-source": opaque_material("pattern-source", "pattern-source.bin"),
        "pattern-side-condition": opaque_material("pattern-side-condition", "pattern-side-condition.bin"),
        "pattern-compiler-profile": opaque_material("pattern-compiler-profile", "pattern-compiler-profile.bin"),
        "module-memory": opaque_material("mutation-module", "mutation-module-memory.bin"),
        "module-counter": opaque_material("mutation-module", "mutation-module-counter.bin"),
        "precondition-memory": opaque_material("precondition", "precondition-memory.bin"),
        "precondition-counter": opaque_material("precondition", "precondition-counter.bin"),
        "postcondition-memory": opaque_material("postcondition", "postcondition-memory.bin"),
        "postcondition-counter": opaque_material("postcondition", "postcondition-counter.bin"),
        "template-memory": opaque_material("patch-template", "patch-template-memory.bin"),
        "template-counter": opaque_material("patch-template", "patch-template-counter.bin"),
        "projection-final": opaque_material("oracle-projection", "oracle-projection-final.bin"),
        "projection-pattern": opaque_material("oracle-projection", "oracle-projection-pattern.bin"),
        "comparison-final": opaque_material("oracle-comparison", "oracle-comparison-final.bin"),
        "comparison-pattern": opaque_material("oracle-comparison", "oracle-comparison-pattern.bin"),
        "oracle-value": opaque_material("oracle-value", "oracle-value.bin"),
        "role-separated-program": opaque_material("program", "program-role-separation.bin"),
    }
    definition = load("semantic-definition-memory.json")
    identity_output_definition = load("semantic-definition-identity-output.json")
    compatibility_digest = digest("k-in-k/compatibility-profile/v1", {"profile": definition["family"]["compatibilityProfile"]})
    operator = load("mutation-operator.json")
    operator["moduleDigest"] = opaque["module-memory"]["digest"]
    operator["preconditionDigest"] = opaque["precondition-memory"]["digest"]
    operator["postconditionDigest"] = opaque["postcondition-memory"]["digest"]
    operator["patchTemplateDigest"] = opaque["template-memory"]["digest"]
    site_registry = load("mutation-site-registry.json")
    selector = site_registry["selector"]
    selector["selectorDigest"] = digest("k-in-k/mutation-selector/v1", selector["clauses"])
    if site_registry["join"] is not None:
        site_registry["join"]["joinDigest"] = digest("k-in-k/mutation-join/v1", without(site_registry["join"], "joinDigest"))
    operator["selectorDigest"] = selector["selectorDigest"]
    operator["joinDigest"] = site_registry["join"]["joinDigest"] if site_registry["join"] is not None else None
    operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", without(operator, "operatorDigest"))
    save("mutation-operator.json", operator)
    site_registry["definitionDigest"] = definition["definitionDigest"]
    site_registry["operatorDigest"] = operator["operatorDigest"]
    sites: list[dict[str, Any]] = []
    site_terms: dict[str, Any] = {}
    sentence_order: dict[str, int] = {}
    for module in definition["modules"]:
        for sentence in module["sentences"]:
            sentence_order[sentence["provenance"]["lineageId"]] = len(sentence_order)
    for clause in selector["clauses"]:
        for module in definition["modules"]:
            for sentence in module["sentences"]:
                generated_allowed = operator["generatedSentencePolicy"] == "include" or (operator["generatedSentencePolicy"] == "only") == sentence["provenance"]["generated"]
                label_matches = clause["label"] is None or sentence["provenance"]["label"] == clause["label"]
                if generated_allowed and label_matches and sentence["value"]["kind"] in clause["sentenceKinds"]:
                    try:
                        term = path_get(sentence, clause["termPath"])
                    except (AssertionError, KeyError, IndexError, TypeError):
                        continue
                    if not (isinstance(term, dict) and term.get("encoding") == "portable-term-v1" and term.get("sort") == clause["termSort"]):
                        continue
                    if clause["termHeadLabel"] is not None and not (term["node"]["kind"] == "application" and term["node"]["label"] == clause["termHeadLabel"]):
                        continue
                    site = {"selectorRole": clause["role"], "sentenceLineage": sentence["provenance"]["lineageId"], "termPath": clause["termPath"], "bindings": [{"name": clause["bindingName"], "term": term}]}
                    site["siteId"] = digest("k-in-k/site/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": definition["definitionDigest"], "targetLineage": site["sentenceLineage"], "selectorRole": site["selectorRole"], "termPath": site["termPath"], "bindings": site["bindings"]})
                    sites.append(site)
                    site_terms[site["siteId"]] = term
    sites.sort(key=lambda site: (sentence_order[site["sentenceLineage"]], site["selectorRole"], canonical(site["termPath"]), site["siteId"]))
    site_registry["sites"] = sites
    if site_registry["join"] is None:
        site_registry["tuples"] = [[site["siteId"]] for site in sites]
    else:
        ordered_roles = site_registry["join"]["orderedRoles"]
        by_role = {role: [site for site in sites if site["selectorRole"] == role] for role in ordered_roles}
        site_registry["tuples"] = [[site["siteId"] for site in combination] for combination in product(*(by_role[role] for role in ordered_roles)) if len({canonical(site_terms[site["siteId"]]) for site in combination}) == 1]
    site_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", without(site_registry, "registryId"))
    save("mutation-site-registry.json", site_registry)

    counter_definition = load("semantic-definition-counter.json")
    generated_definition = load("semantic-definition-generated.json")
    counter_operator = load("counter-mutation-operator.json")
    counter_operator["moduleDigest"] = opaque["module-counter"]["digest"]
    counter_operator["preconditionDigest"] = opaque["precondition-counter"]["digest"]
    counter_operator["postconditionDigest"] = opaque["postcondition-counter"]["digest"]
    counter_operator["patchTemplateDigest"] = opaque["template-counter"]["digest"]
    counter_registry = load("counter-mutation-site-registry.json")
    counter_selector = counter_registry["selector"]
    counter_selector["selectorDigest"] = digest("k-in-k/mutation-selector/v1", counter_selector["clauses"])
    counter_operator["selectorDigest"] = counter_selector["selectorDigest"]
    counter_operator["joinDigest"] = None
    counter_operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", without(counter_operator, "operatorDigest"))
    save("counter-mutation-operator.json", counter_operator)
    counter_registry["definitionDigest"] = counter_definition["definitionDigest"]
    counter_registry["operatorDigest"] = counter_operator["operatorDigest"]
    counter_sites: list[dict[str, Any]] = []
    for clause in counter_selector["clauses"]:
        for module in counter_definition["modules"]:
            for sentence in module["sentences"]:
                generated_allowed = counter_operator["generatedSentencePolicy"] == "include" or (counter_operator["generatedSentencePolicy"] == "only") == sentence["provenance"]["generated"]
                label_matches = clause["label"] is None or sentence["provenance"]["label"] == clause["label"]
                if generated_allowed and label_matches and sentence["value"]["kind"] in clause["sentenceKinds"]:
                    try:
                        term = path_get(sentence, clause["termPath"])
                    except (AssertionError, KeyError, IndexError, TypeError):
                        continue
                    if not (isinstance(term, dict) and term.get("encoding") == "portable-term-v1" and term.get("sort") == clause["termSort"]):
                        continue
                    if clause["termHeadLabel"] is not None and not (term["node"]["kind"] == "application" and term["node"]["label"] == clause["termHeadLabel"]):
                        continue
                    counter_site = {"selectorRole": clause["role"], "sentenceLineage": sentence["provenance"]["lineageId"], "termPath": clause["termPath"], "bindings": [{"name": clause["bindingName"], "term": term}]}
                    counter_site["siteId"] = digest("k-in-k/site/v1", {"operatorId": counter_operator["operatorId"], "operatorVersion": counter_operator["operatorVersion"], "baselineDefinitionDigest": counter_definition["definitionDigest"], "targetLineage": counter_site["sentenceLineage"], "selectorRole": counter_site["selectorRole"], "termPath": counter_site["termPath"], "bindings": counter_site["bindings"]})
                    counter_sites.append(counter_site)
    counter_registry["sites"] = counter_sites
    counter_registry["tuples"] = [[site["siteId"]] for site in counter_sites]
    counter_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", without(counter_registry, "registryId"))
    save("counter-mutation-site-registry.json", counter_registry)
    observation = load("observation-manifest.json")
    mutant_observation = load("mutation-observation-manifest.json")
    ensure_bag11_memory_vocabulary(observation)
    ensure_bag11_memory_vocabulary(mutant_observation)
    observation["observerDigest"] = opaque["observer"]["digest"]
    mutant_observation["observerDigest"] = opaque["observer"]["digest"]
    observation["outputDefinitionDigest"] = definition["definitionDigest"]
    mutant_observation["outputDefinitionDigest"] = load("mutation-campaign.json")["mutants"][0]["outputDefinitionDigest"]
    observation["compatibilityProfileDigest"] = compatibility_digest
    mutant_observation["compatibilityProfileDigest"] = compatibility_digest
    refresh_observation(observation)
    refresh_observation(mutant_observation)
    bag11 = write_bag11_assets(observation, opaque)
    save("observation-manifest.json", observation)
    save("mutation-observation-manifest.json", mutant_observation)

    terminal_state = load("terminal-state.json")
    terminal_state["definitionDigest"] = definition["definitionDigest"]
    terminal_state["terminalStateDigest"] = digest("k-in-k/terminal-state/v1", without(terminal_state, "terminalStateDigest"))
    save("terminal-state.json", terminal_state)
    semantic_crash = load("semantic-crash.json")
    semantic_crash["executionProfileDigest"] = opaque["execution-profile"]["digest"]
    semantic_crash["terminalState"] = {"role": "terminal-state", "digest": terminal_state["terminalStateDigest"]}
    semantic_crash["crashDigest"] = digest("k-in-k/semantic-crash/v1", without(semantic_crash, "crashDigest"))
    save("semantic-crash.json", semantic_crash)
    write_lowering_proof_vectors(definition, load("mutation-campaign.json"), opaque["lowering-profile"]["digest"], opaque["execution-profile"]["digest"])

    catalog = load("artifact-catalog.json")
    catalog["schemaVersion"] = 1
    catalog["unboundRequirements"] = []
    catalog_entries: dict[tuple[str, str], dict[str, Any]] = {}
    structured_sources: dict[tuple[str, str], Any] = {}
    def add_structured_source(role: str, artifact_digest: str, source: Any) -> None:
        structured_sources[(role, artifact_digest)] = source
    add_structured_source("definition", definition["definitionDigest"], definition)
    add_structured_source("definition", counter_definition["definitionDigest"], counter_definition)
    add_structured_source("definition", generated_definition["definitionDigest"], generated_definition)
    add_structured_source("mutant-definition", identity_output_definition["definitionDigest"], identity_output_definition)
    existing_campaign = load("mutation-campaign.json")
    existing_campaign["baseline"]["definitionDigest"] = definition["definitionDigest"]
    for candidate in existing_campaign["generation"]["candidates"]:
        candidate["candidateId"] = digest("k-in-k/candidate/v1", {"operatorId": candidate["patch"]["operatorId"], "operatorVersion": candidate["patch"]["operatorVersion"], "baselineDefinitionDigest": definition["definitionDigest"], "patchId": candidate["patch"]["patchId"]})
    portable_verifier = load_portable_verifier()
    for mutant, candidate in zip(existing_campaign["mutants"], existing_campaign["generation"]["candidates"]):
        mutant["candidateId"] = candidate["candidateId"]
        mutant["patchId"] = candidate["patch"]["patchId"]
        mutant["mutantId"] = digest("k-in-k/mutant/v1", {"baselineDefinitionDigest": definition["definitionDigest"], "patchId": mutant["patchId"]})
        output_definition, derived_diff, patch_failure = portable_verifier.apply_portable_patch(definition, candidate["patch"])
        if patch_failure is not None or output_definition is None or derived_diff is None:
            raise AssertionError(f"campaign fixture patch ceased to be locally well formed: {patch_failure}")
        mutant["outputDefinitionDigest"] = output_definition["definitionDigest"]
        mutant["diff"] = derived_diff
        for artifact in mutant["artifacts"]:
            if artifact["role"] == "structural-diff":
                artifact["digest"] = derived_diff["diffId"]
    save("mutation-campaign.json", existing_campaign)
    save("structural-diff.json", deepcopy(existing_campaign["mutants"][0]["diff"]))
    mutant_patch = existing_campaign["generation"]["candidates"][0]["patch"]
    mutant_definition = materialize_mutant_definition(definition, mutant_patch)
    expected_mutant_digest = existing_campaign["mutants"][0]["outputDefinitionDigest"]
    if mutant_definition["definitionDigest"] != expected_mutant_digest:
        raise AssertionError("portable mutant materialization changed the existing BAG-07 output identity")
    mutant_terminal_state = deepcopy(terminal_state)
    mutant_terminal_state["definitionDigest"] = mutant_definition["definitionDigest"]
    mutant_terminal_state["terminalStateDigest"] = digest("k-in-k/terminal-state/v1", without(mutant_terminal_state, "terminalStateDigest"))
    save("terminal-state-mutant.json", mutant_terminal_state)
    mutant_semantic_crash = deepcopy(semantic_crash)
    mutant_semantic_crash["terminalState"] = {"role": "terminal-state", "digest": mutant_terminal_state["terminalStateDigest"]}
    mutant_semantic_crash["crashDigest"] = digest("k-in-k/semantic-crash/v1", without(mutant_semantic_crash, "crashDigest"))
    save("semantic-crash-mutant.json", mutant_semantic_crash)
    oracle_values = []
    for side, referenced_definition in (("baseline", definition), ("mutant", mutant_definition)):
        oracle_value = {"schemaVersion": 1, "definitionDigest": referenced_definition["definitionDigest"], "value": deepcopy(terminal_state["value"])}
        oracle_value["oracleValueDigest"] = digest("k-in-k/oracle-value/v1", oracle_value)
        save(f"oracle-value-{side}.json", oracle_value)
        oracle_values.append(oracle_value)
    add_structured_source("definition", mutant_definition["definitionDigest"], mutant_definition)
    add_structured_source("compatibility-profile", compatibility_digest, {"profile": definition["family"]["compatibilityProfile"]})
    add_structured_source("terminal-state", terminal_state["terminalStateDigest"], terminal_state)
    add_structured_source("terminal-state", mutant_terminal_state["terminalStateDigest"], mutant_terminal_state)
    for oracle_value in oracle_values:
        add_structured_source("oracle-value", oracle_value["oracleValueDigest"], oracle_value)
    add_structured_source("semantic-crash", semantic_crash["crashDigest"], semantic_crash)
    add_structured_source("semantic-crash", mutant_semantic_crash["crashDigest"], mutant_semantic_crash)
    taxonomy = json.loads((ROOT / "failure-taxonomy.json").read_text(encoding="utf-8"))
    add_structured_source("failure-taxonomy", taxonomy["taxonomyId"], taxonomy)
    for name in ("baseline-cycle", "mutant-cycle"):
        proof = load(f"{name}-lowering-cycle-proof.json")
        receipt = load(f"{name}-lowering-proof-check-receipt.json")
        add_structured_source("lowering-cycle-proof", proof["proofId"], proof)
        add_structured_source("lowering-proof-check-receipt", receipt["receiptId"], receipt)
    for observation_value in (observation, mutant_observation):
        request_digest = digest("k-in-k/observation-request/v1", without(observation_value, "manifestId", "transformationId", "outputDefinitionDigest"))
        transformation = {"kind": "observation-installation", "operatorId": observation_value["observerDigest"], "operatorVersion": 1, "inputDefinitionDigest": observation_value["inputDefinitionDigest"], "manifestDigest": request_digest}
        add_structured_source("observation-manifest", observation_value["manifestId"], observation_value)
        add_structured_source("transformation", observation_value["transformationId"], transformation)
    for plan in bag11["plans"].values():
        add_structured_source("pattern-plan", plan["patternPlanDigest"], plan)
    for query in bag11["queries"].values():
        add_structured_source("pattern-query", query["queryId"], query)
    add_structured_source("side-condition-conformance-table", bag11["table"]["tableDigest"], bag11["table"])
    for operator_value, registry_value in ((operator, site_registry), (counter_operator, counter_registry)):
        add_structured_source("mutation-operator", operator_value["operatorDigest"], operator_value)
        add_structured_source("mutation-selector", operator_value["selectorDigest"], registry_value["selector"])
        if registry_value["join"] is not None:
            add_structured_source("mutation-join", operator_value["joinDigest"], registry_value["join"])
        add_structured_source("mutation-site-registry", registry_value["registryId"], registry_value)
    def add_catalog(role: str, artifact_digest: str | None, content_model: str = "opaque-bytes", material_record: dict[str, str] | None = None, source: Any | None = None, bundled_json: str | None = None) -> None:
        if artifact_digest is None:
            return
        if material_record is not None:
            entry = {"role": role, "digest": artifact_digest, "contentModel": "opaque-bytes", "mediaType": "application/octet-stream", "contentSha256": material_record["contentSha256"], "availability": "bundled", "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{material_record['fileName']}", "resolverId": "repo-v1"}
        elif bundled_json is not None:
            source = source if source is not None else structured_sources[(role, artifact_digest)]
            canonical_bytes = canonical(source).encode("utf-8")
            (MATERIAL / bundled_json).write_bytes(canonical_bytes)
            entry = {"role": role, "digest": artifact_digest, "contentModel": "canonical-json", "mediaType": "application/json", "contentSha256": raw_sha256(canonical_bytes), "availability": "bundled", "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{bundled_json}", "resolverId": "repo-v1"}
        else:
            source = source if source is not None else structured_sources[(role, artifact_digest)]
            entry = {"role": role, "digest": artifact_digest, "contentModel": content_model, "mediaType": "application/json", "contentSha256": raw_sha256(canonical(source).encode("utf-8")), "availability": "external-required", "logicalPath": f"artifact://catalog/{role}/{artifact_digest}", "resolverId": "rust-artifact-store-v1"}
        catalog_entries[(role, artifact_digest)] = entry
    add_catalog("definition", definition["definitionDigest"], "canonical-json")
    add_catalog("definition", counter_definition["definitionDigest"], "canonical-json")
    add_catalog("definition", generated_definition["definitionDigest"], "canonical-json")
    add_catalog("definition", mutant_definition["definitionDigest"], "canonical-json")
    add_catalog("mutant-definition", identity_output_definition["definitionDigest"], "canonical-json")
    add_catalog("compatibility-profile", compatibility_digest, "canonical-json")
    add_catalog("semantic-crash", semantic_crash["crashDigest"], "canonical-json")
    add_catalog("semantic-crash", mutant_semantic_crash["crashDigest"], "canonical-json")
    add_catalog("failure-taxonomy", taxonomy["taxonomyId"], "canonical-json", bundled_json="failure-taxonomy.json")
    for name in ("baseline-cycle", "mutant-cycle"):
        proof = load(f"{name}-lowering-cycle-proof.json")
        receipt = load(f"{name}-lowering-proof-check-receipt.json")
        add_catalog("lowering-cycle-proof", proof["proofId"], "canonical-json", bundled_json=f"{name}-lowering-cycle-proof.json")
        add_catalog("lowering-proof-check-receipt", receipt["receiptId"], "canonical-json", bundled_json=f"{name}-lowering-proof-check-receipt.json")
    add_catalog("terminal-state", terminal_state["terminalStateDigest"], "canonical-json")
    add_catalog("terminal-state", mutant_terminal_state["terminalStateDigest"], "canonical-json")
    for side, oracle_value in zip(("baseline", "mutant"), oracle_values):
        add_catalog("oracle-value", oracle_value["oracleValueDigest"], "canonical-json", bundled_json=f"oracle-value-{side}.json")
    for observation_value in (observation, mutant_observation):
        add_catalog("observer", observation_value["observerDigest"], material_record=opaque["observer"])
        add_catalog("observation-manifest", observation_value["manifestId"], "canonical-json")
        add_catalog("transformation", observation_value["transformationId"], "canonical-json")
    add_catalog("pattern-source", bag11["source"]["digest"], material_record=opaque["pattern-source"])
    add_catalog("pattern-side-condition", bag11["sideArtifact"]["digest"], material_record=opaque["pattern-side-condition"])
    add_catalog("pattern-compiler-profile", opaque["pattern-compiler-profile"]["digest"], material_record=opaque["pattern-compiler-profile"])
    for name in bag11["plans"]:
        plan = bag11["plans"][name]
        query = bag11["queries"][name]
        add_catalog("pattern-plan", plan["patternPlanDigest"], "canonical-json", bundled_json=f"pattern-plan-{name}.json")
        add_catalog("pattern-query", query["queryId"], "canonical-json", bundled_json=f"pattern-query-{name}.json")
    add_catalog("side-condition-conformance-table", bag11["table"]["tableDigest"], "canonical-json", bundled_json="side-condition-conformance-table.json")
    catalog_corpus = load("corpus-manifest.json")
    catalog_corpus.pop("patternDigest", None)
    corpus_query_names = [
        ["write-eventually-load", "single-write", "write-eventually-load"],
        ["single-write"],
    ]
    for test, query_names in zip(catalog_corpus["tests"], corpus_query_names):
        test.pop("patternQuery", None)
        test["patternQueries"] = [bag11_query_root(bag11["queries"][name]) for name in query_names]
    catalog_corpus["patternQueries"] = flatten_test_pattern_queries(catalog_corpus["tests"])
    catalog_corpus["executionProfileDigest"] = opaque["execution-profile"]["digest"]
    catalog_corpus["solverProfileDigest"] = opaque["solver-profile"]["digest"]
    for index, test in enumerate(catalog_corpus["tests"]):
        test["programDigest"] = opaque["program-write-load" if index == 0 else "program-write-only"]["digest"]
        test["parserDigest"] = opaque["parser"]["digest"]
        test["optionsDigest"] = opaque["options-default" if index == 0 else "options-write-only"]["digest"]
    save("corpus-manifest.json", catalog_corpus)
    add_catalog("execution-profile", catalog_corpus["executionProfileDigest"], material_record=opaque["execution-profile"])
    add_catalog("lowering-profile", opaque["lowering-profile"]["digest"], material_record=opaque["lowering-profile"])
    add_catalog("solver-profile", catalog_corpus["solverProfileDigest"], material_record=opaque["solver-profile"])
    for index, test in enumerate(catalog_corpus["tests"]):
        add_catalog("program", test["programDigest"], material_record=opaque["program-write-load" if index == 0 else "program-write-only"])
        add_catalog("parser", test["parserDigest"], material_record=opaque["parser"])
        add_catalog("options", test["optionsDigest"], material_record=opaque["options-default" if index == 0 else "options-write-only"])
    add_catalog("program", opaque["role-separated-program"]["digest"], material_record=opaque["role-separated-program"])
    for operator_value, registry_value in ((operator, site_registry), (counter_operator, counter_registry)):
        add_catalog("mutation-operator", operator_value["operatorDigest"], "canonical-json")
        add_catalog("mutation-module", operator_value["moduleDigest"], material_record=opaque["module-memory" if operator_value is operator else "module-counter"])
        add_catalog("mutation-selector", operator_value["selectorDigest"], "canonical-json", bundled_json="mutation-selector.json" if operator_value is operator else None)
        add_catalog("mutation-join", operator_value["joinDigest"], "canonical-json")
        add_catalog("precondition", operator_value["preconditionDigest"], material_record=opaque["precondition-memory" if operator_value is operator else "precondition-counter"])
        add_catalog("postcondition", operator_value["postconditionDigest"], material_record=opaque["postcondition-memory" if operator_value is operator else "postcondition-counter"])
        add_catalog("patch-template", operator_value["patchTemplateDigest"], material_record=opaque["template-memory" if operator_value is operator else "template-counter"])
        add_catalog("mutation-site-registry", registry_value["registryId"], "canonical-json")
    catalog_mutation_manifest = load("mutation-manifest.json")
    for declaration in catalog_mutation_manifest["oracles"]:
        pattern_oracle = declaration["kind"] == "execution-pattern"
        declaration["projectionDigest"] = opaque["projection-pattern" if pattern_oracle else "projection-final"]["digest"]
        declaration["comparisonDigest"] = opaque["comparison-pattern" if pattern_oracle else "comparison-final"]["digest"]
        declaration["artifacts"] = [{"role": "oracle-projection", "digest": declaration["projectionDigest"]}, {"role": "oracle-comparison", "digest": declaration["comparisonDigest"]}]
        declaration["baselineTerminalPolicy"] = declaration.get("baselineTerminalPolicy", "normal-required")
        if pattern_oracle:
            declaration.update(bag11_query_root(bag11["queries"]["write-eventually-load"]))
        else:
            for field in ("patternSource", "patternPlan", "patternQuery"):
                declaration.pop(field, None)
        add_catalog("oracle-projection", declaration["projectionDigest"], material_record=opaque["projection-pattern" if pattern_oracle else "projection-final"])
        add_catalog("oracle-comparison", declaration["comparisonDigest"], material_record=opaque["comparison-pattern" if pattern_oracle else "comparison-final"])
    for index, test in enumerate(catalog_mutation_manifest["tests"]):
        test["programDigest"] = catalog_corpus["tests"][index]["programDigest"]
        test["parserDigest"] = catalog_corpus["tests"][index]["parserDigest"]
        test["optionsDigest"] = catalog_corpus["tests"][index]["optionsDigest"]
        test["patternQueries"] = mutation_test_pattern_queries(catalog_mutation_manifest, test)
    artifact_keys_only(catalog_mutation_manifest)
    save("mutation-manifest.json", catalog_mutation_manifest)
    catalog_patch = load("patch.json")
    catalog_diff = load("structural-diff.json")
    add_structured_source("patch", catalog_patch["patchId"], catalog_patch)
    add_structured_source("structural-diff", catalog_diff["diffId"], catalog_diff)
    add_catalog("patch", catalog_patch["patchId"], "canonical-json")
    add_catalog("structural-diff", catalog_diff["diffId"], "canonical-json")
    catalog_campaign = load("mutation-campaign.json")
    for candidate in catalog_campaign["generation"]["candidates"]:
        add_catalog("patch", candidate["patch"]["patchId"], "canonical-json", source=candidate["patch"])
    for mutant in catalog_campaign["mutants"]:
        add_catalog("structural-diff", mutant["diff"]["diffId"], "canonical-json", source=mutant["diff"])
    catalog["entries"] = sorted(catalog_entries.values(), key=lambda entry: (entry["role"], entry["digest"]))
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(catalog, "catalogId"))
    save("artifact-catalog.json", catalog)

    installation = load("observation-installation-result.json")
    installation["manifestDigest"] = observation["manifestId"]
    installation["outputDefinitionDigest"] = observation["outputDefinitionDigest"]
    installation["installedSelectionIds"] = [item["selectionId"] for item in observation["selections"]]
    installation["appliedSelectionCount"] = len(observation["selections"])
    installation["resultId"] = digest("k-in-k/observation-installation-result/v1", without(installation, "resultId"))
    save("observation-installation-result.json", installation)

    replay = load("replay-manifest.json")
    write_only_replay = load("write-only-replay-manifest.json")
    mutant_replay = load("mutation-pattern-replay-manifest.json")
    replay_patterns = {
        "replay-manifest.json": load("pattern-result.json"),
        "write-only-replay-manifest.json": load("write-only-pattern-result.json"),
        "mutation-pattern-replay-manifest.json": load("mutation-pattern-result.json"),
    }
    corpus = load("corpus-manifest.json")
    corpus["compatibilityProfileDigest"] = compatibility_digest
    tests = {test["testId"]: test for test in corpus["tests"]}
    for replay_name, item in (("replay-manifest.json", replay), ("write-only-replay-manifest.json", write_only_replay), ("mutation-pattern-replay-manifest.json", mutant_replay)):
        test = tests[item["testId"]]
        query_root = test["patternQueries"][0]
        query = next(query for query in bag11["queries"].values() if query["queryId"] == query_root["patternQuery"]["digest"])
        item["parserDigest"] = test["parserDigest"]
        item["programDigest"] = test["programDigest"]
        item["optionsDigest"] = test["optionsDigest"]
        item["startSymbol"] = test["startSymbol"]
        item["queryId"] = query["queryId"]
        item["executionMode"] = corpus["executionMode"]
        item["observerDigest"] = observation["observerDigest"] if item is not mutant_replay else mutant_observation["observerDigest"]
        item["observationManifestDigest"] = observation["manifestId"] if item is not mutant_replay else mutant_observation["manifestId"]
        item["patternSource"] = deepcopy(query_root["patternSource"])
        item["patternPlan"] = deepcopy(query_root["patternPlan"])
        item["patternQuery"] = deepcopy(query_root["patternQuery"])
        item.pop("patternDigest", None)
        item["artifactCatalogDigest"] = catalog["catalogId"]
        item["compatibilityProfileDigest"] = compatibility_digest
        item["solverProfileDigest"] = corpus["solverProfileDigest"]
        item["executionProfileDigest"] = corpus["executionProfileDigest"]
        item["artifacts"] = [artifact for artifact in item["artifacts"] if artifact["role"] != "pattern"]
        for artifact in item["artifacts"]:
            if artifact["role"] == "program":
                artifact["digest"] = item["programDigest"]
        for field in ("patternSource", "patternPlan", "patternQuery"):
            if item[field] not in item["artifacts"]:
                item["artifacts"].append(deepcopy(item[field]))
    patch_replay = load("mutation-replay-manifest.json")
    patch_replay["parserDigest"] = None
    patch_replay["startSymbol"] = None
    patch_replay["queryId"] = None
    patch_replay["executionMode"] = None
    patch_replay["observerDigest"] = None
    patch_replay["observationManifestDigest"] = None
    patch_replay.pop("patternDigest", None)
    patch_replay["patternSource"] = None
    patch_replay["patternPlan"] = None
    patch_replay["patternQuery"] = None
    patch_replay["transformationDigests"] = []
    patch_replay["artifactCatalogDigest"] = catalog["catalogId"]
    patch_replay["compatibilityProfileDigest"] = compatibility_digest
    patch_replay["solverProfileDigest"] = None
    patch_replay["executionProfileDigest"] = corpus["executionProfileDigest"]
    patch_replay["optionsDigest"] = corpus["tests"][0]["optionsDigest"]
    patch_replay["mutation"]["operatorDigest"] = operator["operatorDigest"]
    replay_campaign = load("mutation-campaign.json")
    replay_candidate = replay_campaign["generation"]["candidates"][0]
    replay_mutant = replay_campaign["mutants"][0]
    patch_replay["definitionDigest"] = replay_campaign["baseline"]["definitionDigest"]
    patch_replay["mutation"].update({"candidateId": replay_candidate["candidateId"], "patchId": replay_candidate["patch"]["patchId"], "mutantId": replay_mutant["mutantId"], "outputDefinitionDigest": replay_mutant["outputDefinitionDigest"]})
    replay_diff_id = replay_mutant["diff"]["diffId"]
    for artifact in patch_replay["artifacts"]:
        if artifact["role"] == "structural-diff":
            artifact["digest"] = replay_diff_id
    for step in patch_replay["steps"]:
        for field in ("inputArtifacts", "expectedArtifacts"):
            for artifact in step[field]:
                if artifact["role"] == "structural-diff":
                    artifact["digest"] = replay_diff_id
    refresh_replay(patch_replay)
    save("mutation-replay-manifest.json", patch_replay)
    replay["transformationDigests"] = [observation["transformationId"]]
    set_step_digest(replay["steps"][1], "inputDigests", "inputArtifacts", 1, observation["transformationId"])
    set_step_digest(replay["steps"][1], "expectedArtifactDigests", "expectedArtifacts", 0, observation["outputDefinitionDigest"])
    write_only_replay["transformationDigests"] = [observation["transformationId"]]
    set_step_digest(write_only_replay["steps"][1], "inputDigests", "inputArtifacts", 1, observation["transformationId"])
    set_step_digest(write_only_replay["steps"][1], "expectedArtifactDigests", "expectedArtifacts", 0, observation["outputDefinitionDigest"])
    mutant_replay["transformationDigests"] = [mutant_observation["transformationId"]]
    set_step_digest(mutant_replay["steps"][1], "inputDigests", "inputArtifacts", 1, mutant_observation["transformationId"])
    set_step_digest(mutant_replay["steps"][1], "expectedArtifactDigests", "expectedArtifacts", 0, mutant_observation["outputDefinitionDigest"])
    refresh_replay(replay)
    refresh_replay(write_only_replay)
    refresh_replay(mutant_replay)

    trace_specs = {
        "baseline": ("event-trace.json", replay),
        "write-only": ("write-only-event-trace.json", write_only_replay),
        "mutant": ("mutation-event-trace.json", mutant_replay),
    }
    trace_digests: dict[str, str] = {}
    for key, (trace_name, trace_replay) in trace_specs.items():
        trace_value = load(trace_name)
        trace_value["definitionDigest"] = trace_replay["definitionDigest"]
        resolved_terminal_state = mutant_terminal_state if key == "mutant" else terminal_state
        trace_value["executionTerminal"] = None if not trace_value["complete"] else {
            "kind": "normal" if trace_value["stopReason"] == "terminal" else "stuck",
            "artifact": {"role": "terminal-state", "digest": resolved_terminal_state["terminalStateDigest"]},
        }
        trace_observation = mutant_observation if key == "mutant" else observation
        for event in trace_value["events"]:
            lineage = event["origin"]["emittingSentence"]["lineageId"]
            emission = next(emission for selection in trace_observation["selections"] if lineage in selection["matchedLineages"] for emission in selection["emissions"] if emission["constructor"] == event["constructor"])
            template = emission["semanticSite"]
            event["origin"]["semanticSite"] = None if template is None else concrete_observation_site(trace_observation, lineage, template)
        trace_value["pathIdentityDigest"] = digest(
            "k-in-k/unkeyed-path/v1",
            without(trace_value, "pathOrdinal", "pathKey", "pathIdentityDigest"),
        )
        save(trace_name, trace_value)
        trace_digest = digest("k-in-k/event-trace/v1", trace_value)
        trace_digests[key] = trace_digest
        if "expectedArtifactDigests" in trace_replay["steps"][-2]:
            trace_replay["steps"][-2]["expectedArtifactDigests"] = [trace_digest]
        else:
            trace_replay["steps"][-2]["expectedArtifacts"] = [{"role": "event-trace", "digest": trace_digest}]
        set_step_digest(trace_replay["steps"][-1], "inputDigests", "inputArtifacts", 0, trace_digest)
        refresh_replay(trace_replay)

    pattern = load("pattern-result.json")
    write_only_pattern = load("write-only-pattern-result.json")
    mutant_pattern = load("mutation-pattern-result.json")
    for pattern_value, trace_name in ((pattern, "event-trace.json"), (write_only_pattern, "write-only-event-trace.json"), (mutant_pattern, "mutation-event-trace.json")):
        resolved_trace = load(trace_name)
        for path in pattern_value["pathResults"]:
            path["executionStopReason"] = "query-satisfied" if path["stopReason"] == "match-found" else path["stopReason"]
            path["executionTerminal"] = deepcopy(resolved_trace["executionTerminal"])
        for witness in pattern_value["witnesses"]:
            witness["executionStopReason"] = "query-satisfied" if witness["stopReason"] == "match-found" else witness["stopReason"]
            witness["events"] = [deepcopy(resolved_trace["events"][index]) for index in witness["eventIndices"]]
        if "primaryWitness" in pattern_value:
            pattern_value["primaryWitness"] = deepcopy(pattern_value["witnesses"][0])
        artifact_keys_only(pattern_value)
    pattern["inputs"]["observationManifestDigest"] = observation["manifestId"]
    pattern["inputs"]["parserDigest"] = tests[pattern["testId"]]["parserDigest"]
    pattern["inputs"]["startSymbol"] = tests[pattern["testId"]]["startSymbol"]
    pattern["inputs"]["compatibilityProfileDigest"] = compatibility_digest
    pattern["inputs"]["solverProfileDigest"] = corpus["solverProfileDigest"]
    pattern["inputs"]["executionMode"] = corpus["executionMode"]
    pattern["inputs"]["transformationId"] = observation["transformationId"]
    pattern["inputs"]["replayInvocationDigest"] = replay["invocationDigest"]
    pattern["inputs"]["observerDigest"] = replay["observerDigest"]
    pattern["inputs"]["definitionDigest"] = replay["definitionDigest"]
    pattern_query = bag11["queries"]["write-eventually-load"]
    pattern["queryId"] = pattern_query["queryId"]
    pattern["inputs"].pop("patternDigest", None)
    pattern["inputs"].update(bag11_query_root(pattern_query))
    pattern["inputs"]["programDigest"] = replay["programDigest"]
    pattern["inputs"]["optionsDigest"] = replay["optionsDigest"]
    pattern["inputs"]["executionProfileDigest"] = replay["executionProfileDigest"]
    pattern["inputs"]["artifacts"][0]["digest"] = trace_digests["baseline"]
    pattern["pathResults"][0]["traceDigest"] = trace_digests["baseline"]
    pattern["pathResults"][0]["pathIdentityDigest"] = load("event-trace.json")["pathIdentityDigest"]
    pattern["witnesses"] = bag11_fixture_witnesses(bag11["plans"]["write-eventually-load"], load("event-trace.json"), pattern["pathResults"][0])
    pattern["primaryWitness"] = deepcopy(pattern["witnesses"][0])
    pattern["resultId"] = digest("k-in-k/pattern-result/v1", without(pattern, "resultId"))
    write_only_pattern["inputs"]["observationManifestDigest"] = observation["manifestId"]
    write_only_pattern["inputs"]["parserDigest"] = tests[write_only_pattern["testId"]]["parserDigest"]
    write_only_pattern["inputs"]["startSymbol"] = tests[write_only_pattern["testId"]]["startSymbol"]
    write_only_pattern["inputs"]["compatibilityProfileDigest"] = compatibility_digest
    write_only_pattern["inputs"]["solverProfileDigest"] = corpus["solverProfileDigest"]
    write_only_pattern["inputs"]["executionMode"] = corpus["executionMode"]
    write_only_pattern["inputs"]["transformationId"] = observation["transformationId"]
    write_only_pattern["inputs"]["replayInvocationDigest"] = write_only_replay["invocationDigest"]
    write_only_pattern["inputs"]["observerDigest"] = write_only_replay["observerDigest"]
    write_only_pattern["inputs"]["definitionDigest"] = write_only_replay["definitionDigest"]
    write_only_query = bag11["queries"]["single-write"]
    write_only_pattern["queryId"] = write_only_query["queryId"]
    write_only_pattern["inputs"].pop("patternDigest", None)
    write_only_pattern["inputs"].update(bag11_query_root(write_only_query))
    write_only_pattern["inputs"]["programDigest"] = write_only_replay["programDigest"]
    write_only_pattern["inputs"]["optionsDigest"] = write_only_replay["optionsDigest"]
    write_only_pattern["inputs"]["executionProfileDigest"] = write_only_replay["executionProfileDigest"]
    write_only_pattern["inputs"]["artifacts"][0]["digest"] = trace_digests["write-only"]
    write_only_pattern["pathResults"][0]["traceDigest"] = trace_digests["write-only"]
    write_only_pattern["pathResults"][0]["pathIdentityDigest"] = load("write-only-event-trace.json")["pathIdentityDigest"]
    write_only_pattern["witnesses"] = bag11_fixture_witnesses(bag11["plans"]["single-write"], load("write-only-event-trace.json"), write_only_pattern["pathResults"][0])
    write_only_pattern.pop("primaryWitness", None)
    write_only_pattern["resultId"] = digest("k-in-k/pattern-result/v1", without(write_only_pattern, "resultId"))
    mutant_pattern["inputs"]["observationManifestDigest"] = mutant_observation["manifestId"]
    mutant_pattern["inputs"]["parserDigest"] = tests[mutant_pattern["testId"]]["parserDigest"]
    mutant_pattern["inputs"]["startSymbol"] = tests[mutant_pattern["testId"]]["startSymbol"]
    mutant_pattern["inputs"]["compatibilityProfileDigest"] = compatibility_digest
    mutant_pattern["inputs"]["solverProfileDigest"] = corpus["solverProfileDigest"]
    mutant_pattern["inputs"]["executionMode"] = corpus["executionMode"]
    mutant_pattern["inputs"]["transformationId"] = mutant_observation["transformationId"]
    mutant_pattern["inputs"]["replayInvocationDigest"] = mutant_replay["invocationDigest"]
    mutant_pattern["inputs"]["observerDigest"] = mutant_replay["observerDigest"]
    mutant_pattern["inputs"]["definitionDigest"] = mutant_replay["definitionDigest"]
    mutant_pattern["queryId"] = pattern_query["queryId"]
    mutant_pattern["inputs"].pop("patternDigest", None)
    mutant_pattern["inputs"].update(bag11_query_root(pattern_query))
    mutant_pattern["inputs"]["programDigest"] = mutant_replay["programDigest"]
    mutant_pattern["inputs"]["optionsDigest"] = mutant_replay["optionsDigest"]
    mutant_pattern["inputs"]["executionProfileDigest"] = mutant_replay["executionProfileDigest"]
    mutant_pattern["inputs"]["artifacts"][0]["digest"] = trace_digests["mutant"]
    mutant_pattern["pathResults"][0]["traceDigest"] = trace_digests["mutant"]
    mutant_pattern["pathResults"][0]["pathIdentityDigest"] = load("mutation-event-trace.json")["pathIdentityDigest"]
    mutant_pattern["witnesses"] = bag11_fixture_witnesses(bag11["plans"]["write-eventually-load"], load("mutation-event-trace.json"), mutant_pattern["pathResults"][0])
    mutant_pattern.pop("primaryWitness", None)
    mutant_pattern["resultId"] = digest("k-in-k/pattern-result/v1", without(mutant_pattern, "resultId"))
    save("pattern-result.json", pattern)
    save("write-only-pattern-result.json", write_only_pattern)
    save("mutation-pattern-result.json", mutant_pattern)

    replay["expectedResultDigest"] = pattern["resultId"]
    replay["steps"][-1]["expectedArtifacts"] = [{"role": "pattern-result", "digest": pattern["resultId"]}]
    replay["steps"][-1].pop("expectedArtifactDigests", None)
    write_only_replay["expectedResultDigest"] = write_only_pattern["resultId"]
    write_only_replay["steps"][-1]["expectedArtifacts"] = [{"role": "pattern-result", "digest": write_only_pattern["resultId"]}]
    write_only_replay["steps"][-1].pop("expectedArtifactDigests", None)
    mutant_replay["expectedResultDigest"] = mutant_pattern["resultId"]
    mutant_replay["steps"][-1]["expectedArtifacts"] = [{"role": "pattern-result", "digest": mutant_pattern["resultId"]}]
    mutant_replay["steps"][-1].pop("expectedArtifactDigests", None)
    refresh_replay(replay)
    refresh_replay(write_only_replay)
    refresh_replay(mutant_replay)
    save("replay-manifest.json", replay)
    save("write-only-replay-manifest.json", write_only_replay)
    save("mutation-pattern-replay-manifest.json", mutant_replay)
    closure_records = [replay_closure_record(item, catalog) for item in (replay, write_only_replay, patch_replay, mutant_replay)]
    closure_records.sort(key=lambda item: item["replayId"])
    save("replay-closure.json", {"schemaVersion": 1, "records": closure_records})

    corpus["observationManifestDigest"] = observation["manifestId"]
    corpus["artifactCatalogDigest"] = catalog["catalogId"]
    corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", without(corpus, "manifestId"))
    save("corpus-manifest.json", corpus)

    corpus_result = load("corpus-result.json")
    corpus_result["manifestDigest"] = corpus["manifestId"]
    corpus_result["components"][0]["patternResultDigest"] = pattern["resultId"]
    corpus_result["components"][0]["pathResults"][0]["patternResultDigest"] = pattern["resultId"]
    corpus_result["components"][0]["pathResults"][0]["pathOrdinal"] = pattern["pathResults"][0]["pathOrdinal"]
    corpus_result["components"][0]["pathResults"][0]["pathIdentityDigest"] = pattern["pathResults"][0]["pathIdentityDigest"]
    corpus_result["components"][0]["pathResults"][0]["executionStopReason"] = pattern["pathResults"][0]["executionStopReason"]
    corpus_result["components"][0]["matchingPathOrdinals"] = [path["pathOrdinal"] for path in pattern["pathResults"] if path["status"] == "match"]
    corpus_result["components"][1]["patternResultDigest"] = write_only_pattern["resultId"]
    corpus_result["components"][1]["pathResults"][0]["patternResultDigest"] = write_only_pattern["resultId"]
    corpus_result["components"][1]["pathResults"][0]["pathOrdinal"] = write_only_pattern["pathResults"][0]["pathOrdinal"]
    corpus_result["components"][1]["pathResults"][0]["pathIdentityDigest"] = write_only_pattern["pathResults"][0]["pathIdentityDigest"]
    corpus_result["components"][1]["pathResults"][0]["executionStopReason"] = write_only_pattern["pathResults"][0]["executionStopReason"]
    corpus_result["components"][1]["matchingPathOrdinals"] = [path["pathOrdinal"] for path in write_only_pattern["pathResults"] if path["status"] == "match"]
    corpus_result["resultId"] = digest("k-in-k/corpus-result/v1", without(corpus_result, "resultId"))
    save("corpus-result.json", corpus_result)

    mutation_manifest = load("mutation-manifest.json")
    mutation_manifest["artifactCatalogDigest"] = catalog["catalogId"]
    mutation_manifest["definitionDigest"] = definition["definitionDigest"]
    mutation_manifest["operatorDigest"] = operator["operatorDigest"]
    mutation_manifest["siteRegistryDigest"] = site_registry["registryId"]
    mutation_manifest["corpusManifestDigest"] = corpus["manifestId"]
    mutation_manifest["loweringProfileDigest"] = opaque["lowering-profile"]["digest"]
    mutant_proof = load("mutant-cycle-lowering-cycle-proof.json")
    mutant_receipt = load("mutant-cycle-lowering-proof-check-receipt.json")
    mutation_manifest["loweringEvidence"] = [
        {"role": "lowering-cycle-proof", "digest": mutant_proof["proofId"]},
        {"role": "lowering-proof-check-receipt", "digest": mutant_receipt["receiptId"]},
    ]
    for test in mutation_manifest["tests"]:
        corpus_test = tests[test["testId"]]
        test["parserDigest"] = corpus_test["parserDigest"]
        test["startSymbol"] = corpus_test["startSymbol"]
        test["boundsDigest"] = digest("k-in-k/bounds/v1", corpus["bounds"])
        test["patternQueries"] = mutation_test_pattern_queries(mutation_manifest, test)
        invocation = {"testId": test["testId"], "programDigest": test["programDigest"], "parserDigest": test["parserDigest"], "startSymbol": test["startSymbol"], "optionsDigest": test["optionsDigest"], "bounds": corpus["bounds"], "executionMode": corpus["executionMode"], "solverProfileDigest": corpus["solverProfileDigest"], "executionProfileDigest": corpus["executionProfileDigest"], "compatibilityProfileDigest": corpus["compatibilityProfileDigest"], "observationManifestDigest": corpus["observationManifestDigest"], "patternQueries": test["patternQueries"]}
        test["invocationDigest"] = digest("k-in-k/test-invocation/v1", invocation)
    mutation_manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", without(mutation_manifest, "manifestId"))
    save("mutation-manifest.json", mutation_manifest)

    execution_policy = load("mutation-execution-policy.json")
    operator = load("mutation-operator.json")
    patch = load("patch.json")
    old_isolation = execution_policy.pop("isolation", None)
    isolation = execution_policy.get("isolationPolicy")
    if isolation is None:
        isolation = {"schemaVersion": 1, **old_isolation}
        execution_policy["isolationPolicy"] = isolation
    isolation["isolationPolicyDigest"] = digest(
        "k-in-k/isolation-policy/v1",
        without(isolation, "isolationPolicyDigest"),
    )
    execution_policy.pop("cacheKey", None)
    execution_policy["policyId"] = digest(
        "k-in-k/mutation-execution-policy/v1",
        without(execution_policy, "policyId"),
    )
    save("mutation-execution-policy.json", execution_policy)

    campaign = load("mutation-campaign.json")
    campaign_oracles_to_legacy(campaign)
    campaign["operator"]["digest"] = operator["operatorDigest"]
    campaign["manifestDigest"] = mutation_manifest["manifestId"]
    campaign["schemas"]["siteRegistry"] = 1
    campaign["generation"]["siteRegistryDigest"] = site_registry["registryId"]
    campaign["generation"]["derivedInstanceCount"] = len(site_registry["tuples"])
    campaign["generation"]["retainedInstanceCount"] = min(len(site_registry["tuples"]), campaign["generation"]["candidateCap"])
    oracle_declarations = {item["oracleId"]: item for item in mutation_manifest["oracles"]}
    baseline_oracle_value_digest, mutant_oracle_value_digest = (value["oracleValueDigest"] for value in oracle_values)
    for owner in [campaign["baseline"], *campaign["mutants"]]:
        for oracle_result in owner["oracleResults"]:
            declaration = oracle_declarations[oracle_result["oracleId"]]
            oracle_result["projectionDigest"] = declaration["projectionDigest"]
            oracle_result["comparisonDigest"] = declaration["comparisonDigest"]
            if oracle_result["kind"] != "execution-pattern":
                if oracle_result["baselineValueDigest"] is not None:
                    oracle_result["baselineValueDigest"] = baseline_oracle_value_digest
                if oracle_result["mutantValueDigest"] is not None:
                    oracle_result["mutantValueDigest"] = baseline_oracle_value_digest if owner is campaign["baseline"] else mutant_oracle_value_digest
    manifest_tests = {test["testId"]: test for test in mutation_manifest["tests"]}
    for candidate in campaign["generation"]["candidates"]:
        candidate["candidateId"] = digest("k-in-k/candidate/v1", {"operatorId": campaign["operator"]["id"], "operatorVersion": campaign["operator"]["version"], "baselineDefinitionDigest": campaign["baseline"]["definitionDigest"], "patchId": candidate["patch"]["patchId"]})
        for origin, site_tuple in zip(candidate["originInstances"], site_registry["tuples"]):
            origin["siteTuple"] = site_tuple
            sites_by_id = {site["siteId"]: site for site in site_registry["sites"]}
            bindings_by_name = {binding["name"]: binding for site_id in site_tuple for binding in sites_by_id[site_id]["bindings"]}
            origin.pop("bindings", None)
            origin["discoveryTuples"] = [{"siteTuple": site_tuple, "bindings": [bindings_by_name[name] for name in sorted(bindings_by_name)]}]
            origin.pop("producedEditIds", None)
            origin["editReceipts"] = build_edit_receipts(operator, site_registry, origin, candidate["patch"], campaign["operator"])
            origin["instanceId"] = digest("k-in-k/instance/v1", instance_payload(campaign["operator"], campaign["baseline"]["definitionDigest"], campaign["generation"]["policy"], origin, candidate["patch"]["patchId"]))
    candidates_by_patch = {candidate["patch"]["patchId"]: candidate for candidate in campaign["generation"]["candidates"]}
    for mutant in campaign["mutants"]:
        mutant["candidateId"] = candidates_by_patch[mutant["patchId"]]["candidateId"]
        mutant["mutantId"] = digest("k-in-k/mutant/v1", {"baselineDefinitionDigest": campaign["baseline"]["definitionDigest"], "patchId": mutant["patchId"]})
    for report_test in campaign["baseline"]["tests"]:
        if "boundsDigest" in report_test:
            report_test["boundsDigest"] = manifest_tests[report_test["id"]]["boundsDigest"]
        if "invocationDigest" in report_test:
            report_test["invocationDigest"] = manifest_tests[report_test["id"]]["invocationDigest"]
    for mutant in campaign["mutants"]:
        mutant["replayManifestDigest"] = patch_replay["replayId"]
        for report_test in mutant["tests"]:
            report_test["boundsDigest"] = manifest_tests[report_test["id"]]["boundsDigest"]
            report_test["invocationDigest"] = manifest_tests[report_test["id"]]["invocationDigest"]
    for oracle in campaign["baseline"]["oracleResults"]:
        if oracle["kind"] == "execution-pattern":
            oracle["baselineValueDigest"] = pattern["resultId"]
            oracle["mutantValueDigest"] = pattern["resultId"]
            oracle["witnessDigest"] = pattern["resultId"]
    for mutant in campaign["mutants"]:
        for oracle in mutant["oracleResults"]:
            if oracle["kind"] == "execution-pattern":
                oracle["baselineValueDigest"] = pattern["resultId"]
                oracle["mutantValueDigest"] = mutant_pattern["resultId"]
                oracle["witnessDigest"] = pattern["resultId"]
    for owner in [campaign["baseline"], *campaign["mutants"]]:
        for oracle_result in owner["oracleResults"]:
            oracle_result["valueArtifacts"] = []
            value_role = "pattern-result" if oracle_result["kind"] == "execution-pattern" else "oracle-value"
            for field in ("baselineValueDigest", "mutantValueDigest"):
                if oracle_result[field] is not None:
                    oracle_result["valueArtifacts"].append({"role": value_role, "digest": oracle_result[field]})
    artifact_keys_only(campaign)
    campaign_oracles_to_bag09(campaign)
    campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
    campaign["reportId"] = digest("k-in-k/mutation-report/v1", without(campaign, "reportId"))
    save("mutation-campaign.json", campaign)
    save("mutation-policy-cases.json", build_policy_cases(definition["definitionDigest"], campaign, operator))
    refresh_bag13_patch_vector_outputs()
    finalize_bag12_refresh(ROOT)
    finalize_bag14_refresh(ROOT)


if __name__ == "__main__":
    if sys.argv[1:] == ["--structural-observation-only"]:
        refresh_structural_observation_cases()
    elif sys.argv[1:] == ["--baseline-observation-only"]:
        refresh_baseline_observation_only()
    elif sys.argv[1:]:
        raise SystemExit("usage: refresh_fixture_ids.py [--baseline-observation-only|--structural-observation-only]")
    else:
        main()
