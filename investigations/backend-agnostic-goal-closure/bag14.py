#!/usr/bin/env python3
"""Portable BAG-14 cache identities, completeness records, and schedules.

This module only constructs and checks deterministic JSON evidence.  It does
not execute K, a compiler, an adapter, a solver, or a cache implementation.
"""

from __future__ import annotations

import hashlib
import json
import unicodedata
from copy import deepcopy
from pathlib import Path
from typing import Any, Callable


DIGEST_REF = {"$ref": "common.schema.json#/$defs/digest"}
ARTIFACT_REF = {"$ref": "common.schema.json#/$defs/artifactKey"}
TERM_REF = {"$ref": "common.schema.json#/$defs/term"}
NEW_ROLES = {
    "cache-campaign-invocation",
    "cache-campaign-manifest",
    "cache-record",
    "cache-mutation-report",
}
DOMAINS = {
    "execution-attempt": "k-in-k/execution-attempt-key/v1",
    "oracle-evaluation": "k-in-k/oracle-evaluation-key/v1",
}
ADVERSARY_NAMES = (
    "schedule-record-as-attempt", "first-kill-as-full", "fabricated-skipped-record",
    "subject-reversal", "candidate-id-drift", "patch-drift", "mutant-definition-drift",
    "test-invocation-drift", "profile-drift", "bounds-drift", "declaration-drift",
    "missing-produced-artifact", "partial-output-complete", "diagnostic-reused-as-agreement",
    "bounded-under-different-bounds", "conflicting-same-key", "refreshed-id-concealment",
    "output-in-attempt-key", "status-in-attempt-key", "schedule-in-raw-key", "hit-in-raw-key",
    "schedule-omitted-invocation", "schedule-omitted-report", "parser-drift", "start-symbol-drift",
    "options-drift", "lowering-drift", "solver-drift", "isolation-drift", "observer-order-drift",
    "attempt-kind-drift", "query-coupling-drift", "search-policy-drift", "operation-version-drift",
    "oracle-operand-order", "baseline-policy-drift", "evaluator-drift", "wrong-resolver-material",
    "boolean-completion", "missing-baseline-gate", "cached-fold-difference",
    "query-kind-reuse", "suite-level-boolean-hit", "duplicate-json-key", "nonportable-json-value",
    "terminal-output-substitution", "oracle-output-substitution", "requested-plan-reorder", "status-self-assertion",
    "operator-template-operation-drift", "operator-selected-site-drift", "operation-id-drift",
    "adapter-version-drift", "evaluator-id-drift", "same-key-output-conflict",
    "same-key-provenance-conflict", "definition-semantic-id-drift", "selector-semantic-id-drift",
    "operator-semantic-id-drift", "edit-semantic-id-drift", "patch-semantic-id-drift",
    "mutant-materialization-drift", "terminal-semantic-id-drift", "trace-semantic-id-drift",
    "declaration-semantic-id-drift", "operand-semantic-id-drift", "gate-outcome-drift",
    "comparison-outcome-drift", "incoherent-query-triple", "declaration-slot-reorder",
    "declaration-slot-removal", "crash-profile-drift", "crash-terminal-drift",
    "crash-side-role-drift", "crash-producer-trace-drift",
    "same-key-normal-crash-result-substitution", "fabricated-query-test-slot",
    "swapped-crash-comparison", "mutant-crash-baseline-gate", "normal-only-crash-policy-drift",
    "crash-policy-drift", "catalog-key-self-id-mismatch",
    "same-key-altered-execution-terminal-trace-row",
)


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def digest(domain: str, value: Any) -> str:
    normalized = unicodedata.normalize("NFC", canonical(value)).encode("utf-8")
    return hashlib.sha256(domain.encode("utf-8") + b"\0" + normalized).hexdigest()


def without(value: dict[str, Any], *fields: str) -> dict[str, Any]:
    return {name: deepcopy(item) for name, item in value.items() if name not in fields}


def key(role: str, identity: str) -> dict[str, str]:
    return {"role": role, "digest": identity}


def typed_key(role: str) -> dict[str, Any]:
    return obj(["role", "digest"], {"role": {"const": role}, "digest": DIGEST_REF})


def obj(required: list[str], properties: dict[str, Any], **extra: Any) -> dict[str, Any]:
    return {"type": "object", "additionalProperties": False, "required": required, "properties": properties, **extra}


def array(items: dict[str, Any], minimum: int = 0, unique: bool = False) -> dict[str, Any]:
    result: dict[str, Any] = {"type": "array", "items": items}
    if minimum:
        result["minItems"] = minimum
    if unique:
        result["uniqueItems"] = True
    return result


def operation_schema() -> dict[str, Any]:
    return obj(
        ["operationId", "operationVersion", "adapterId", "adapterVersion"],
        {
            "operationId": {"type": "string", "minLength": 1},
            "operationVersion": {"type": "integer", "minimum": 1},
            "adapterId": {"type": "string", "minLength": 1},
            "adapterVersion": {"type": "integer", "minimum": 1},
        },
    )


def isolation_schema() -> dict[str, Any]:
    return obj(
        ["schemaVersion", "isolationPolicyDigest", "baselineState", "mutantState", "sharedWritableState", "observerState"],
        {
            "schemaVersion": {"const": 1},
            "isolationPolicyDigest": DIGEST_REF,
            "baselineState": {"const": "immutable"},
            "mutantState": {"const": "fresh-per-mutant"},
            "sharedWritableState": {"const": False},
            "observerState": {"const": "fresh-per-test-path"},
        },
    )


def subject_schema() -> dict[str, Any]:
    baseline = obj(
        ["kind", "definition"],
        {"kind": {"const": "baseline"}, "definition": typed_key("definition")},
    )
    mutant = obj(
        ["kind", "baselineDefinition", "candidateId", "operator", "patch", "mutantId", "mutantDefinition"],
        {
            "kind": {"const": "mutant"},
            "baselineDefinition": typed_key("definition"),
            "candidateId": DIGEST_REF,
            "operator": typed_key("mutation-operator"),
            "patch": typed_key("patch"),
            "mutantId": DIGEST_REF,
            "mutantDefinition": typed_key("mutant-definition"),
        },
    )
    return {"oneOf": [baseline, mutant]}


def attempt_kind_schema() -> dict[str, Any]:
    observations = array(ARTIFACT_REF, minimum=1, unique=True)
    ordinary = obj(["kind"], {"kind": {"const": "ordinary"}})
    exhaustive = obj(
        ["kind", "observationInputs"],
        {"kind": {"const": "observed-exhaustive"}, "observationInputs": observations},
    )
    coupled = obj(
        ["kind", "observationInputs", "patternSource", "patternPlan", "patternQuery", "searchPolicy"],
        {
            "kind": {"const": "query-coupled"},
            "observationInputs": observations,
            "patternSource": typed_key("pattern-source"),
            "patternPlan": typed_key("pattern-plan"),
            "patternQuery": typed_key("pattern-query"),
            "searchPolicy": {"enum": ["exhaustive", "existential-first"]},
        },
    )
    return {"oneOf": [ordinary, exhaustive, coupled]}


def execution_key_schema() -> dict[str, Any]:
    fields = [
        "schemaVersion", "keyDigest", "operation", "subject", "testInvocationDigest",
        "compatibilityProfileDigest", "loweringProfileDigest", "executionProfileDigest",
        "solverProfileDigest", "isolationPolicy", "attemptKind",
    ]
    return obj(
        fields,
        {
            "schemaVersion": {"const": 1},
            "keyDigest": DIGEST_REF,
            "operation": operation_schema(),
            "subject": subject_schema(),
            "testInvocationDigest": DIGEST_REF,
            "compatibilityProfileDigest": DIGEST_REF,
            "loweringProfileDigest": DIGEST_REF,
            "executionProfileDigest": DIGEST_REF,
            "solverProfileDigest": DIGEST_REF,
            "isolationPolicy": isolation_schema(),
            "attemptKind": attempt_kind_schema(),
        },
    )


def semantic_input_schema(side: str) -> dict[str, Any]:
    return obj(
        ["side", "value"],
        {
            "side": {"const": side},
            "value": {"oneOf": [typed_key("oracle-operand"), typed_key("semantic-crash")]},
        },
    )


def oracle_key_schema() -> dict[str, Any]:
    admission_inputs = {"type": "array", "prefixItems": [semantic_input_schema("baseline")], "items": False, "minItems": 1, "maxItems": 1}
    comparison_inputs = {"type": "array", "prefixItems": [semantic_input_schema("baseline"), semantic_input_schema("mutant")], "items": False, "minItems": 2, "maxItems": 2}
    builtin = obj(
        ["evaluatorId", "evaluatorVersion", "mode"],
        {"evaluatorId": {"type": "string", "minLength": 1}, "evaluatorVersion": {"type": "integer", "minimum": 1}, "mode": {"const": "built-in"}},
    )
    authored = obj(
        ["evaluatorId", "evaluatorVersion", "mode", "conformance"],
        {"evaluatorId": {"type": "string", "minLength": 1}, "evaluatorVersion": {"type": "integer", "minimum": 1}, "mode": {"const": "k-authored"}, "conformance": typed_key("oracle-evaluator-conformance")},
    )
    common = {
        "schemaVersion": {"const": 1},
        "keyDigest": DIGEST_REF,
        "operation": operation_schema(),
        "declaration": typed_key("oracle-declaration"),
        "evaluator": {"oneOf": [builtin, authored]},
    }
    admission = obj(
        ["schemaVersion", "keyDigest", "operation", "evaluationKind", "declaration", "semanticInputs", "evaluator"],
        {**common, "evaluationKind": {"const": "baseline-admission"}, "semanticInputs": admission_inputs},
    )
    comparison = obj(
        ["schemaVersion", "keyDigest", "operation", "evaluationKind", "declaration", "semanticInputs", "evaluator"],
        {**common, "evaluationKind": {"const": "baseline-mutant-comparison"}, "semanticInputs": comparison_inputs},
    )
    return {"oneOf": [admission, comparison]}


def terminal_record_schema() -> dict[str, Any]:
    execution_failure = {
        "oneOf": [
            {"$ref": "common.schema.json#/$defs/baselineExecutionFailure"},
            {"$ref": "common.schema.json#/$defs/mutantExecutionFailure"},
        ]
    }
    oracle_failure = {
        "oneOf": [
            {"$ref": "common.schema.json#/$defs/oracleOperandProductionFailure"},
            {"$ref": "common.schema.json#/$defs/oracleComparisonFailure"},
        ]
    }
    execution = {"oneOf": [
        obj(["kind", "terminal"], {"kind": {"enum": ["normal", "stuck"]}, "terminal": typed_key("terminal-state")}),
        obj(["kind", "crash"], {"kind": {"const": "semantic-crash"}, "crash": typed_key("semantic-crash")}),
        obj(["kind", "classification", "boundsDigest", "failure"], {"kind": {"const": "bounded-stop"}, "classification": {"enum": ["depth-limit", "time-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown"]}, "boundsDigest": DIGEST_REF, "failure": execution_failure}),
        obj(["kind", "failure"], {"kind": {"const": "diagnostic-only"}, "failure": execution_failure}),
    ]}
    oracle = {"oneOf": [
        obj(["kind", "result"], {"kind": {"const": "baseline-gate"}, "result": typed_key("baseline-oracle-gate-result")}),
        obj(["kind", "result"], {"kind": {"const": "comparison"}, "result": typed_key("oracle-comparison-result")}),
        obj(["kind", "classification", "failure"], {"kind": {"const": "bounded-unknown"}, "classification": {"enum": ["time-limit", "depth-limit", "branch-limit", "result-limit", "resource-limit", "solver-unknown", "evaluator-unavailable"]}, "failure": oracle_failure}),
        obj(["kind", "failure"], {"kind": {"const": "diagnostic-only"}, "failure": oracle_failure}),
    ]}
    return {"execution": execution, "oracle": oracle}


def cache_record_schema() -> dict[str, Any]:
    terminals = terminal_record_schema()
    completion = obj(
        ["producerStatus", "evidenceClass", "materialClosure", "executionConformance"],
        {
            "producerStatus": {"const": "complete"},
            "evidenceClass": {"enum": ["semantic-result", "exact-bounded-attempt", "diagnostic-only"]},
            "materialClosure": {"enum": ["repo-complete", "external-required"]},
            "executionConformance": {"enum": ["finite-vector-proven", "native-proven", "not-proven"]},
        },
    )
    finite_production_schema = obj(
        ["mode", "vectorId", "inputDigest", "outputKeys"],
        {"mode": {"const": "finite-vector"}, "vectorId": {"type": "string", "minLength": 1}, "inputDigest": DIGEST_REF, "outputKeys": array(ARTIFACT_REF, unique=True)},
    )
    receipt_production_schema = obj(
        ["mode", "receipt", "result"],
        {"mode": {"const": "operation-receipt"}, "receipt": typed_key("operation-receipt"), "result": typed_key("execution-attempt-result")},
    )
    common = {
        "schemaVersion": {"const": 1}, "recordId": DIGEST_REF, "keyDigest": DIGEST_REF,
        "producedArtifacts": array(ARTIFACT_REF, unique=True), "completion": completion,
        "reuseClass": {"enum": ["semantic-result", "exact-bounded-attempt", "not-reusable"]},
        "productionEvidence": finite_production_schema,
    }
    execution = obj(
        ["schemaVersion", "recordId", "kind", "keyDigest", "key", "terminalRecord", "producedArtifacts", "completion", "reuseClass", "productionEvidence"],
        {**common, "kind": {"const": "execution-attempt"}, "key": execution_key_schema(), "terminalRecord": terminals["execution"], "productionEvidence": {"oneOf": [finite_production_schema, receipt_production_schema]}},
    )
    oracle = obj(
        ["schemaVersion", "recordId", "kind", "keyDigest", "key", "terminalRecord", "producedArtifacts", "completion", "reuseClass", "productionEvidence"],
        {**common, "kind": {"const": "oracle-evaluation"}, "key": oracle_key_schema(), "terminalRecord": terminals["oracle"]},
    )
    return {"oneOf": [execution, oracle]}


def manifest_schema() -> dict[str, Any]:
    test = obj(
        ["testId", "program", "parser", "startSymbol", "options", "bounds", "testInvocationDigest", "attemptKind", "oracleDeclarations"],
        {
            "testId": {"type": "string", "minLength": 1}, "program": typed_key("program"), "parser": typed_key("parser"),
            "startSymbol": {"type": "string", "minLength": 1}, "options": typed_key("options"),
            "bounds": obj(["depth", "timeMs", "branches", "results"], {name: {"type": "integer", "minimum": 1} for name in ("depth", "timeMs", "branches", "results")}),
            "testInvocationDigest": DIGEST_REF, "attemptKind": attempt_kind_schema(),
            "oracleDeclarations": array(typed_key("oracle-declaration"), minimum=1),
        },
    )
    candidate = obj(
        ["candidateId", "patch", "mutantId", "mutantDefinition"],
        {
            "candidateId": DIGEST_REF,
            "patch": typed_key("patch"),
            "mutantId": DIGEST_REF,
            "mutantDefinition": typed_key("mutant-definition"),
        },
    )
    return obj(
        ["schemaVersion", "manifestId", "baselineDefinition", "candidate", "compatibilityProfile", "loweringProfile", "executionProfile", "solverProfile", "isolationPolicy", "tests"],
        {
            "schemaVersion": {"const": 1}, "manifestId": DIGEST_REF, "baselineDefinition": typed_key("definition"),
            "candidate": candidate,
            "compatibilityProfile": typed_key("compatibility-profile"), "loweringProfile": typed_key("lowering-profile"),
            "executionProfile": typed_key("execution-profile"), "solverProfile": typed_key("solver-profile"),
            "isolationPolicy": isolation_schema(), "tests": array(test, minimum=1),
        },
    )


def campaign_invocation_schema() -> dict[str, Any]:
    slot = obj(
        ["slotId", "testId", "phase", "recordKind", "keyDigest"],
        {"slotId": {"type": "string", "minLength": 1}, "testId": {"type": "string", "minLength": 1}, "phase": {"enum": ["baseline", "mutant"]}, "recordKind": {"enum": ["execution-attempt", "oracle-evaluation"]}, "keyDigest": DIGEST_REF},
    )
    return obj(
        ["schemaVersion", "campaignInvocationId", "manifest", "operator", "scheduleMode", "requestedPlan"],
        {"schemaVersion": {"const": 1}, "campaignInvocationId": DIGEST_REF, "manifest": typed_key("cache-campaign-manifest"), "operator": typed_key("mutation-operator"), "scheduleMode": {"enum": ["first-kill", "full"]}, "requestedPlan": array(slot, minimum=1)},
    )


def report_schema() -> dict[str, Any]:
    status = obj(["slotId", "status"], {"slotId": {"type": "string", "minLength": 1}, "status": {"enum": ["executed", "accepted", "agree", "kill", "timeout", "unknown", "error", "skipped"]}})
    selected = obj(["slotId", "recordId"], {"slotId": {"type": "string", "minLength": 1}, "recordId": DIGEST_REF})
    score = obj(["killed", "survived", "denominator", "ratio"], {"killed": {"type": "integer", "minimum": 0}, "survived": {"type": "integer", "minimum": 0}, "denominator": {"type": "integer", "minimum": 0}, "ratio": {"oneOf": [obj(["numerator", "denominator"], {"numerator": {"type": "integer", "minimum": 0}, "denominator": {"type": "integer", "minimum": 1}}), {"type": "null"}]}})
    return obj(
        ["schemaVersion", "reportId", "campaignInvocation", "scheduleMode", "selectedRecords", "testStatuses", "scheduledButUnexecuted", "exclusions", "score", "campaignStatus"],
        {
            "schemaVersion": {"const": 1}, "reportId": DIGEST_REF, "campaignInvocation": typed_key("cache-campaign-invocation"),
            "scheduleMode": {"enum": ["first-kill", "full"]}, "selectedRecords": array(selected),
            "testStatuses": array(status, minimum=1), "scheduledButUnexecuted": array({"type": "string", "minLength": 1}, unique=True),
            "exclusions": obj(["timeout", "unknown", "error"], {name: {"type": "integer", "minimum": 0} for name in ("timeout", "unknown", "error")}),
            "score": score, "campaignStatus": {"const": "complete"},
        },
    )


def cache_schema() -> dict[str, Any]:
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/cache-semantics.schema.json",
        "title": "Portable per-attempt cache identities, records, and schedule reports v1",
        "oneOf": [{"$ref": f"#/$defs/{name}"} for name in ("executionAttemptKey", "oracleEvaluationKey", "cacheRecord", "campaignManifest", "campaignInvocation", "mutationReport")],
        "$defs": {
            "isolationPolicy": isolation_schema(), "executionAttemptKey": execution_key_schema(),
            "oracleEvaluationKey": oracle_key_schema(), "cacheRecord": cache_record_schema(),
            "campaignManifest": manifest_schema(), "campaignInvocation": campaign_invocation_schema(),
            "mutationReport": report_schema(),
        },
    }


def policy_schema() -> dict[str, Any]:
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": "https://starstream.dev/k-in-k/backend-agnostic/v1/mutation-execution-policy.schema.json",
        "title": "Portable mutation isolation policy v1",
        **obj(["schemaVersion", "policyId", "isolationPolicy"], {"schemaVersion": {"const": 1}, "policyId": DIGEST_REF, "isolationPolicy": isolation_schema()}),
    }


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def raw_sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identify(value: dict[str, Any], field: str, domain: str) -> dict[str, Any]:
    value[field] = digest(domain, without(value, field))
    return value


def role_specs() -> dict[str, dict[str, Any]]:
    values = {
        "cache-campaign-manifest": ("#/$defs/campaignManifest", "k-in-k/cache-campaign-manifest/v1", "manifestId"),
        "cache-campaign-invocation": ("#/$defs/campaignInvocation", "k-in-k/campaign-invocation/v1", "campaignInvocationId"),
        "cache-record": ("#/$defs/cacheRecord", "k-in-k/cache-record/v1", "recordId"),
        "cache-mutation-report": ("#/$defs/mutationReport", "k-in-k/mutation-report/v1", "reportId"),
    }
    return {
        role: {
            "role": role,
            "contentModel": "canonical-json",
            "mediaType": "application/json",
            "schema": f"cache-semantics.schema.json{fragment}",
            "digestDomain": domain,
            "projection": {"kind": "without-field"},
            "selfIdField": field,
        }
        for role, (fragment, domain, field) in values.items()
    }


def install_schemas_and_roles(root: Path) -> None:
    schemas = root / "schemas"
    write_json(schemas / "cache-semantics.schema.json", cache_schema())
    write_json(schemas / "mutation-execution-policy.schema.json", policy_schema())
    common_path = schemas / "common.schema.json"
    common = read_json(common_path)
    common["$defs"]["artifactRole"]["enum"] = sorted(set(common["$defs"]["artifactRole"]["enum"]) | NEW_ROLES)
    write_json(common_path, common)
    specs_path = root / "artifact-role-specs.json"
    specs = read_json(specs_path)
    by_role = {item["role"]: item for item in specs["specs"]}
    by_role.update(role_specs())
    specs["specs"] = [by_role[role] for role in sorted(by_role)]
    write_json(specs_path, specs)


def refreshed_definition(value: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(value)
    modules = []
    for module in result["modules"]:
        contents = []
        for sentence in module["sentences"]:
            body = sentence["value"]
            provenance = sentence["provenance"]
            provenance["bodyFingerprint"] = digest(
                "k-in-k/sentence-body/v1",
                {"body": body["body"], "requires": body["requires"], "ensures": body["ensures"]},
            )
            provenance["contentFingerprint"] = digest(
                "k-in-k/sentence-content/v1",
                {
                    "lineageId": provenance["lineageId"],
                    "module": body["module"],
                    "label": body["label"],
                    "kind": body["kind"],
                    "source": body["source"],
                    "location": body["location"],
                    "generated": provenance["generated"],
                    "bodyFingerprint": provenance["bodyFingerprint"],
                    "attributes": body["attributes"],
                    "transformationChain": provenance["transformationChain"],
                },
            )
            contents.append(provenance["contentFingerprint"])
        module_payload = {
            "name": module["name"], "ordinal": module["ordinal"],
            "imports": module["imports"], "sentenceContentFingerprints": contents,
        }
        module["fingerprint"] = digest("k-in-k/module/v1", module_payload)
        modules.append(module_payload)
    result["definitionDigest"] = digest(
        "k-in-k/definition/v1",
        {
            "schemaVersion": result["schemaVersion"], "representation": result["representation"],
            "baselineFamilyId": result["baselineFamilyId"], "modules": modules,
        },
    )
    return result


def cache_baseline_definition(root: Path) -> tuple[dict[str, Any], dict[str, str]]:
    result = deepcopy(read_json(root / "fixtures" / "semantic-definition-counter.json"))
    result["family"]["familyName"] = "bag14-portable-counter"
    result["family"]["compatibilityProfile"] = "bag14-portable-v1"
    result["baselineFamilyId"] = digest("k-in-k/baseline-family/v1", result["family"])
    replacements: dict[str, str] = {}
    for module in result["modules"]:
        for sentence in module["sentences"]:
            provenance = sentence["provenance"]
            old = provenance["lineageId"]
            provenance["lineageId"] = digest(
                "k-in-k/input-lineage/v1",
                {
                    "baselineFamilyId": result["baselineFamilyId"], "module": module["name"],
                    "source": sentence["value"]["source"], "location": sentence["value"]["location"],
                    "kind": sentence["value"]["kind"], "sourceOccurrenceOrdinal": sentence["sourceOccurrenceOrdinal"],
                },
            )
            replacements[old] = provenance["lineageId"]
    return refreshed_definition(result), replacements


def cache_patch_and_mutant(root: Path, baseline: dict[str, Any], lineage_replacements: dict[str, str], operator: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    vectors = read_json(root / "vectors" / "patch-application-vectors.json")
    case = next(item for item in vectors["cases"] if item["id"] == "add-attribute")
    pool = vectors["valuePool"]
    edits = []
    for template in case["edits"]:
        edit = deepcopy(template)
        edit["value"] = deepcopy(pool[edit.pop("valueRef")])
        edit["targetLineage"] = lineage_replacements[edit["targetLineage"]]
        target = next(sentence for module in baseline["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == edit["targetLineage"])
        edit["expectedContent"] = target["provenance"]["contentFingerprint"]
        edit["editId"] = digest("k-in-k/edit/v1", edit)
        edits.append(edit)
    edits.sort(key=lambda item: (item["targetLineage"] or "", canonical(item["targetPath"]), item["operation"], item["editId"]))
    patch = {
        "schemaVersion": 1,
        "patchId": digest("k-in-k/patch/v1", {"schemaVersion": 1, "edits": edits}),
        "operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "edits": edits,
    }
    mutant = deepcopy(baseline)
    by_lineage = {
        sentence["provenance"]["lineageId"]: sentence
        for module in mutant["modules"] for sentence in module["sentences"]
    }
    for edit in edits:
        if edit["operation"] != "add-attribute":
            raise AssertionError("BAG-14 finite patch vector changed operation")
        attributes = by_lineage[edit["targetLineage"]]["value"]["attributes"]
        attributes.append({"name": edit["value"]["name"], "value": edit["value"]["value"]})
        attributes.sort(key=lambda item: item["name"])
    mutant = refreshed_definition(mutant)
    return patch, mutant


def structured_entry(root: Path, role: str, identity: str, value: Any, name: str) -> dict[str, Any]:
    data = canonical(value).encode("utf-8")
    (root / "material" / name).write_bytes(data)
    return {
        "role": role, "digest": identity, "contentModel": "canonical-json", "mediaType": "application/json",
        "contentSha256": raw_sha256(data), "availability": "bundled",
        "logicalPath": f"repo://investigations/backend-agnostic-goal-closure/material/{name}", "resolverId": "repo-v1",
    }


def test_invocation_digest(test: dict[str, Any], manifest: dict[str, Any]) -> str:
    return digest(
        "k-in-k/cache-test-invocation/v1",
        {
            **without(test, "testInvocationDigest", "oracleDeclarations"),
            "compatibilityProfile": manifest["compatibilityProfile"],
            "loweringProfile": manifest["loweringProfile"],
            "executionProfile": manifest["executionProfile"],
            "solverProfile": manifest["solverProfile"],
            "isolationPolicy": manifest["isolationPolicy"],
        },
    )


def execution_key(manifest: dict[str, Any], test: dict[str, Any], subject: dict[str, Any], *, operation_version: int = 1) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "keyDigest": "0" * 64,
        "operation": {"operationId": "portable-finite-execution", "operationVersion": operation_version, "adapterId": "bag14-vector-adapter", "adapterVersion": 1},
        "subject": subject, "testInvocationDigest": test["testInvocationDigest"],
        "compatibilityProfileDigest": manifest["compatibilityProfile"]["digest"],
        "loweringProfileDigest": manifest["loweringProfile"]["digest"],
        "executionProfileDigest": manifest["executionProfile"]["digest"],
        "solverProfileDigest": manifest["solverProfile"]["digest"],
        "isolationPolicy": deepcopy(manifest["isolationPolicy"]), "attemptKind": deepcopy(test["attemptKind"]),
    }
    value["keyDigest"] = digest(DOMAINS["execution-attempt"], without(value, "keyDigest"))
    return value


def oracle_key(declaration: dict[str, Any], inputs: list[dict[str, Any]], evaluation_kind: str) -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "keyDigest": "0" * 64,
        "operation": {"operationId": "portable-oracle-evaluation", "operationVersion": 1, "adapterId": "bag14-vector-adapter", "adapterVersion": 1},
        "evaluationKind": evaluation_kind,
        "declaration": key("oracle-declaration", declaration["declarationId"]),
        "semanticInputs": deepcopy(inputs),
        "evaluator": {"evaluatorId": "bag12-portable-exit-stop", "evaluatorVersion": 1, "mode": "built-in"},
    }
    value["keyDigest"] = digest(DOMAINS["oracle-evaluation"], without(value, "keyDigest"))
    return value


def finite_input_digest(vector_id: str, inputs: dict[str, Any]) -> str:
    return digest("k-in-k/cache-finite-vector-input/v1", {"vectorId": vector_id, "inputs": inputs})


def finite_production(vector_id: str, cache_key: dict[str, Any], terminal: dict[str, Any], outputs: list[dict[str, str]]) -> dict[str, Any]:
    del terminal
    inputs = {"keyDigest": cache_key["keyDigest"]}
    return {"mode": "finite-vector", "vectorId": vector_id, "inputDigest": finite_input_digest(vector_id, inputs), "outputKeys": deepcopy(outputs)}


def finite_cache_row(record: dict[str, Any]) -> dict[str, Any]:
    inputs = {"keyDigest": record["keyDigest"]}
    return {
        "inputs": inputs,
        "inputDigest": finite_input_digest(record["productionEvidence"]["vectorId"], inputs),
        "terminalRecord": deepcopy(record["terminalRecord"]),
        "outputKeys": deepcopy(record["producedArtifacts"]),
    }


def finite_operand_row(
    declaration: dict[str, Any],
    subject: dict[str, Any],
    terminal_key: dict[str, str],
    trace_key: dict[str, str],
    operand: dict[str, Any],
) -> dict[str, Any]:
    vector_id = "bag14.oracle-operand-production.v1"
    inputs = {
        "declaration": key("oracle-declaration", declaration["declarationId"]),
        "subject": deepcopy(subject),
        "terminal": deepcopy(terminal_key),
        "producerTrace": deepcopy(trace_key),
    }
    return {
        "inputs": inputs,
        "inputDigest": finite_input_digest(vector_id, inputs),
        "outputKeys": [key("oracle-operand", operand["operandId"])],
    }


def cache_record(kind: str, cache_key: dict[str, Any], terminal: dict[str, Any], outputs: list[dict[str, str]], vector_id: str, evidence_class: str, reuse_class: str, *, conformance: str = "finite-vector-proven") -> dict[str, Any]:
    value = {
        "schemaVersion": 1, "recordId": "0" * 64, "kind": kind, "keyDigest": cache_key["keyDigest"],
        "key": deepcopy(cache_key), "terminalRecord": deepcopy(terminal), "producedArtifacts": deepcopy(outputs),
        "completion": {"producerStatus": "complete", "evidenceClass": evidence_class, "materialClosure": "repo-complete", "executionConformance": conformance},
        "reuseClass": reuse_class,
        "productionEvidence": finite_production(vector_id, cache_key, terminal, outputs),
    }
    value["recordId"] = digest("k-in-k/cache-record/v1", without(value, "recordId"))
    return value


def cache_terminal(definition_digest: str, text_value: str) -> dict[str, Any]:
    return identify(
        {
            "schemaVersion": 1, "terminalStateDigest": "0" * 64,
            "value": {"encoding": "portable-term-v1", "sort": "GeneratedTopCell", "node": {"kind": "token", "text": text_value}},
            "definitionDigest": definition_digest,
        },
        "terminalStateDigest", "k-in-k/terminal-state/v1",
    )


def cache_trace(test_id: str, path_key: str, definition_digest: str, terminal_key: dict[str, str], terminal_kind: str) -> dict[str, Any]:
    stop_reason = "stuck" if terminal_kind == "stuck" else "terminal"
    value = {
        "schemaVersion": 1, "testId": test_id, "pathOrdinal": 0, "pathKey": path_key,
        "complete": True, "stopReason": stop_reason,
        "pathPredicate": {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "token", "text": "true"}},
        "events": [], "pathIdentityDigest": "0" * 64,
        "executionTerminal": {"kind": terminal_kind, "artifact": terminal_key},
        "definitionDigest": definition_digest,
    }
    value["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", without(value, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    return value


def cache_crash(execution_profile_digest: str, terminal_key: dict[str, str]) -> dict[str, Any]:
    return identify(
        {
            "schemaVersion": 1,
            "crashDigest": "0" * 64,
            "executionProfileDigest": execution_profile_digest,
            "terminalState": deepcopy(terminal_key),
            "classification": "declared-object-language-crash",
        },
        "crashDigest",
        "k-in-k/semantic-crash/v1",
    )


def cache_declaration(
    test: dict[str, Any],
    manifest: dict[str, Any],
    slot_ordinal: int,
    slot_id: str,
    *,
    execution_pattern: bool = False,
    allow_crash: bool = False,
) -> dict[str, Any]:
    if execution_pattern:
        attempt = test["attemptKind"]
        kind = "execution-pattern"
        baseline_policy = "normal-or-crash"
        baseline_gate = {"mode": "reference-only"}
        projection = "pattern-outcome-bindings-v1"
        comparator = "exact-pattern-outcome-bindings-v1"
        kind_config = {
            "kind": kind,
            "patternSource": deepcopy(attempt["patternSource"]),
            "patternPlan": deepcopy(attempt["patternPlan"]),
            "patternQuery": deepcopy(attempt["patternQuery"]),
            "searchPolicy": attempt["searchPolicy"],
        }
    else:
        kind = "exit-stop"
        baseline_policy = "normal-or-crash" if allow_crash else "normal-only"
        baseline_gate = {"mode": "reference-only"} if allow_crash else {"mode": "assert", "expectedSide": {"kind": "exit-stop", "normalizedValue": {"terminalClass": "normal", "exitCode": None}}}
        projection = "terminal-class-and-declared-exit-v1"
        comparator = "exact-terminal-class-and-exit-v1"
        kind_config = {"kind": kind, "exitCodeMode": "none"}
    return identify(
        {
            "schemaVersion": 1, "declarationId": "0" * 64, "testInvocationDigest": test["testInvocationDigest"],
            "slotOrdinal": slot_ordinal, "slotId": slot_id, "oracleId": slot_id, "oracleVersion": 1, "kind": kind,
            "compatibilityProfileDigest": manifest["compatibilityProfile"]["digest"],
            "executionProfileDigest": manifest["executionProfile"]["digest"],
            "solverProfileDigest": manifest["solverProfile"]["digest"],
            "boundsDigest": digest("k-in-k/bounds/v1", test["bounds"]),
            "baselineTerminalPolicy": baseline_policy, "crashPolicy": "semantic-crash-distinguishes",
            "baselineGate": baseline_gate,
            "projectionSpec": {"mode": "portable-built-in", "projectionId": projection},
            "comparisonSpec": {"mode": "portable-built-in", "comparatorId": comparator},
            "kindConfig": kind_config,
        },
        "declarationId", "k-in-k/oracle-declaration/v1",
    )


def cache_operand(declaration: dict[str, Any], subject: dict[str, Any], terminal_key: dict[str, str], trace_key: dict[str, str], terminal_kind: str) -> dict[str, Any]:
    return identify(
        {
            "schemaVersion": 1, "operandId": "0" * 64,
            "declaration": key("oracle-declaration", declaration["declarationId"]), "subject": subject,
            "testInvocationDigest": declaration["testInvocationDigest"],
            "compatibilityProfileDigest": declaration["compatibilityProfileDigest"],
            "executionProfileDigest": declaration["executionProfileDigest"],
            "solverProfileDigest": declaration["solverProfileDigest"],
            "completionEvidence": {"kind": "execution-terminal", "terminal": {"kind": terminal_kind, "artifact": terminal_key}, "producerTrace": trace_key},
            "normalizedValue": {"terminalClass": terminal_kind, "exitCode": None},
        },
        "operandId", "k-in-k/oracle-operand/v1",
    )


def normalized_value_digest(declaration: dict[str, Any], operand: dict[str, Any]) -> str:
    return digest(
        "k-in-k/oracle-normalized-value/v1",
        {"kind": declaration["kind"], "projectionId": declaration["projectionSpec"]["projectionId"], "normalizedValue": operand["normalizedValue"]},
    )


def semantic_side(side_name: str, value_key: dict[str, str]) -> dict[str, Any]:
    return {
        "side": side_name,
        "normalOperand": deepcopy(value_key) if value_key["role"] == "oracle-operand" else None,
        "semanticCrash": deepcopy(value_key) if value_key["role"] == "semantic-crash" else None,
    }


def cache_gate(declaration: dict[str, Any], baseline_value: dict[str, Any], baseline_key: dict[str, str]) -> dict[str, Any]:
    if declaration["baselineGate"]["mode"] == "reference-only":
        assertion = None
        status = "accepted"
    else:
        assertion = "agree" if baseline_key["role"] == "oracle-operand" and baseline_value["normalizedValue"] == declaration["baselineGate"]["expectedSide"]["normalizedValue"] else "distinguish"
        status = "accepted" if assertion == "agree" else "rejected"
    return identify(
        {
            "schemaVersion": 1, "gateResultId": "0" * 64,
            "declaration": key("oracle-declaration", declaration["declarationId"]),
            "actualSide": semantic_side("baseline", baseline_key),
            "assertionOutcome": assertion, "status": status, "failure": None,
        },
        "gateResultId", "k-in-k/baseline-oracle-gate-result/v1",
    )


def crash_semantic_value(crash: dict[str, Any], terminal: dict[str, Any]) -> tuple[Any, ...]:
    return crash["executionProfileDigest"], crash["classification"], terminal["value"]


def cache_comparison(
    declaration: dict[str, Any],
    baseline_value: dict[str, Any],
    baseline_key: dict[str, str],
    mutant_value: dict[str, Any],
    mutant_key: dict[str, str],
    *,
    crash_terminals: tuple[dict[str, Any], dict[str, Any]] | None = None,
) -> dict[str, Any]:
    left = semantic_side("baseline", baseline_key)
    right = semantic_side("mutant", mutant_key)
    digests: list[str | None]
    if baseline_key["role"] == mutant_key["role"] == "oracle-operand":
        outcome = "agree" if baseline_value["normalizedValue"] == mutant_value["normalizedValue"] else "distinguish"
        digests = [normalized_value_digest(declaration, baseline_value), normalized_value_digest(declaration, mutant_value)]
    else:
        if baseline_key["role"] == mutant_key["role"] == "semantic-crash" and crash_terminals is not None and crash_semantic_value(baseline_value, crash_terminals[0]) == crash_semantic_value(mutant_value, crash_terminals[1]):
            outcome = "agree"
        else:
            outcome = "distinguish" if declaration["crashPolicy"] == "semantic-crash-distinguishes" else "incomparable"
        digests = [None if baseline_key["role"] == "semantic-crash" else normalized_value_digest(declaration, baseline_value), None if mutant_key["role"] == "semantic-crash" else normalized_value_digest(declaration, mutant_value)]
    return identify(
        {
            "schemaVersion": 1, "comparisonId": "0" * 64,
            "declaration": key("oracle-declaration", declaration["declarationId"]), "sides": [left, right],
            "projectionId": declaration["projectionSpec"]["projectionId"], "comparatorId": declaration["comparisonSpec"]["comparatorId"],
            "normalizedValueDigests": digests,
            "outcome": outcome,
        },
        "comparisonId", "k-in-k/oracle-comparison-result/v1",
    )


def write_fixture_and_entry(root: Path, role: str, identity: str, value: dict[str, Any], name: str) -> dict[str, Any]:
    write_json(root / "fixtures" / name, value)
    return structured_entry(root, role, identity, value, name)


def finalize_refresh(root: Path) -> None:
    """Publish the backend-free BAG-14 finite cache evidence."""
    install_schemas_and_roles(root)
    fixtures = root / "fixtures"
    obsolete_names = [
        *[f"bag14-oracle-declaration-t{index}.json" for index in (1, 2)],
        *[f"bag14-oracle-operand-{side}-t{index}.json" for side in ("baseline", "mutant") for index in (1, 2)],
        *[f"bag14-baseline-gate-t{index}.json" for index in (1, 2)],
        *[f"bag14-oracle-comparison-t{index}.json" for index in (1, 2)],
        *[f"bag14-cache-record-baseline-gate-t{index}.json" for index in (1, 2)],
        *[f"bag14-cache-record-mutant-comparison-t{index}.json" for index in (1, 2)],
    ]
    for directory in (fixtures, root / "material"):
        for name in obsolete_names:
            (directory / name).unlink(missing_ok=True)
    active_catalog = read_json(fixtures / "artifact-catalog.json")
    active_entries = {(item["role"], item["digest"]): deepcopy(item) for item in active_catalog["entries"]}
    baseline, lineage_replacements = cache_baseline_definition(root)
    counter_registry = read_json(fixtures / "counter-mutation-site-registry.json")
    selector = deepcopy(counter_registry["selector"])
    selector["clauses"][0].update({
        "role": "bag14-branch-result",
        "label": "branch",
        "termPath": [{"kind": "field", "name": "body"}, {"kind": "field", "name": "rhs"}],
        "termSort": "Control",
        "termHeadLabel": "selected",
        "bindingName": "RESULT",
    })
    selector["selectorDigest"] = digest("k-in-k/mutation-selector/v1", selector["clauses"])
    operator = deepcopy(read_json(fixtures / "counter-mutation-operator.json"))
    operator["operatorId"] = "bag14-counter-branch-site"
    operator["selectorDigest"] = selector["selectorDigest"]
    operator["patchTemplateRoles"] = [{"name": "bag14-heating-attribute", "operation": "add-attribute", "sourceSelectorRoles": ["bag14-branch-result"]}]
    template_bytes = b"BAG-14 finite patch template: add heating attribute to the selected counter sentence.\n"
    template_content_hash = raw_sha256(template_bytes)
    operator["patchTemplateDigest"] = digest("k-in-k/opaque-artifact/v1", {"role": "patch-template", "mediaType": "application/octet-stream", "contentSha256": template_content_hash})
    (root / "material" / "bag14-patch-template.bin").write_bytes(template_bytes)
    template_entry = {
        "role": "patch-template", "digest": operator["patchTemplateDigest"], "contentModel": "opaque-bytes", "mediaType": "application/octet-stream",
        "contentSha256": template_content_hash, "availability": "bundled",
        "logicalPath": "repo://investigations/backend-agnostic-goal-closure/material/bag14-patch-template.bin", "resolverId": "repo-v1",
    }
    operator["rationale"] = "Finite BAG-14 cache conformance derivative; no native execution authority."
    operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", without(operator, "operatorDigest"))
    patch, mutant_definition = cache_patch_and_mutant(root, baseline, lineage_replacements, operator)
    compatibility_digest = digest("k-in-k/compatibility-profile/v1", {"profile": baseline["family"]["compatibilityProfile"]})
    compatibility = {"profile": deepcopy(baseline["family"]["compatibilityProfile"])}

    corpus = read_json(fixtures / "corpus-manifest.json")
    tests = []
    manifest: dict[str, Any] = {
        "schemaVersion": 1, "manifestId": "0" * 64,
        "baselineDefinition": key("definition", baseline["definitionDigest"]),
        "candidate": {"candidateId": "0" * 64, "patch": key("patch", patch["patchId"]), "mutantId": "0" * 64, "mutantDefinition": key("mutant-definition", mutant_definition["definitionDigest"])},
        "compatibilityProfile": key("compatibility-profile", compatibility_digest),
        "loweringProfile": key("lowering-profile", corpus.get("loweringProfileDigest", read_json(fixtures / "mutation-manifest.json")["loweringProfileDigest"])),
        "executionProfile": key("execution-profile", corpus["executionProfileDigest"]),
        "solverProfile": key("solver-profile", corpus["solverProfileDigest"]),
        "isolationPolicy": {"schemaVersion": 1, "isolationPolicyDigest": "0" * 64, "baselineState": "immutable", "mutantState": "fresh-per-mutant", "sharedWritableState": False, "observerState": "fresh-per-test-path"},
        "tests": tests,
    }
    manifest["isolationPolicy"]["isolationPolicyDigest"] = digest("k-in-k/isolation-policy/v1", without(manifest["isolationPolicy"], "isolationPolicyDigest"))
    manifest["candidate"]["candidateId"] = digest("k-in-k/candidate/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": baseline["definitionDigest"], "patchId": patch["patchId"]})
    manifest["candidate"]["mutantId"] = digest("k-in-k/mutant/v1", {"baselineDefinitionDigest": baseline["definitionDigest"], "patchId": patch["patchId"]})
    for index, (source, test_id) in enumerate(zip(corpus["tests"], ("cache-prefix", "cache-suffix")), start=1):
        test = {
            "testId": test_id, "program": key("program", source["programDigest"]), "parser": key("parser", source["parserDigest"]),
            "startSymbol": source["startSymbol"], "options": key("options", source["optionsDigest"]), "bounds": deepcopy(corpus["bounds"]),
            "testInvocationDigest": "0" * 64, "attemptKind": {"kind": "ordinary"},
            "oracleDeclarations": [],
        }
        test["testInvocationDigest"] = test_invocation_digest(test, manifest)
        tests.append(test)
    declarations_by_test = [
        [
            cache_declaration(tests[0], manifest, 0, "cache-prefix-exit-stop-primary"),
            cache_declaration(tests[0], manifest, 1, "cache-prefix-exit-stop-secondary"),
        ],
        [cache_declaration(tests[1], manifest, 0, "cache-suffix-exit-stop", allow_crash=True)],
    ]
    declarations = [declaration for selected in declarations_by_test for declaration in selected]
    for test, selected in zip(tests, declarations_by_test):
        test["oracleDeclarations"] = [key("oracle-declaration", declaration["declarationId"]) for declaration in selected]
    manifest["manifestId"] = digest("k-in-k/cache-campaign-manifest/v1", without(manifest, "manifestId"))

    baseline_terminal = cache_terminal(baseline["definitionDigest"], "bag14-done")
    mutant_normal_terminal = cache_terminal(mutant_definition["definitionDigest"], "bag14-done")
    mutant_stuck_terminal = cache_terminal(mutant_definition["definitionDigest"], "bag14-stuck")
    baseline_subject = {"kind": "baseline", "definition": manifest["baselineDefinition"]}
    mutant_subject = {
        "kind": "mutant", "baselineDefinition": manifest["baselineDefinition"],
        "candidateId": manifest["candidate"]["candidateId"], "operator": key("mutation-operator", operator["operatorDigest"]),
        "patch": manifest["candidate"]["patch"], "mutantId": manifest["candidate"]["mutantId"], "mutantDefinition": manifest["candidate"]["mutantDefinition"],
    }
    assets: list[tuple[str, str, dict[str, Any], str]] = [
        ("definition", baseline["definitionDigest"], baseline, "bag14-definition-baseline.json"),
        ("mutant-definition", mutant_definition["definitionDigest"], mutant_definition, "bag14-definition-mutant.json"),
        ("mutation-operator", operator["operatorDigest"], operator, "bag14-mutation-operator.json"),
        ("mutation-selector", selector["selectorDigest"], selector, "bag14-mutation-selector.json"),
        ("patch", patch["patchId"], patch, "bag14-patch.json"),
        ("compatibility-profile", compatibility_digest, compatibility, "bag14-compatibility-profile.json"),
        ("cache-campaign-manifest", manifest["manifestId"], manifest, "bag14-cache-campaign-manifest.json"),
        ("terminal-state", baseline_terminal["terminalStateDigest"], baseline_terminal, "bag14-terminal-baseline.json"),
        ("terminal-state", mutant_normal_terminal["terminalStateDigest"], mutant_normal_terminal, "bag14-terminal-mutant-normal.json"),
        ("terminal-state", mutant_stuck_terminal["terminalStateDigest"], mutant_stuck_terminal, "bag14-terminal-mutant-stuck.json"),
    ]
    for test_index, selected in enumerate(declarations_by_test, start=1):
        for slot_ordinal, declaration in enumerate(selected):
            assets.append(("oracle-declaration", declaration["declarationId"], declaration, f"bag14-oracle-declaration-t{test_index}-o{slot_ordinal}.json"))

    records: dict[str, dict[str, Any]] = {}
    operand_rows: list[dict[str, Any]] = []
    plan_rows: list[tuple[str, str, str, str]] = []
    for index, (test, selected_declarations) in enumerate(zip(tests, declarations_by_test), start=1):
        mutant_terminal = mutant_stuck_terminal if index == 1 else mutant_normal_terminal
        mutant_terminal_kind = "stuck" if index == 1 else "normal"
        baseline_terminal_kind = "normal"
        baseline_terminal_key = key("terminal-state", baseline_terminal["terminalStateDigest"])
        mutant_terminal_key = key("terminal-state", mutant_terminal["terminalStateDigest"])
        baseline_value_key = baseline_terminal_key
        mutant_value_key = mutant_terminal_key
        trace_values = [
            ("baseline", cache_trace(test["testId"], f"root/baseline/{index}", baseline["definitionDigest"], baseline_value_key, baseline_terminal_kind)),
            ("mutant", cache_trace(test["testId"], f"root/mutant/{index}", mutant_definition["definitionDigest"], mutant_value_key, mutant_terminal_kind)),
        ]
        trace_keys: dict[str, dict[str, str]] = {}
        for side_name, trace in trace_values:
            trace_id = digest("k-in-k/event-trace/v1", trace)
            trace_keys[side_name] = key("event-trace", trace_id)
            assets.append(("event-trace", trace_id, trace, f"bag14-event-trace-{side_name}-t{index}.json"))
        base_key = execution_key(manifest, test, baseline_subject)
        mutant_key = execution_key(manifest, test, mutant_subject)
        baseline_terminal_record = {"kind": "normal", "terminal": baseline_terminal_key}
        mutant_terminal_record = {"kind": mutant_terminal_kind, "terminal": mutant_terminal_key}
        baseline_outputs = [baseline_terminal_key, trace_keys["baseline"]]
        mutant_outputs = [mutant_terminal_key, trace_keys["mutant"]]
        execution_vector = "bag14.execution-terminal.v1"
        built = [
            (f"baseline-execution-t{index}", cache_record("execution-attempt", base_key, baseline_terminal_record, baseline_outputs, execution_vector, "semantic-result", "semantic-result"), "baseline", "execution-attempt"),
            (f"mutant-execution-t{index}", cache_record("execution-attempt", mutant_key, mutant_terminal_record, mutant_outputs, execution_vector, "semantic-result", "semantic-result"), "mutant", "execution-attempt"),
        ]

        for slot_ordinal, declaration in enumerate(selected_declarations):
            suffix = f"t{index}-o{slot_ordinal}"
            baseline_subject_value = {"side": "baseline", "definitionDigest": baseline["definitionDigest"]}
            mutant_subject_value = {"side": "mutant", "baselineDefinitionDigest": baseline["definitionDigest"], "mutantId": manifest["candidate"]["mutantId"], "mutantDefinitionDigest": mutant_definition["definitionDigest"]}
            baseline_operand = cache_operand(declaration, baseline_subject_value, baseline_terminal_key, trace_keys["baseline"], "normal")
            mutant_operand = cache_operand(declaration, mutant_subject_value, mutant_terminal_key, trace_keys["mutant"], mutant_terminal_kind)
            baseline_semantic_value = baseline_operand
            mutant_semantic_value = mutant_operand
            baseline_semantic_key = key("oracle-operand", baseline_operand["operandId"])
            mutant_semantic_key = key("oracle-operand", mutant_operand["operandId"])
            operand_rows.extend([
                finite_operand_row(declaration, baseline_subject_value, baseline_terminal_key, trace_keys["baseline"], baseline_operand),
                finite_operand_row(declaration, mutant_subject_value, mutant_terminal_key, trace_keys["mutant"], mutant_operand),
            ])
            assets.extend([
                ("oracle-operand", baseline_operand["operandId"], baseline_operand, f"bag14-oracle-operand-baseline-{suffix}.json"),
                ("oracle-operand", mutant_operand["operandId"], mutant_operand, f"bag14-oracle-operand-mutant-{suffix}.json"),
            ])
            gate = cache_gate(declaration, baseline_semantic_value, baseline_semantic_key)
            comparison = cache_comparison(
                declaration,
                baseline_semantic_value,
                baseline_semantic_key,
                mutant_semantic_value,
                mutant_semantic_key,
            )
            assets.extend([
                ("baseline-oracle-gate-result", gate["gateResultId"], gate, f"bag14-baseline-gate-{suffix}.json"),
                ("oracle-comparison-result", comparison["comparisonId"], comparison, f"bag14-oracle-comparison-{suffix}.json"),
            ])
            gate_key = oracle_key(declaration, [{"side": "baseline", "value": baseline_semantic_key}], "baseline-admission")
            comparison_key = oracle_key(declaration, [{"side": "baseline", "value": baseline_semantic_key}, {"side": "mutant", "value": mutant_semantic_key}], "baseline-mutant-comparison")
            built.extend([
                (f"baseline-gate-{suffix}", cache_record("oracle-evaluation", gate_key, {"kind": "baseline-gate", "result": key("baseline-oracle-gate-result", gate["gateResultId"])}, [key("baseline-oracle-gate-result", gate["gateResultId"])], "bag14.baseline-gate.v1", "semantic-result", "semantic-result"), "baseline", "oracle-evaluation"),
                (f"mutant-comparison-{suffix}", cache_record("oracle-evaluation", comparison_key, {"kind": "comparison", "result": key("oracle-comparison-result", comparison["comparisonId"])}, [key("oracle-comparison-result", comparison["comparisonId"])], "bag14.oracle-comparison.v1", "semantic-result", "semantic-result"), "mutant", "oracle-evaluation"),
            ])
        for slot_id, record, phase, record_kind in built:
            records[slot_id] = record
            plan_rows.append((slot_id, test["testId"], phase, record_kind))

    # All baseline admissions precede mutant scoring.  This order is the
    # portable reason a first-kill suffix cannot hide a missing baseline gate.
    plan_order = [
        "baseline-execution-t1", "baseline-gate-t1-o0", "baseline-gate-t1-o1",
        "baseline-execution-t2", "baseline-gate-t2-o0",
        "mutant-execution-t1", "mutant-comparison-t1-o0", "mutant-comparison-t1-o1",
        "mutant-execution-t2", "mutant-comparison-t2-o0",
    ]
    plan_by_id = {slot_id: (test_id, phase, kind_value) for slot_id, test_id, phase, kind_value in plan_rows}
    requested_plan = [
        {"slotId": slot_id, "testId": plan_by_id[slot_id][0], "phase": plan_by_id[slot_id][1], "recordKind": plan_by_id[slot_id][2], "keyDigest": records[slot_id]["keyDigest"]}
        for slot_id in plan_order
    ]
    invocations = {}
    reports = {}
    for schedule in ("first-kill", "full"):
        invocation = {
            "schemaVersion": 1, "campaignInvocationId": "0" * 64,
            "manifest": key("cache-campaign-manifest", manifest["manifestId"]), "operator": key("mutation-operator", operator["operatorDigest"]),
            "scheduleMode": schedule, "requestedPlan": deepcopy(requested_plan),
        }
        invocation["campaignInvocationId"] = digest("k-in-k/campaign-invocation/v1", without(invocation, "campaignInvocationId"))
        invocations[schedule] = invocation
        first_kill_length = plan_order.index("mutant-comparison-t1-o0") + 1
        selected_slots = plan_order[:first_kill_length] if schedule == "first-kill" else plan_order
        skipped = plan_order[first_kill_length:] if schedule == "first-kill" else []
        status_by_slot = {slot_id: "executed" for slot_id in plan_order}
        status_by_slot.update({
            "baseline-gate-t1-o0": "accepted", "baseline-gate-t1-o1": "accepted", "baseline-gate-t2-o0": "accepted",
            "mutant-comparison-t1-o0": "kill", "mutant-comparison-t1-o1": "kill", "mutant-comparison-t2-o0": "agree",
        })
        status_by_slot.update({slot_id: "skipped" for slot_id in skipped})
        report = {
            "schemaVersion": 1, "reportId": "0" * 64,
            "campaignInvocation": key("cache-campaign-invocation", invocation["campaignInvocationId"]), "scheduleMode": schedule,
            "selectedRecords": [{"slotId": slot_id, "recordId": records[slot_id]["recordId"]} for slot_id in selected_slots],
            "testStatuses": [{"slotId": slot_id, "status": status_by_slot[slot_id]} for slot_id in plan_order],
            "scheduledButUnexecuted": skipped, "exclusions": {"timeout": 0, "unknown": 0, "error": 0},
            "score": {"killed": 1, "survived": 0, "denominator": 1, "ratio": {"numerator": 1, "denominator": 1}},
            "campaignStatus": "complete",
        }
        report["reportId"] = digest("k-in-k/mutation-report/v1", without(report, "reportId"))
        reports[schedule] = report

    bounded_key = execution_key(manifest, tests[0], mutant_subject, operation_version=2)
    bounded_failure = {"stage": "execution", "classification": "time-limit", "context": "mutant-execution", "scope": "mutant", "retryability": "same-input-after-resource-change", "semanticEvidence": [], "details": {}}
    bounded_terminal = {"kind": "bounded-stop", "classification": "time-limit", "boundsDigest": digest("k-in-k/bounds/v1", tests[0]["bounds"]), "failure": bounded_failure}
    bounded = cache_record("execution-attempt", bounded_key, bounded_terminal, [], "bag14.exact-bounded-stop.v1", "exact-bounded-attempt", "exact-bounded-attempt")
    diagnostic_key = execution_key(manifest, tests[1], mutant_subject, operation_version=3)
    diagnostic_terminal = {"kind": "diagnostic-only", "failure": {"stage": "infrastructure", "classification": "worker-lost", "context": "mutant-execution", "scope": "mutant", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}}
    diagnostic = cache_record("execution-attempt", diagnostic_key, diagnostic_terminal, [], "bag14.diagnostic-failure.v1", "diagnostic-only", "not-reusable")
    records["bounded-attempt"] = bounded
    records["diagnostic-attempt"] = diagnostic

    # Closed-union regression: crashes are semantic inputs with their own
    # producer traces, not oracle operands and not reusable campaign records.
    crash_declaration = declarations_by_test[1][0]
    crash_test = tests[1]
    crash_values = []
    for side_name, definition_digest, terminal in (
        ("baseline", baseline["definitionDigest"], baseline_terminal),
        ("mutant", mutant_definition["definitionDigest"], mutant_normal_terminal),
    ):
        terminal_key = key("terminal-state", terminal["terminalStateDigest"])
        crash = cache_crash(manifest["executionProfile"]["digest"], terminal_key)
        crash_key = key("semantic-crash", crash["crashDigest"])
        trace = cache_trace(crash_test["testId"], f"root/crash/{side_name}", definition_digest, crash_key, "semantic-crash")
        trace_id = digest("k-in-k/event-trace/v1", trace)
        assets.extend([
            ("semantic-crash", crash["crashDigest"], crash, f"bag14-semantic-crash-{side_name}.json"),
            ("event-trace", trace_id, trace, f"bag14-event-trace-crash-{side_name}.json"),
        ])
        crash_values.append((crash, crash_key))
    crash_gate_key = oracle_key(crash_declaration, [{"side": "baseline", "value": crash_values[0][1]}], "baseline-admission")
    crash_comparison_key = oracle_key(
        crash_declaration,
        [{"side": "baseline", "value": crash_values[0][1]}, {"side": "mutant", "value": crash_values[1][1]}],
        "baseline-mutant-comparison",
    )
    crash_gate = cache_gate(crash_declaration, crash_values[0][0], crash_values[0][1])
    crash_comparison = cache_comparison(
        crash_declaration,
        crash_values[0][0],
        crash_values[0][1],
        crash_values[1][0],
        crash_values[1][1],
        crash_terminals=(baseline_terminal, mutant_normal_terminal),
    )
    assets.extend([
        ("baseline-oracle-gate-result", crash_gate["gateResultId"], crash_gate, "bag14-baseline-gate-crash.json"),
        ("oracle-comparison-result", crash_comparison["comparisonId"], crash_comparison, "bag14-oracle-comparison-crash.json"),
    ])
    crash_oracle_evidence = [
        {"key": crash_gate_key, "result": key("baseline-oracle-gate-result", crash_gate["gateResultId"])},
        {"key": crash_comparison_key, "result": key("oracle-comparison-result", crash_comparison["comparisonId"])},
    ]

    # BAG-11/BAG-12 cache-root regression selects an exact active manifest
    # test/declaration slot; it is not an invented derivative manifest slot.
    active_manifest = read_json(fixtures / "mutation-manifest.json")
    active_test = next(item for item in active_manifest["tests"] if item["invocationDigest"] == "043447ba5bd136575c0d4952ca2d36508d4856c1a28f4efb5001ab611d5367ca")
    selected_declaration_key = active_test["oracleDeclarations"][12]
    active_declaration = read_json(fixtures / "oracle-declaration-execution-pattern-pattern-outcome-distinguish.json")
    query_roots = deepcopy(active_test["patternQueries"][0])
    query_value = read_json(fixtures / "pattern-query-write-eventually-load.json")
    splice_query_value = read_json(fixtures / "pattern-query-single-write.json")
    observation_value = read_json(fixtures / "observation-manifest.json")
    observation_key = key("observation-manifest", observation_value["manifestId"])
    query_attempt = {
        "kind": "query-coupled",
        "observationInputs": [observation_key],
        **query_roots,
        "searchPolicy": active_declaration["kindConfig"]["searchPolicy"],
    }
    query_execution = {
        "schemaVersion": 1,
        "keyDigest": "0" * 64,
        "operation": {"operationId": "portable-finite-execution", "operationVersion": 1, "adapterId": "bag14-vector-adapter", "adapterVersion": 1},
        "subject": {"kind": "baseline", "definition": key("definition", active_manifest["definitionDigest"])},
        "testInvocationDigest": active_test["invocationDigest"],
        "compatibilityProfileDigest": active_declaration["compatibilityProfileDigest"],
        "loweringProfileDigest": active_manifest["loweringProfileDigest"],
        "executionProfileDigest": active_declaration["executionProfileDigest"],
        "solverProfileDigest": active_declaration["solverProfileDigest"],
        "isolationPolicy": deepcopy(manifest["isolationPolicy"]),
        "attemptKind": query_attempt,
    }
    query_execution["keyDigest"] = digest(DOMAINS["execution-attempt"], without(query_execution, "keyDigest"))
    query_regression = {
        "activeCatalogDigest": active_manifest["artifactCatalogDigest"],
        "activeManifestId": active_manifest["manifestId"],
        "testId": active_test["testId"],
        "slotOrdinal": 12,
        "selectedDeclaration": selected_declaration_key,
        "executionKey": query_execution,
    }

    for slot_id, record in records.items():
        assets.append(("cache-record", record["recordId"], record, f"bag14-cache-record-{slot_id}.json"))
    for schedule, invocation in invocations.items():
        assets.append(("cache-campaign-invocation", invocation["campaignInvocationId"], invocation, f"bag14-campaign-invocation-{schedule}.json"))
    for schedule, report in reports.items():
        assets.append(("cache-mutation-report", report["reportId"], report, f"bag14-mutation-report-{schedule}.json"))

    needed_existing = {
        ("program", test["program"]["digest"]) for test in tests
    } | {("parser", test["parser"]["digest"]) for test in tests} | {("options", test["options"]["digest"]) for test in tests} | {
        (manifest[name]["role"], manifest[name]["digest"])
        for name in ("loweringProfile", "executionProfile", "solverProfile")
    } | {
        (role, artifact_digest)
        for role, artifact_digest in (
            ("mutation-module", operator["moduleDigest"]), ("precondition", operator["preconditionDigest"]),
            ("postcondition", operator["postconditionDigest"]),
        )
    } | {
        (item["role"], item["digest"])
        for item in (
            observation_key,
            query_value["patternSource"],
            query_value["patternPlan"],
            key("pattern-query", query_value["queryId"]),
            splice_query_value["patternSource"],
            splice_query_value["patternPlan"],
            key("pattern-query", splice_query_value["queryId"]),
            selected_declaration_key,
        )
    }
    catalog_entries = {identity: active_entries[identity] for identity in needed_existing}
    catalog_entries[("patch-template", operator["patchTemplateDigest"])] = template_entry
    for role, identity, value, name in assets:
        catalog_entries[(role, identity)] = write_fixture_and_entry(root, role, identity, value, name)
    cache_catalog = {"schemaVersion": 1, "catalogId": "0" * 64, "entries": sorted(catalog_entries.values(), key=lambda item: (item["role"], item["digest"])), "unboundRequirements": []}
    cache_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", without(cache_catalog, "catalogId"))
    write_json(fixtures / "bag14-cache-artifact-catalog.json", cache_catalog)

    policy = {"schemaVersion": 1, "policyId": "0" * 64, "isolationPolicy": deepcopy(manifest["isolationPolicy"])}
    policy["policyId"] = digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId"))
    write_json(fixtures / "mutation-execution-policy.json", policy)

    output_roles = {
        "bag14.execution-terminal.v1": ["terminal-state", "event-trace"],
        "bag14.baseline-gate.v1": ["baseline-oracle-gate-result"],
        "bag14.oracle-comparison.v1": ["oracle-comparison-result"],
        "bag14.exact-bounded-stop.v1": [],
        "bag14.diagnostic-failure.v1": [],
    }
    registry = {
        vector_id: {
            "kind": "cache-record",
            "outputRoles": roles,
            "rows": [finite_cache_row(record) for record in records.values() if record["productionEvidence"]["vectorId"] == vector_id],
        }
        for vector_id, roles in output_roles.items()
    }
    registry["bag14.oracle-operand-production.v1"] = {
        "kind": "oracle-operand-production",
        "outputRoles": ["oracle-operand"],
        "rows": operand_rows,
    }
    vector = {
        "schemaVersion": 1,
        "artifactCatalogDigest": cache_catalog["catalogId"],
        "queryCoupledRegression": query_regression,
        "crashOracleEvidence": crash_oracle_evidence,
        "finiteVectorRegistry": registry,
        "scheduleFolds": [
            {
                "scheduleMode": schedule,
                "materializations": [
                    {
                        "cacheState": cache_state,
                        "recordSources": [
                            {
                                **mapping,
                                "source": "cache-hit" if cache_state == "full-hit" or (cache_state == "partial-hit" and index < max(1, len(reports[schedule]["selectedRecords"]) // 2)) else "executed",
                            }
                            for index, mapping in enumerate(reports[schedule]["selectedRecords"])
                        ],
                    }
                    for cache_state in ("uncached", "partial-hit", "full-hit")
                ],
            }
            for schedule in ("first-kill", "full")
        ],
        "sharedPrefixRecords": reports["first-kill"]["selectedRecords"],
        "fullSuffixRecords": reports["full"]["selectedRecords"][len(reports["first-kill"]["selectedRecords"]):],
        "adversaries": [{"probe": name, "expected": "reject"} for name in ADVERSARY_NAMES],
    }
    write_json(root / "vectors" / "cache-semantics-vectors.json", vector)


class CacheVerifier:
    def __init__(self, root: Path, api: dict[str, Any]):
        self.root = root
        self.fixtures = root / "fixtures"
        self.api = api
        self.ok: Callable[[bool, str], None] = api["ok"]
        self.catalog = read_json(self.fixtures / "bag14-cache-artifact-catalog.json")
        self.entries = {(item["role"], item["digest"]): item for item in self.catalog["entries"]}
        self.ok(len(self.entries) == len(self.catalog["entries"]), "BAG-14 cache catalog duplicates an artifact key")
        self.assets: dict[tuple[str, str], dict[str, Any]] = {}
        for identity, entry in self.entries.items():
            self.ok(entry["availability"] == "bundled" and entry["resolverId"] == "repo-v1" and entry["logicalPath"].startswith("repo://"), "BAG-14 positive graph is not wholly repo-resolvable")
            relative = entry["logicalPath"].removeprefix("repo://")
            path = self.root.parents[1] / relative
            self.ok(path.is_file(), "BAG-14 bundled cache material is missing")
            data = path.read_bytes()
            self.ok(raw_sha256(data) == entry["contentSha256"], "BAG-14 cache material byte hash drift")
            if entry["contentModel"] == "canonical-json":
                value = json.loads(data.decode("utf-8"), object_pairs_hook=self.unique_object)
                self.ok(data == canonical(value).encode("utf-8"), "BAG-14 structured material is not canonical JSON")
                self.assets[identity] = value
            else:
                expected_opaque = digest(
                    "k-in-k/opaque-artifact/v1",
                    {"role": entry["role"], "mediaType": entry["mediaType"], "contentSha256": entry["contentSha256"]},
                )
                self.ok(entry["digest"] == expected_opaque, "BAG-14 opaque artifact semantic identity drift")
        for (role, identity), value in self.assets.items():
            self.validate_catalog_identity(role, identity, value)
        self.ok(self.catalog["catalogId"] == digest("k-in-k/artifact-catalog/v1", without(self.catalog, "catalogId")), "BAG-14 cache catalog identity drift")
        self.manifest = self.only("cache-campaign-manifest")
        self.records = {identity: value for (role, identity), value in self.assets.items() if role == "cache-record"}
        self.invocations = {identity: value for (role, identity), value in self.assets.items() if role == "cache-campaign-invocation"}
        self.reports = {identity: value for (role, identity), value in self.assets.items() if role == "cache-mutation-report"}
        self.vector = read_json(root / "vectors" / "cache-semantics-vectors.json")
        self.ok(self.vector["artifactCatalogDigest"] == self.catalog["catalogId"], "BAG-14 evidence vector does not bind its authoritative resolver snapshot")

    @staticmethod
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError(f"duplicate object key {name}")
            result[name] = value
        return result

    def only(self, role: str) -> dict[str, Any]:
        matches = [value for (item_role, _), value in self.assets.items() if item_role == role]
        self.ok(len(matches) == 1, f"BAG-14 expected one {role}")
        return matches[0]

    def validate_catalog_identity(self, role: str, identity: str, value: dict[str, Any]) -> None:
        self_ids = {
            "cache-campaign-manifest": "manifestId",
            "cache-record": "recordId",
            "cache-campaign-invocation": "campaignInvocationId",
            "cache-mutation-report": "reportId",
            "oracle-declaration": "declarationId",
            "oracle-operand": "operandId",
            "baseline-oracle-gate-result": "gateResultId",
            "oracle-comparison-result": "comparisonId",
            "terminal-state": "terminalStateDigest",
            "semantic-crash": "crashDigest",
        }
        field = self_ids.get(role)
        if field is not None:
            self.ok(value.get(field) == identity, f"BAG-14 catalog key differs from embedded {role} self identity")

    def resolve(self, artifact: dict[str, str]) -> dict[str, Any]:
        self.ok(set(artifact) == {"role", "digest"}, "BAG-14 artifact key is open or incomplete")
        identity = (artifact["role"], artifact["digest"])
        self.ok(identity in self.entries, f"BAG-14 unresolved artifact {artifact}")
        return self.assets.get(identity, self.entries[identity])

    def artifact_keys(self, value: Any) -> list[dict[str, str]]:
        result: list[dict[str, str]] = []
        if isinstance(value, dict):
            if set(value) == {"role", "digest"} and isinstance(value["role"], str):
                result.append(value)
            else:
                for item in value.values():
                    result.extend(self.artifact_keys(item))
        elif isinstance(value, list):
            for item in value:
                result.extend(self.artifact_keys(item))
        return result

    def validate_definition(self, value: dict[str, Any], role: str) -> None:
        family_id = digest("k-in-k/baseline-family/v1", value["family"])
        self.ok(value["baselineFamilyId"] == family_id, f"BAG-14 {role} baseline-family identity drift")
        for module in value["modules"]:
            for sentence in module["sentences"]:
                provenance = sentence["provenance"]
                expected_lineage = digest(
                    "k-in-k/input-lineage/v1",
                    {
                        "baselineFamilyId": family_id,
                        "module": module["name"],
                        "source": sentence["value"]["source"],
                        "location": sentence["value"]["location"],
                        "kind": sentence["value"]["kind"],
                        "sourceOccurrenceOrdinal": sentence["sourceOccurrenceOrdinal"],
                    },
                )
                self.ok(provenance["lineageId"] == expected_lineage, f"BAG-14 {role} input-lineage identity drift")
        self.ok(refreshed_definition(value) == value, f"BAG-14 {role} sentence/module/definition identity drift")

    def selector_value(self, sentence: dict[str, Any], path: list[dict[str, Any]]) -> dict[str, Any] | None:
        current: Any = sentence["value"]
        for step in path:
            if step["kind"] == "field":
                name = step["name"]
                if name == "lhs":
                    current = current.get("node", {}).get("left")
                elif name == "rhs":
                    current = current.get("node", {}).get("right")
                elif isinstance(current, dict):
                    current = current.get(name)
                else:
                    return None
            elif step["kind"] == "argument":
                args = current.get("node", {}).get("args", []) if isinstance(current, dict) else []
                current = args[step["index"]] if step["index"] < len(args) else None
            elif step["kind"] == "item":
                items = current.get("node", {}).get("items", []) if isinstance(current, dict) else []
                current = items[step["index"]] if step["index"] < len(items) else None
            else:
                return None
            if current is None:
                return None
        return current if isinstance(current, dict) else None

    def selected_lineages(self, definition: dict[str, Any], selector: dict[str, Any]) -> dict[str, list[str]]:
        result: dict[str, list[str]] = {}
        for clause in selector["clauses"]:
            matches = []
            for module in definition["modules"]:
                for sentence in module["sentences"]:
                    sentence_value = sentence["value"]
                    if sentence_value["kind"] not in clause["sentenceKinds"]:
                        continue
                    if clause["label"] is not None and sentence_value["label"] != clause["label"]:
                        continue
                    term = self.selector_value(sentence, clause["termPath"])
                    if term is None or term.get("sort") != clause["termSort"]:
                        continue
                    head = term.get("node", {}).get("label") if term.get("node", {}).get("kind") == "application" else None
                    if clause["termHeadLabel"] is not None and head != clause["termHeadLabel"]:
                        continue
                    matches.append(sentence["provenance"]["lineageId"])
            result[clause["role"]] = matches
        return result

    def validate_patch_materialization(self, baseline: dict[str, Any], mutant: dict[str, Any], operator: dict[str, Any], selector: dict[str, Any], patch: dict[str, Any]) -> None:
        self.ok(selector["selectorDigest"] == digest("k-in-k/mutation-selector/v1", selector["clauses"]), "BAG-14 selector identity drift")
        self.ok(operator["selectorDigest"] == selector["selectorDigest"], "BAG-14 operator selected another selector")
        self.ok(operator["operatorDigest"] == digest("k-in-k/mutation-operator/v1", without(operator, "operatorDigest")), "BAG-14 operator identity drift")
        self.ok(patch["operatorId"] == operator["operatorId"] and patch["operatorVersion"] == operator["operatorVersion"], "BAG-14 patch/operator identity drift")
        for edit in patch["edits"]:
            self.ok(edit["editId"] == digest("k-in-k/edit/v1", without(edit, "editId")), "BAG-14 patch edit identity drift")
        ordered = sorted(patch["edits"], key=lambda item: (item["targetLineage"] or "", canonical(item["targetPath"]), item["operation"], item["editId"]))
        self.ok(patch["edits"] == ordered, "BAG-14 patch edit order drift")
        self.ok(patch["patchId"] == digest("k-in-k/patch/v1", {"schemaVersion": patch["schemaVersion"], "edits": patch["edits"]}), "BAG-14 patch identity drift")

        selections = self.selected_lineages(baseline, selector)
        self.ok(all(len(lineages) == 1 for lineages in selections.values()), "BAG-14 selector does not derive one exact finite site per role")
        authorized = {lineage for lineages in selections.values() for lineage in lineages}
        self.ok({edit["targetLineage"] for edit in patch["edits"]} == authorized, "BAG-14 patch target is not the exact selector-derived site")

        expected = deepcopy(baseline)
        by_lineage = {
            sentence["provenance"]["lineageId"]: sentence
            for module in expected["modules"] for sentence in module["sentences"]
        }
        for edit in patch["edits"]:
            target = by_lineage.get(edit["targetLineage"])
            self.ok(target is not None and edit["expectedContent"] == target["provenance"]["contentFingerprint"], "BAG-14 patch precondition does not bind the selected baseline sentence")
            self.ok(edit["operation"] == "add-attribute" and edit["expectedAttributeFingerprint"] is None, "BAG-14 finite patch uses another operation/precondition")
            attribute = edit["value"]
            expected_path = [{"kind": "field", "name": "attributes"}, {"kind": "attribute", "name": attribute["name"]}]
            self.ok(edit["targetPath"] == expected_path and attribute["kind"] == "attribute", "BAG-14 attribute patch path/value drift")
            attributes = target["value"]["attributes"]
            self.ok(attribute["name"] not in {item["name"] for item in attributes}, "BAG-14 attribute patch overwrites an existing attribute")
            attributes.append({"name": attribute["name"], "value": attribute["value"]})
            attributes.sort(key=lambda item: item["name"])
        expected = refreshed_definition(expected)
        self.ok(expected == mutant, "BAG-14 patch application does not produce the cataloged mutant definition")

    def validate_terminal_asset(self, value: dict[str, Any]) -> None:
        self.ok(value["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", without(value, "terminalStateDigest")), "BAG-14 terminal-state identity drift")
        definitions = {
            identity for (role, identity) in self.assets
            if role in {"definition", "mutant-definition"}
        }
        self.ok(value["definitionDigest"] in definitions, "BAG-14 terminal state resolves another definition")

    def validate_trace_asset(self, identity: str, value: dict[str, Any]) -> None:
        self.ok(identity == digest("k-in-k/event-trace/v1", value), "BAG-14 event-trace semantic identity drift")
        expected_path = digest("k-in-k/unkeyed-path/v1", without(value, "pathOrdinal", "pathKey", "pathIdentityDigest"))
        self.ok(value["pathIdentityDigest"] == expected_path, "BAG-14 event-trace path identity drift")
        terminal = self.resolve(value["executionTerminal"]["artifact"])
        terminal = self.resolve(terminal["terminalState"]) if value["executionTerminal"]["kind"] == "semantic-crash" else terminal
        self.ok(terminal["definitionDigest"] == value["definitionDigest"], "BAG-14 trace terminal resolves another definition")
        expected_stop = "stuck" if value["executionTerminal"]["kind"] == "stuck" else "terminal"
        self.ok(value["complete"] and value["stopReason"] == expected_stop, "BAG-14 finite trace completion/terminal drift")

    def validate_operand_asset(self, value: dict[str, Any]) -> None:
        declaration = self.resolve(value["declaration"])
        completion = value["completionEvidence"]
        terminal = completion["terminal"]
        expected = cache_operand(declaration, value["subject"], terminal["artifact"], completion["producerTrace"], terminal["kind"])
        self.ok(value == expected, "BAG-14 oracle operand semantic identity/value/provenance drift")
        trace = self.resolve(completion["producerTrace"])
        self.ok(trace["executionTerminal"] == terminal, "BAG-14 oracle operand terminal is not its producer trace terminal")
        test = self.test_by_digest(declaration["testInvocationDigest"])
        self.ok(trace["testId"] == test["testId"], "BAG-14 oracle operand producer trace belongs to another test")
        terminal_value = self.resolve(terminal["artifact"])
        subject_definition = value["subject"].get("definitionDigest", value["subject"].get("mutantDefinitionDigest"))
        self.ok(terminal_value["definitionDigest"] == subject_definition == trace["definitionDigest"], "BAG-14 oracle operand subject/terminal/trace definition drift")

    def validate_declaration_asset(self, value: dict[str, Any]) -> None:
        self.ok(value["declarationId"] == digest("k-in-k/oracle-declaration/v1", without(value, "declarationId")), "BAG-14 declaration semantic identity drift")
        test = self.test_by_digest(value["testInvocationDigest"])
        declaration_key = key("oracle-declaration", value["declarationId"])
        self.ok(value["slotOrdinal"] < len(test["oracleDeclarations"]) and test["oracleDeclarations"][value["slotOrdinal"]] == declaration_key, "BAG-14 declaration is not the exact ordered manifest test slot")
        expected = cache_declaration(
            test,
            self.manifest,
            value["slotOrdinal"],
            value["slotId"],
            execution_pattern=value["kind"] == "execution-pattern",
            allow_crash=value["kind"] != "execution-pattern" and value["baselineTerminalPolicy"] == "normal-or-crash",
        )
        self.ok(value == expected, "BAG-14 finite declaration profiles/policies/built-in authority drift")

    def validate_gate_asset(self, value: dict[str, Any]) -> None:
        declaration = self.resolve(value["declaration"])
        test = self.test_by_digest(declaration["testInvocationDigest"])
        side = value["actualSide"]
        self.ok(side["side"] == "baseline" and ((side["normalOperand"] is None) != (side["semanticCrash"] is None)), "BAG-14 finite baseline gate side drift")
        value_key = side["normalOperand"] or side["semanticCrash"]
        semantic = self.validate_semantic_input(value["declaration"], test, "baseline", value_key)
        expected = cache_gate(declaration, semantic, value_key)
        self.ok(value == expected, "BAG-14 baseline gate outcome/status was not derived from its declaration and semantic input")

    def validate_comparison_asset(self, value: dict[str, Any]) -> None:
        declaration = self.resolve(value["declaration"])
        test = self.test_by_digest(declaration["testInvocationDigest"])
        self.ok([side["side"] for side in value["sides"]] == ["baseline", "mutant"], "BAG-14 finite comparison side order drift")
        value_keys = [side["normalOperand"] or side["semanticCrash"] for side in value["sides"]]
        self.ok(all(item is not None for item in value_keys), "BAG-14 finite comparison side omitted its closed semantic input")
        values = [self.validate_semantic_input(value["declaration"], test, side, item) for side, item in zip(("baseline", "mutant"), value_keys)]
        terminals = None
        if all(item["role"] == "semantic-crash" for item in value_keys):
            terminals = tuple(self.resolve(item["terminalState"]) for item in values)
        expected = cache_comparison(declaration, values[0], value_keys[0], values[1], value_keys[1], crash_terminals=terminals)
        self.ok(value == expected, "BAG-14 comparison identity/projection/outcome was not derived from its declaration and operands")

    def validate_crash_asset(self, identity: str, value: dict[str, Any]) -> None:
        self.ok(identity == value["crashDigest"] == digest("k-in-k/semantic-crash/v1", without(value, "crashDigest")), "BAG-14 semantic-crash identity drift")
        self.ok(value["executionProfileDigest"] == self.manifest["executionProfile"]["digest"], "BAG-14 semantic-crash execution profile drift")
        self.resolve(value["terminalState"])

    def validate_semantic_assets(self) -> None:
        baseline = self.resolve(self.manifest["baselineDefinition"])
        mutant = self.resolve(self.manifest["candidate"]["mutantDefinition"])
        self.ok(self.manifest["baselineDefinition"]["digest"] == baseline["definitionDigest"], "BAG-14 baseline catalog key differs from its semantic identity")
        self.ok(self.manifest["candidate"]["mutantDefinition"]["digest"] == mutant["definitionDigest"], "BAG-14 mutant catalog key differs from its semantic identity")
        self.validate_definition(baseline, "baseline definition")
        self.validate_definition(mutant, "mutant definition")
        operator = self.only("mutation-operator")
        operator_key = next(key(role, identity) for (role, identity) in self.assets if role == "mutation-operator")
        self.ok(operator_key["digest"] == operator["operatorDigest"], "BAG-14 operator catalog key differs from its semantic identity")
        selector = self.resolve(key("mutation-selector", operator["selectorDigest"]))
        patch = self.resolve(self.manifest["candidate"]["patch"])
        self.ok(self.manifest["candidate"]["patch"]["digest"] == patch["patchId"], "BAG-14 patch catalog key differs from its semantic identity")
        self.validate_patch_materialization(baseline, mutant, operator, selector, patch)
        compatibility = self.resolve(self.manifest["compatibilityProfile"])
        self.ok(self.manifest["compatibilityProfile"]["digest"] == digest("k-in-k/compatibility-profile/v1", compatibility), "BAG-14 compatibility-profile identity drift")

        for (role, identity), value in self.assets.items():
            if role == "terminal-state":
                self.ok(identity == value["terminalStateDigest"], "BAG-14 catalog terminal key differs from embedded identity")
                self.validate_terminal_asset(value)
            elif role == "event-trace":
                self.validate_trace_asset(identity, value)
            elif role == "semantic-crash":
                self.validate_crash_asset(identity, value)
            elif role == "oracle-declaration":
                self.ok(identity == value["declarationId"], "BAG-14 catalog declaration key differs from embedded identity")
                campaign_digests = {test["testInvocationDigest"] for test in self.manifest["tests"]}
                if value["testInvocationDigest"] in campaign_digests:
                    self.validate_declaration_asset(value)
                else:
                    self.ok(key(role, identity) == self.vector["queryCoupledRegression"]["selectedDeclaration"], "BAG-14 unrelated external oracle declaration entered derivative catalog")
            elif role == "oracle-operand":
                self.ok(identity == value["operandId"], "BAG-14 catalog operand key differs from embedded identity")
                self.validate_operand_asset(value)
            elif role == "baseline-oracle-gate-result":
                self.ok(identity == value["gateResultId"] == digest("k-in-k/baseline-oracle-gate-result/v1", without(value, "gateResultId")), "BAG-14 baseline-gate semantic identity drift")
                self.validate_gate_asset(value)
            elif role == "oracle-comparison-result":
                self.ok(identity == value["comparisonId"] == digest("k-in-k/oracle-comparison-result/v1", without(value, "comparisonId")), "BAG-14 comparison semantic identity drift")
                self.validate_comparison_asset(value)

    def validate_manifest(self, value: dict[str, Any] | None = None) -> None:
        manifest = self.manifest if value is None else value
        self.ok(manifest["manifestId"] == digest("k-in-k/cache-campaign-manifest/v1", without(manifest, "manifestId")), "BAG-14 campaign manifest identity drift")
        for name in ("baselineDefinition", "compatibilityProfile", "loweringProfile", "executionProfile", "solverProfile"):
            self.resolve(manifest[name])
        candidate = manifest["candidate"]
        patch = self.resolve(candidate["patch"])
        self.resolve(candidate["mutantDefinition"])
        operator = self.only("mutation-operator")
        for role, artifact_digest in (
            ("mutation-module", operator["moduleDigest"]), ("mutation-selector", operator["selectorDigest"]),
            ("precondition", operator["preconditionDigest"]), ("postcondition", operator["postconditionDigest"]),
            ("patch-template", operator["patchTemplateDigest"]),
        ):
            self.resolve(key(role, artifact_digest))
        selector = self.resolve(key("mutation-selector", operator["selectorDigest"]))
        selector_roles = [clause["role"] for clause in selector["clauses"]]
        interface_operations = [item["operation"] for item in operator["patchTemplateRoles"]]
        self.ok([edit["operation"] for edit in patch["edits"]] == interface_operations, "BAG-14 operator/template operations do not exactly authorize the patch")
        self.ok([role for item in operator["patchTemplateRoles"] for role in item["sourceSelectorRoles"]] == selector_roles, "BAG-14 operator/template selector interface drift")
        baseline_digest = manifest["baselineDefinition"]["digest"]
        expected_candidate = digest("k-in-k/candidate/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": baseline_digest, "patchId": patch["patchId"]})
        expected_mutant = digest("k-in-k/mutant/v1", {"baselineDefinitionDigest": baseline_digest, "patchId": patch["patchId"]})
        self.ok(candidate["candidateId"] == expected_candidate and candidate["mutantId"] == expected_mutant, "BAG-14 enclosing candidate/materialization identity drift")
        isolation = manifest["isolationPolicy"]
        self.ok(isolation["isolationPolicyDigest"] == digest("k-in-k/isolation-policy/v1", without(isolation, "isolationPolicyDigest")), "BAG-14 isolation policy digest drift")
        test_ids = [test["testId"] for test in manifest["tests"]]
        self.ok(len(test_ids) == len(set(test_ids)) and len(test_ids) >= 1, "BAG-14 campaign test slots are incomplete or duplicated")
        for test in manifest["tests"]:
            for field in ("program", "parser", "options"):
                self.resolve(test[field])
            self.ok(test["testInvocationDigest"] == test_invocation_digest(test, manifest), "BAG-14 test invocation does not close parser/start/options/bounds/profiles")
            self.ok(test["attemptKind"] == {"kind": "ordinary"}, "BAG-14 repo-reusable derivative campaign is not ordinary")
            slot_ids = []
            for slot_ordinal, declaration_key in enumerate(test["oracleDeclarations"]):
                declaration = self.resolve(declaration_key)
                self.ok(declaration["testInvocationDigest"] == test["testInvocationDigest"] and declaration["slotOrdinal"] == slot_ordinal, "BAG-14 declaration is scoped to another test or ordered slot")
                slot_ids.append(declaration["slotId"])
            self.ok(len(slot_ids) == len(set(slot_ids)), "BAG-14 ordered declaration slots repeat a slot identity")

    def test_by_digest(self, identity: str) -> dict[str, Any]:
        matches = [test for test in self.manifest["tests"] if test["testInvocationDigest"] == identity]
        self.ok(len(matches) == 1, "BAG-14 key does not resolve one exact test slot")
        return matches[0]

    def validate_execution_key(self, value: dict[str, Any]) -> None:
        self.ok(value["keyDigest"] == digest(DOMAINS["execution-attempt"], without(value, "keyDigest")), "BAG-14 execution key digest drift")
        operation = value["operation"]
        self.ok(
            operation["operationId"] == "portable-finite-execution"
            and operation["operationVersion"] in {1, 2, 3}
            and operation["adapterId"] == "bag14-vector-adapter"
            and operation["adapterVersion"] == 1,
            "BAG-14 execution operation/adapter authority drift",
        )
        test = self.test_by_digest(value["testInvocationDigest"])
        self.ok(value["attemptKind"] == test["attemptKind"], "BAG-14 attempt/query/observation kind differs from its test slot")
        expected_roots = {
            "compatibilityProfileDigest": self.manifest["compatibilityProfile"]["digest"],
            "loweringProfileDigest": self.manifest["loweringProfile"]["digest"],
            "executionProfileDigest": self.manifest["executionProfile"]["digest"],
            "solverProfileDigest": self.manifest["solverProfile"]["digest"],
        }
        self.ok(all(value[name] == expected for name, expected in expected_roots.items()), "BAG-14 execution key profile drift")
        self.ok(value["isolationPolicy"] == self.manifest["isolationPolicy"], "BAG-14 execution key isolation drift")
        subject = value["subject"]
        if subject["kind"] == "baseline":
            self.ok(subject["definition"] == self.manifest["baselineDefinition"], "BAG-14 baseline subject reversal/drift")
        else:
            candidate = self.manifest["candidate"]
            operator = self.only("mutation-operator")
            self.ok(subject["baselineDefinition"] == self.manifest["baselineDefinition"] and subject["candidateId"] == candidate["candidateId"] and subject["patch"] == candidate["patch"] and subject["mutantId"] == candidate["mutantId"] and subject["mutantDefinition"] == candidate["mutantDefinition"] and subject["operator"] == key("mutation-operator", operator["operatorDigest"]), "BAG-14 mutant subject does not equal enclosing materialization")
        for artifact in self.artifact_keys(value):
            self.resolve(artifact)

    def validate_query_coupled_regression(self, value: dict[str, Any] | None = None) -> None:
        regression = self.vector["queryCoupledRegression"] if value is None else value
        active_catalog = read_json(self.fixtures / "artifact-catalog.json")
        active_manifest = read_json(self.fixtures / "mutation-manifest.json")
        corpus = read_json(self.fixtures / "corpus-manifest.json")
        self.ok(active_catalog["catalogId"] == digest("k-in-k/artifact-catalog/v1", without(active_catalog, "catalogId")), "BAG-14 active query catalog identity drift")
        self.ok(active_manifest["manifestId"] == digest("k-in-k/mutation-manifest/v1", without(active_manifest, "manifestId")), "BAG-14 active query manifest identity drift")
        self.ok(regression["activeCatalogDigest"] == active_manifest["artifactCatalogDigest"] == active_catalog["catalogId"] and regression["activeManifestId"] == active_manifest["manifestId"], "BAG-14 query regression is orphaned from active catalog/manifest authority")
        active_entries = {(entry["role"], entry["digest"]): entry for entry in active_catalog["entries"]}
        tests = [test for test in active_manifest["tests"] if test["testId"] == regression["testId"]]
        self.ok(len(tests) == 1, "BAG-14 active query test selection is fabricated or ambiguous")
        test = tests[0]
        slot = regression["slotOrdinal"]
        self.ok(slot == 12 and regression["selectedDeclaration"] == key("oracle-declaration", "65ae3e3c775dc834554e9d681c442a6ecf8351948a0028402951464e27a1e173"), "BAG-14 query regression changed the exact accepted active declaration selection")
        self.ok(slot < len(test["oracleDeclarations"]) and test["oracleDeclarations"][slot] == regression["selectedDeclaration"], "BAG-14 active query declaration slot/order drift")
        declaration_key = regression["selectedDeclaration"]
        declaration_entry = active_entries.get((declaration_key["role"], declaration_key["digest"]))
        self.ok(declaration_entry is not None and declaration_entry["availability"] == "bundled", "BAG-14 active query declaration lacks catalog authority")
        declaration = self.resolve(declaration_key)
        execution = regression["executionKey"]
        self.ok(execution["keyDigest"] == digest(DOMAINS["execution-attempt"], without(execution, "keyDigest")), "BAG-14 query-coupled regression key identity drift")
        self.ok(declaration["declarationId"] == digest("k-in-k/oracle-declaration/v1", without(declaration, "declarationId")), "BAG-14 selected query declaration identity drift")
        attempt = execution["attemptKind"]
        self.ok(attempt["kind"] == "query-coupled" and declaration["kind"] == "execution-pattern", "BAG-14 query regression changed attempt/declaration kind")
        self.ok(execution["testInvocationDigest"] == test["invocationDigest"] == declaration["testInvocationDigest"] and declaration["slotOrdinal"] == slot, "BAG-14 query regression declaration selects another test invocation/slot")
        selected_roots = [deepcopy(item) for item in test["patternQueries"]]
        selected_declarations = []
        for item in test["oracleDeclarations"]:
            entry = active_entries.get((item["role"], item["digest"]))
            self.ok(entry is not None and entry["availability"] == "bundled" and entry["logicalPath"].startswith("repo://"), "BAG-14 active query declaration order contains an unresolved slot")
            selected_declarations.append(read_json(self.root.parents[1] / entry["logicalPath"].removeprefix("repo://")))
        expected_roots = [deepcopy(item["kindConfig"]) for item in selected_declarations if item["kind"] == "execution-pattern"]
        expected_roots = [{name: item[name] for name in ("patternSource", "patternPlan", "patternQuery")} for item in expected_roots]
        self.ok(selected_roots == expected_roots and selected_roots.count(selected_roots[0]) >= 2, "BAG-14 active query roots lost declaration order/repetitions")
        repeated = {name: deepcopy(attempt[name]) for name in ("patternSource", "patternPlan", "patternQuery", "searchPolicy")}
        self.ok(declaration["kindConfig"] == {"kind": "execution-pattern", **repeated}, "BAG-14 query attempt roots/order differ from the selected execution-pattern declaration")
        query = self.resolve(attempt["patternQuery"])
        plan = self.resolve(attempt["patternPlan"])
        self.resolve(attempt["patternSource"])
        self.ok(query["queryId"] == digest("k-in-k/pattern-query/v1", without(query, "queryId")), "BAG-14 query self identity drift")
        self.ok(query["patternSource"] == attempt["patternSource"] and query["patternPlan"] == attempt["patternPlan"], "BAG-14 incoherent query/source/plan triple")
        self.ok(plan["patternPlanDigest"] == attempt["patternPlan"]["digest"] == digest("k-in-k/pattern-plan/v1", without(plan, "patternPlanDigest")), "BAG-14 query plan semantic identity drift")
        observation = self.resolve(attempt["observationInputs"][0])
        self.ok(observation["manifestId"] == digest("k-in-k/observation-manifest/v1", without(observation, "manifestId")), "BAG-14 query observation manifest identity drift")
        self.ok(observation["eventVocabularyDigest"] == digest("k-in-k/event-vocabulary/v1", observation["eventVocabulary"]) == plan["eventVocabularyDigest"], "BAG-14 query observation vocabulary/plan drift")
        self.ok(observation["inputDefinitionDigest"] == observation["outputDefinitionDigest"] == execution["subject"]["definition"]["digest"] == active_manifest["definitionDigest"], "BAG-14 query observation/definition root drift")
        self.ok(("definition", active_manifest["definitionDigest"]) in active_entries, "BAG-14 query definition root lacks active catalog authority")
        self.ok(attempt["searchPolicy"] == declaration["kindConfig"]["searchPolicy"], "BAG-14 query search policy differs from selected declaration")
        for observation in attempt["observationInputs"]:
            self.resolve(observation)
        self.ok(execution["subject"] == {"kind": "baseline", "definition": key("definition", active_manifest["definitionDigest"])}, "BAG-14 query regression subject drift")
        self.ok(execution["compatibilityProfileDigest"] == corpus["compatibilityProfileDigest"] == declaration["compatibilityProfileDigest"] and execution["loweringProfileDigest"] == active_manifest["loweringProfileDigest"] and execution["executionProfileDigest"] == corpus["executionProfileDigest"] == declaration["executionProfileDigest"] and execution["solverProfileDigest"] == corpus["solverProfileDigest"] == declaration["solverProfileDigest"], "BAG-14 query regression profile/declaration drift")
        self.ok(execution["isolationPolicy"] == self.manifest["isolationPolicy"] and execution["operation"] == {"operationId": "portable-finite-execution", "operationVersion": 1, "adapterId": "bag14-vector-adapter", "adapterVersion": 1}, "BAG-14 query execution policy/operation drift")

    def validate_oracle_key(self, value: dict[str, Any]) -> None:
        self.ok(value["keyDigest"] == digest(DOMAINS["oracle-evaluation"], without(value, "keyDigest")), "BAG-14 oracle key digest drift")
        self.ok(value["operation"] == {"operationId": "portable-oracle-evaluation", "operationVersion": 1, "adapterId": "bag14-vector-adapter", "adapterVersion": 1}, "BAG-14 oracle operation/adapter authority drift")
        self.ok(value["evaluator"] == {"evaluatorId": "bag12-portable-exit-stop", "evaluatorVersion": 1, "mode": "built-in"}, "BAG-14 oracle evaluator authority drift")
        declaration = self.resolve(value["declaration"])
        test = self.test_by_digest(declaration["testInvocationDigest"])
        self.ok(value["declaration"] in test["oracleDeclarations"], "BAG-14 oracle key selected another declaration slot")
        expected_sides = ["baseline"] if value["evaluationKind"] == "baseline-admission" else ["baseline", "mutant"]
        self.ok([item["side"] for item in value["semanticInputs"]] == expected_sides, "BAG-14 oracle operand order drift")
        for item in value["semanticInputs"]:
            self.validate_semantic_input(value["declaration"], test, item["side"], item["value"])

    def validate_semantic_input(self, declaration_key: dict[str, str], test: dict[str, Any], side: str, semantic_key: dict[str, str]) -> dict[str, Any]:
        self.ok(semantic_key["role"] in {"oracle-operand", "semantic-crash"}, "BAG-14 oracle semantic input escaped the closed operand/crash union")
        semantic = self.resolve(semantic_key)
        definition_digest = self.manifest["baselineDefinition"]["digest"] if side == "baseline" else self.manifest["candidate"]["mutantDefinition"]["digest"]
        if semantic_key["role"] == "oracle-operand":
            self.validate_operand_asset(semantic)
            self.ok(semantic["declaration"] == declaration_key and semantic["subject"]["side"] == side, "BAG-14 oracle operand declaration/side drift")
            subject_definition = semantic["subject"].get("definitionDigest", semantic["subject"].get("mutantDefinitionDigest"))
            self.ok(subject_definition == definition_digest and semantic["testInvocationDigest"] == test["testInvocationDigest"], "BAG-14 oracle operand test/definition provenance drift")
        else:
            declaration = self.resolve(declaration_key)
            self.validate_crash_asset(semantic_key["digest"], semantic)
            self.ok(declaration["crashPolicy"] == "semantic-crash-distinguishes", "BAG-14 semantic input used an unsupported crash policy")
            if side == "baseline":
                self.ok(declaration["baselineTerminalPolicy"] == "normal-or-crash", "BAG-14 normal-only declaration admitted a baseline semantic crash")
            terminal = self.resolve(semantic["terminalState"])
            self.ok(terminal["definitionDigest"] == definition_digest, "BAG-14 semantic-crash terminal belongs to another side definition")
            traces = [
                trace for (role, _), trace in self.assets.items()
                if role == "event-trace"
                and trace["testId"] == test["testId"]
                and trace["definitionDigest"] == definition_digest
                and trace["executionTerminal"] == {"kind": "semantic-crash", "artifact": semantic_key}
            ]
            self.ok(len(traces) == 1, "BAG-14 semantic-crash lacks one exact test/side producer trace")
        return semantic

    def derive_oracle_result(self, oracle_value: dict[str, Any]) -> tuple[dict[str, str], dict[str, Any]]:
        self.validate_oracle_key(oracle_value)
        declaration = self.resolve(oracle_value["declaration"])
        test = self.test_by_digest(declaration["testInvocationDigest"])
        values = [self.validate_semantic_input(oracle_value["declaration"], test, item["side"], item["value"]) for item in oracle_value["semanticInputs"]]
        keys = [item["value"] for item in oracle_value["semanticInputs"]]
        if oracle_value["evaluationKind"] == "baseline-admission":
            result = cache_gate(declaration, values[0], keys[0])
            return key("baseline-oracle-gate-result", result["gateResultId"]), result
        crash_terminals = None
        if all(item["role"] == "semantic-crash" for item in keys):
            crash_terminals = tuple(self.resolve(item["terminalState"]) for item in values)
        result = cache_comparison(declaration, values[0], keys[0], values[1], keys[1], crash_terminals=crash_terminals)
        return key("oracle-comparison-result", result["comparisonId"]), result

    def validate_finite_registry(self) -> None:
        registry = self.vector["finiteVectorRegistry"]
        expected = {
            "bag14.execution-terminal.v1": ("cache-record", ["terminal-state", "event-trace"]),
            "bag14.baseline-gate.v1": ("cache-record", ["baseline-oracle-gate-result"]),
            "bag14.oracle-comparison.v1": ("cache-record", ["oracle-comparison-result"]),
            "bag14.exact-bounded-stop.v1": ("cache-record", []),
            "bag14.diagnostic-failure.v1": ("cache-record", []),
            "bag14.oracle-operand-production.v1": ("oracle-operand-production", ["oracle-operand"]),
        }
        self.ok(set(registry) == set(expected), "BAG-14 finite producer registry has an unknown or missing operation")
        produced_operands: list[dict[str, str]] = []
        for vector_id, specification in registry.items():
            kind_value, output_roles = expected[vector_id]
            self.ok(set(specification) == {"kind", "outputRoles", "rows"} and specification["kind"] == kind_value and specification["outputRoles"] == output_roles and specification["rows"], "BAG-14 finite producer specification is open, incomplete, or role-drifted")
            row_digests = []
            for row in specification["rows"]:
                expected_fields = {"inputs", "inputDigest", "outputKeys"}
                if kind_value == "cache-record":
                    expected_fields.add("terminalRecord")
                self.ok(set(row) == expected_fields, "BAG-14 finite producer row is open or incomplete")
                self.ok(row["inputDigest"] == finite_input_digest(vector_id, row["inputs"]), "BAG-14 finite producer input digest covers expectations or drifted inputs")
                self.ok([item["role"] for item in row["outputKeys"]] == output_roles, "BAG-14 finite producer row output role/order drift")
                row_digests.append(row["inputDigest"])
                for output in row["outputKeys"]:
                    self.resolve(output)
                if kind_value == "cache-record":
                    self.ok(set(row["inputs"]) == {"keyDigest"}, "BAG-14 cache finite row input is not the cycle-free request key")
                    requests = [
                        record for record in self.records.values()
                        if record["keyDigest"] == row["inputs"]["keyDigest"] and record["productionEvidence"]["vectorId"] == vector_id
                    ]
                    self.ok(len(requests) == 1, "BAG-14 finite cache row does not resolve one exact request key")
                    request = requests[0]
                    derived_outputs = self.derived_outputs(request)
                    self.ok(row["terminalRecord"] == request["terminalRecord"] and row["outputKeys"] == derived_outputs, "BAG-14 finite row terminal/output is not independently derived from its request key inputs")
                else:
                    self.ok(set(row["inputs"]) == {"declaration", "subject", "terminal", "producerTrace"}, "BAG-14 operand producer input is open or incomplete")
                    inputs = row["inputs"]
                    declaration = self.resolve(inputs["declaration"])
                    trace = self.resolve(inputs["producerTrace"])
                    terminal = self.resolve(inputs["terminal"])
                    self.ok(trace["executionTerminal"]["artifact"] == inputs["terminal"], "BAG-14 operand finite producer consumes another trace terminal")
                    expected_operand = cache_operand(declaration, inputs["subject"], inputs["terminal"], inputs["producerTrace"], trace["executionTerminal"]["kind"])
                    output_operand = self.resolve(row["outputKeys"][0])
                    self.ok(output_operand == expected_operand and terminal["definitionDigest"] == trace["definitionDigest"], "BAG-14 operand finite producer output was not independently derived")
                    produced_operands.extend(row["outputKeys"])
            self.ok(len(row_digests) == len(set(row_digests)), "BAG-14 finite producer has duplicate input rows")
        expected_operands = sorted(
            [key(role, identity) for (role, identity) in self.assets if role == "oracle-operand"],
            key=canonical,
        )
        self.ok(sorted(produced_operands, key=canonical) == expected_operands, "BAG-14 oracle operand graph lacks one-to-one finite production evidence")

    def derived_reuse(self, record: dict[str, Any]) -> tuple[str, str]:
        terminal = record["terminalRecord"]
        conformance = record["completion"]["executionConformance"]
        if conformance == "not-proven" or terminal["kind"] == "diagnostic-only":
            return "diagnostic-only", "not-reusable"
        if terminal["kind"] in {"bounded-stop", "bounded-unknown"}:
            return "exact-bounded-attempt", "exact-bounded-attempt"
        if record["kind"] == "oracle-evaluation" and terminal["kind"] == "baseline-gate":
            result = self.resolve(terminal["result"])
            if result["status"] != "accepted":
                return "diagnostic-only", "not-reusable"
        return "semantic-result", "semantic-result"

    def derive_execution_result(self, execution: dict[str, Any], vector_id: str) -> tuple[dict[str, Any], list[dict[str, str]]]:
        """Compute the reviewed finite result from the cycle-free execution key."""
        test = self.test_by_digest(execution["testInvocationDigest"])
        test_index = self.manifest["tests"].index(test) + 1
        subject = execution["subject"]
        side = "baseline" if subject["kind"] == "baseline" else "mutant"
        definition_digest = subject["definition"]["digest"] if side == "baseline" else subject["mutantDefinition"]["digest"]
        if vector_id == "bag14.execution-terminal.v1":
            terminal_kind = "stuck" if side == "mutant" and test_index == 1 else "normal"
            terminal_text = "bag14-stuck" if terminal_kind == "stuck" else "bag14-done"
            terminal = cache_terminal(definition_digest, terminal_text)
            terminal_key = key("terminal-state", terminal["terminalStateDigest"])
            self.ok(self.resolve(terminal_key) == terminal, "BAG-14 reviewed finite execution terminal material drift")
            trace = cache_trace(test["testId"], f"root/{side}/{test_index}", definition_digest, terminal_key, terminal_kind)
            trace_key = key("event-trace", digest("k-in-k/event-trace/v1", trace))
            self.ok(self.resolve(trace_key) == trace, "BAG-14 reviewed finite execution trace material drift")
            return {"kind": terminal_kind, "terminal": terminal_key}, [terminal_key, trace_key]
        if vector_id == "bag14.exact-bounded-stop.v1":
            failure = {"stage": "execution", "classification": "time-limit", "context": "mutant-execution", "scope": "mutant", "retryability": "same-input-after-resource-change", "semanticEvidence": [], "details": {}}
            terminal = {"kind": "bounded-stop", "classification": "time-limit", "boundsDigest": digest("k-in-k/bounds/v1", test["bounds"]), "failure": failure}
            return terminal, []
        if vector_id == "bag14.diagnostic-failure.v1":
            failure = {"stage": "infrastructure", "classification": "worker-lost", "context": "mutant-execution", "scope": "mutant", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}
            return {"kind": "diagnostic-only", "failure": failure}, []
        self.ok(False, "BAG-14 execution record selected an unknown reviewed finite vector")
        raise AssertionError("unreachable")

    def derived_outputs(self, record: dict[str, Any]) -> list[dict[str, str]]:
        terminal = record["terminalRecord"]
        if record["kind"] == "execution-attempt":
            expected_terminal, expected_outputs = self.derive_execution_result(record["key"], record["productionEvidence"]["vectorId"])
            self.ok(terminal == expected_terminal, "BAG-14 execution terminal is not independently derived from its cycle-free request key")
            return expected_outputs
        if terminal["kind"] in {"bounded-stop", "bounded-unknown", "diagnostic-only"}:
            return []
        if record["kind"] == "oracle-evaluation":
            expected_key, expected_value = self.derive_oracle_result(record["key"])
            expected_kind = "baseline-gate" if record["key"]["evaluationKind"] == "baseline-admission" else "comparison"
            self.ok(terminal == {"kind": expected_kind, "result": expected_key}, "BAG-14 oracle terminal/result is not derived from exact key semanticInputs")
            self.ok(self.resolve(terminal["result"]) == expected_value, "BAG-14 oracle result material differs from exact key semanticInputs derivation")
            return [expected_key]
        self.ok(False, "BAG-14 non-oracle result escaped reviewed execution derivation")
        raise AssertionError("unreachable")

    def validate_record(self, record: dict[str, Any]) -> None:
        self.ok(record["recordId"] == digest("k-in-k/cache-record/v1", without(record, "recordId")), "BAG-14 cache record identity drift")
        self.ok(record["keyDigest"] == record["key"]["keyDigest"], "BAG-14 cache record repeats another key digest")
        if record["kind"] == "execution-attempt":
            self.validate_execution_key(record["key"])
        else:
            self.validate_oracle_key(record["key"])
        production = record["productionEvidence"]
        if production["mode"] == "operation-receipt":
            validator = self.api.get("validate_operation_receipt_production")
            self.ok(record["kind"] == "execution-attempt" and validator is not None, "BAG-14 operation-receipt production lacks BAG-15 authority")
            validator(record, production)
            self.ok(record["producedArtifacts"] == self.derived_outputs(record), "BAG-14 receipt-produced execution outputs differ from independently derived key result")
            return
        self.ok(production["mode"] == "finite-vector" and production["vectorId"] in self.vector["finiteVectorRegistry"], "BAG-14 unregistered/fabricated production evidence")
        specification = self.vector["finiteVectorRegistry"][production["vectorId"]]
        self.ok(specification["kind"] == "cache-record", "BAG-14 cache record cites a non-cache finite producer")
        expected_roles = specification["outputRoles"]
        self.ok([item["role"] for item in record["producedArtifacts"]] == expected_roles, "BAG-14 operation output role/order completeness drift")
        self.ok(record["producedArtifacts"] == self.derived_outputs(record), "BAG-14 terminal/result and exact finite-vector output keys disagree")
        self.ok(production["outputKeys"] == record["producedArtifacts"], "BAG-14 production evidence/output disagreement")
        inputs = {"keyDigest": record["keyDigest"]}
        expected_input = finite_input_digest(production["vectorId"], inputs)
        rows = [row for row in specification["rows"] if row["inputDigest"] == production["inputDigest"]]
        self.ok(production["inputDigest"] == expected_input and len(rows) == 1, "BAG-14 finite producer input was not recomputed/resolved")
        row = rows[0]
        self.ok(row["inputs"] == inputs and row["terminalRecord"] == record["terminalRecord"] and row["outputKeys"] == record["producedArtifacts"], "BAG-14 cache record terminal/output differs from its independent finite row")
        required_version = {"bag14.execution-terminal.v1": 1, "bag14.execution-crash.v1": 1, "bag14.exact-bounded-stop.v1": 2, "bag14.diagnostic-failure.v1": 3}.get(production["vectorId"])
        if record["kind"] == "execution-attempt":
            self.ok(record["key"]["operation"]["operationVersion"] == required_version, "BAG-14 execution operation version is unauthorized for its finite producer")
        for artifact in record["producedArtifacts"]:
            self.resolve(artifact)
        self.ok(record["completion"]["producerStatus"] == "complete" and record["completion"]["materialClosure"] == "repo-complete", "BAG-14 publication lacks positive producer/material completion")
        expected_class, expected_reuse = self.derived_reuse(record)
        self.ok(record["completion"]["evidenceClass"] == expected_class and record["reuseClass"] == expected_reuse, "BAG-14 completion/reuse class was trusted rather than derived")
        self.ok(record["completion"]["executionConformance"] == "finite-vector-proven", "BAG-14 finite evidence was relabelled native or left unproven")
        terminal = record["terminalRecord"]
        if terminal["kind"] == "bounded-stop":
            test = self.test_by_digest(record["key"]["testInvocationDigest"])
            self.ok(terminal["boundsDigest"] == digest("k-in-k/bounds/v1", test["bounds"]), "BAG-14 bounded result was reused under different bounds")
        if record["kind"] == "oracle-evaluation" and terminal["kind"] in {"baseline-gate", "comparison"}:
            result = self.resolve(terminal["result"])
            self.ok(result["declaration"] == record["key"]["declaration"], "BAG-14 oracle output belongs to another declaration")

    def operand_for(self, declaration_key: dict[str, str], side: str) -> dict[str, Any]:
        matches = [
            value for (role, _), value in self.assets.items()
            if role == "oracle-operand" and value["declaration"] == declaration_key and value["subject"]["side"] == side
        ]
        self.ok(len(matches) == 1, "BAG-14 declaration/side does not resolve one exact operand")
        return matches[0]

    def expected_plan(self) -> list[dict[str, Any]]:
        operator = self.only("mutation-operator")
        baseline_subject = {"kind": "baseline", "definition": self.manifest["baselineDefinition"]}
        candidate = self.manifest["candidate"]
        mutant_subject = {
            "kind": "mutant", "baselineDefinition": self.manifest["baselineDefinition"], "candidateId": candidate["candidateId"],
            "operator": key("mutation-operator", operator["operatorDigest"]), "patch": candidate["patch"],
            "mutantId": candidate["mutantId"], "mutantDefinition": candidate["mutantDefinition"],
        }
        baseline_rows = []
        mutant_rows = []
        for index, test in enumerate(self.manifest["tests"], start=1):
            base_key = execution_key(self.manifest, test, baseline_subject)
            mutant_key = execution_key(self.manifest, test, mutant_subject)
            baseline_rows.append({"slotId": f"baseline-execution-t{index}", "testId": test["testId"], "phase": "baseline", "recordKind": "execution-attempt", "keyDigest": base_key["keyDigest"]})
            mutant_rows.append({"slotId": f"mutant-execution-t{index}", "testId": test["testId"], "phase": "mutant", "recordKind": "execution-attempt", "keyDigest": mutant_key["keyDigest"]})
            for slot_ordinal, declaration_key in enumerate(test["oracleDeclarations"]):
                declaration = self.resolve(declaration_key)
                baseline_operand = self.operand_for(declaration_key, "baseline")
                mutant_operand = self.operand_for(declaration_key, "mutant")
                gate_key = oracle_key(declaration, [{"side": "baseline", "value": key("oracle-operand", baseline_operand["operandId"])}], "baseline-admission")
                comparison_key = oracle_key(declaration, [{"side": "baseline", "value": key("oracle-operand", baseline_operand["operandId"])}, {"side": "mutant", "value": key("oracle-operand", mutant_operand["operandId"])}], "baseline-mutant-comparison")
                baseline_rows.append({"slotId": f"baseline-gate-t{index}-o{slot_ordinal}", "testId": test["testId"], "phase": "baseline", "recordKind": "oracle-evaluation", "keyDigest": gate_key["keyDigest"]})
                mutant_rows.append({"slotId": f"mutant-comparison-t{index}-o{slot_ordinal}", "testId": test["testId"], "phase": "mutant", "recordKind": "oracle-evaluation", "keyDigest": comparison_key["keyDigest"]})
        return baseline_rows + mutant_rows

    def validate_conflicts(self, values: list[dict[str, Any]]) -> None:
        by_key: dict[str, str] = {}
        for record in values:
            semantic = canonical(without(record, "recordId"))
            previous = by_key.setdefault(record["keyDigest"], semantic)
            self.ok(previous == semantic, "BAG-14 conflicting validated terminal/output/completion/provenance for one key was not quarantined")

    def validate_invocation(self, value: dict[str, Any]) -> None:
        self.ok(value["campaignInvocationId"] == digest("k-in-k/campaign-invocation/v1", without(value, "campaignInvocationId")), "BAG-14 campaign invocation identity omits schedule/plan")
        self.ok(value["manifest"] == key("cache-campaign-manifest", self.manifest["manifestId"]), "BAG-14 invocation selects another manifest")
        self.resolve(value["operator"])
        self.ok(value["requestedPlan"] == self.expected_plan(), "BAG-14 requested plan is not the exact manifest-derived baseline-gate/mutant order")
        slot_ids = [item["slotId"] for item in value["requestedPlan"]]
        self.ok(len(slot_ids) == len(set(slot_ids)), "BAG-14 requested plan duplicates a slot ID")
        for slot in value["requestedPlan"]:
            candidates = [record for record in self.records.values() if record["keyDigest"] == slot["keyDigest"] and record["kind"] == slot["recordKind"]]
            self.ok(candidates, "BAG-14 requested plan key has no finite conformance record")

    def derive_semantic_report(self, invocation: dict[str, Any], selected: list[dict[str, str]]) -> dict[str, Any]:
        plan = invocation["requestedPlan"]
        self.ok([item["slotId"] for item in selected] == [item["slotId"] for item in plan[:len(selected)]], "BAG-14 selected records do not map explicitly to the plan prefix")
        for mapping, slot in zip(selected, plan):
            record = self.records.get(mapping["recordId"])
            self.ok(record is not None and record["keyDigest"] == slot["keyDigest"] and record["kind"] == slot["recordKind"] and record["reuseClass"] != "not-reusable", "BAG-14 report selected an inexact/nonreusable record")
        derived_statuses: dict[str, str] = {}
        selected_by_slot = {item["slotId"]: self.records[item["recordId"]] for item in selected}
        for slot in plan:
            record = selected_by_slot.get(slot["slotId"])
            if record is None:
                derived_statuses[slot["slotId"]] = "skipped"
            elif slot["recordKind"] == "execution-attempt":
                terminal_kind = record["terminalRecord"]["kind"]
                if terminal_kind in {"normal", "stuck", "semantic-crash"}:
                    derived_statuses[slot["slotId"]] = "executed"
                elif terminal_kind == "bounded-stop":
                    derived_statuses[slot["slotId"]] = "timeout" if record["terminalRecord"]["classification"] == "time-limit" else "unknown"
                else:
                    derived_statuses[slot["slotId"]] = "error"
            elif record["terminalRecord"]["kind"] == "baseline-gate":
                gate = self.resolve(record["terminalRecord"]["result"])
                derived_statuses[slot["slotId"]] = "accepted" if gate["status"] == "accepted" else "error"
            elif record["terminalRecord"]["kind"] == "comparison":
                comparison = self.resolve(record["terminalRecord"]["result"])
                derived_statuses[slot["slotId"]] = {"distinguish": "kill", "agree": "agree", "incomparable": "error"}[comparison["outcome"]]
            elif record["terminalRecord"]["kind"] == "bounded-unknown":
                derived_statuses[slot["slotId"]] = "unknown"
            else:
                derived_statuses[slot["slotId"]] = "error"
        baseline_gate_slots = [item["slotId"] for item in plan if item["phase"] == "baseline" and item["recordKind"] == "oracle-evaluation"]
        self.ok(all(derived_statuses[slot] == "accepted" and slot in {item["slotId"] for item in selected} for slot in baseline_gate_slots), "BAG-14 report lacks a selected accepted baseline gate")
        kills = [index for index, item in enumerate(plan) if derived_statuses[item["slotId"]] == "kill"]
        self.ok(kills, "BAG-14 complete positive report has no derived kill")
        expected_prefix = len(plan) if invocation["scheduleMode"] == "full" else kills[0] + 1
        self.ok(len(selected) == expected_prefix, "BAG-14 first-kill/full record coverage is incomplete")
        expected_suffix = [item["slotId"] for item in plan[expected_prefix:]]
        self.ok(all(derived_statuses[item] == "skipped" for item in expected_suffix), "BAG-14 skipped suffix has fabricated child evidence")
        excluded = {
            name: sum(status == name for status in derived_statuses.values())
            for name in ("timeout", "unknown", "error")
        }
        report = {
            "schemaVersion": 1,
            "reportId": "0" * 64,
            "campaignInvocation": key("cache-campaign-invocation", invocation["campaignInvocationId"]),
            "scheduleMode": invocation["scheduleMode"],
            "selectedRecords": deepcopy(selected),
            "testStatuses": [{"slotId": item["slotId"], "status": derived_statuses[item["slotId"]]} for item in plan],
            "scheduledButUnexecuted": expected_suffix,
            "exclusions": excluded,
            "score": {"killed": 1, "survived": 0, "denominator": 1, "ratio": {"numerator": 1, "denominator": 1}},
            "campaignStatus": "complete",
        }
        report["reportId"] = digest("k-in-k/mutation-report/v1", without(report, "reportId"))
        return report

    def validate_report(self, value: dict[str, Any]) -> None:
        self.ok(value["reportId"] == digest("k-in-k/mutation-report/v1", without(value, "reportId")), "BAG-14 report identity drift")
        invocation = self.resolve(value["campaignInvocation"])
        self.ok(value["scheduleMode"] == invocation["scheduleMode"], "BAG-14 report/invocation schedule drift")
        expected = self.derive_semantic_report(invocation, value["selectedRecords"])
        self.ok(value == expected, "BAG-14 report statuses/kill/score/suffix were not derived from exact selected records")

    def expect_rejection(self, check: Callable[[], None], message: str) -> None:
        try:
            check()
        except (AssertionError, KeyError, ValueError, TypeError):
            self.ok(True, message)
        else:
            raise AssertionError(message)

    def schema_rejection(self, value: dict[str, Any], message: str) -> None:
        self.api["expect_schema_rejection"](value, "cache-semantics.schema.json", message)

    def adversary_probes(self) -> dict[str, Callable[[], None]]:
        records = list(self.records.values())
        execution = next(item for item in records if item["kind"] == "execution-attempt" and item["terminalRecord"]["kind"] == "normal")
        mutant_execution = next(item for item in records if item["kind"] == "execution-attempt" and item["key"]["subject"]["kind"] == "mutant" and item["terminalRecord"]["kind"] in {"normal", "stuck"})
        comparison = next(item for item in records if item["kind"] == "oracle-evaluation" and item["terminalRecord"]["kind"] == "comparison")
        bounded = next(item for item in records if item["terminalRecord"]["kind"] == "bounded-stop")
        diagnostic = next(item for item in records if item["terminalRecord"]["kind"] == "diagnostic-only")
        first = next(value for value in self.reports.values() if value["scheduleMode"] == "first-kill")
        full = next(value for value in self.reports.values() if value["scheduleMode"] == "full")
        first_invocation = self.resolve(first["campaignInvocation"])

        def refreshed_record(record: dict[str, Any]) -> None:
            record["recordId"] = digest("k-in-k/cache-record/v1", without(record, "recordId"))

        def refreshed_execution_key(record: dict[str, Any]) -> None:
            record["key"]["keyDigest"] = digest(DOMAINS["execution-attempt"], without(record["key"], "keyDigest"))
            record["keyDigest"] = record["key"]["keyDigest"]
            refreshed_record(record)

        def semantic_record_mutation(mutator: Callable[[dict[str, Any]], None], *, base: dict[str, Any] = mutant_execution) -> None:
            bad = deepcopy(base)
            mutator(bad)
            refreshed_execution_key(bad)
            self.expect_rejection(lambda: self.validate_record(bad), "refreshed semantic cache drift survived")

        def bad_report(mutator: Callable[[dict[str, Any]], None], base: dict[str, Any] = first) -> None:
            bad = deepcopy(base); mutator(bad); bad["reportId"] = digest("k-in-k/mutation-report/v1", without(bad, "reportId"))
            self.expect_rejection(lambda: self.validate_report(bad), "refreshed invalid cache report survived")

        probes: dict[str, Callable[[], None]] = {}
        probes["schedule-record-as-attempt"] = lambda: self.expect_rejection(lambda: self.validate_record(first), "schedule report was accepted as a raw cache record")
        probes["first-kill-as-full"] = lambda: bad_report(lambda bad: bad.update({"scheduleMode": "full"}))
        probes["fabricated-skipped-record"] = lambda: bad_report(lambda bad: bad["selectedRecords"].append(deepcopy(full["selectedRecords"][len(first["selectedRecords"])])))
        probes["subject-reversal"] = lambda: semantic_record_mutation(lambda bad: bad["key"].update({"subject": {"kind": "baseline", "definition": self.manifest["baselineDefinition"]}}))
        probes["candidate-id-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["subject"].update({"candidateId": "f" * 64}))
        probes["patch-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["subject"].update({"patch": key("patch", "f" * 64)}))
        probes["mutant-definition-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["subject"].update({"mutantDefinition": key("mutant-definition", "f" * 64)}))
        probes["test-invocation-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"].update({"testInvocationDigest": "f" * 64}))
        probes["profile-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"].update({"executionProfileDigest": "f" * 64}))
        probes["bounds-drift"] = lambda: self._bounded_drift(bounded)
        probes["declaration-drift"] = lambda: self._oracle_drift(comparison, lambda bad: bad["key"].update({"declaration": key("oracle-declaration", "f" * 64)}))
        probes["missing-produced-artifact"] = lambda: self._record_drift(execution, lambda bad: bad["producedArtifacts"][0].update({"digest": "f" * 64}))
        probes["partial-output-complete"] = lambda: self._record_drift(execution, lambda bad: bad["producedArtifacts"].pop())
        probes["diagnostic-reused-as-agreement"] = lambda: self._record_drift(diagnostic, lambda bad: bad.update({"reuseClass": "semantic-result"}))
        probes["bounded-under-different-bounds"] = lambda: self._bounded_drift(bounded)
        probes["conflicting-same-key"] = lambda: self._conflict(execution)
        probes["refreshed-id-concealment"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["subject"].update({"mutantId": "f" * 64}))
        for name, field in (("output-in-attempt-key", "output"), ("status-in-attempt-key", "status"), ("schedule-in-raw-key", "scheduleMode"), ("hit-in-raw-key", "cacheHit"), ("suite-level-boolean-hit", "suiteCacheHit")):
            probes[name] = lambda field=field, name=name: self._open_key(execution, field, name)
        probes["schedule-omitted-invocation"] = lambda: self._missing_schema(first_invocation, "scheduleMode")
        probes["schedule-omitted-report"] = lambda: self._missing_schema(first, "scheduleMode")
        probes["parser-drift"] = lambda: self._manifest_test_drift("parser", key("parser", "f" * 64))
        probes["start-symbol-drift"] = lambda: self._manifest_test_drift("startSymbol", "Other")
        probes["options-drift"] = lambda: self._manifest_test_drift("options", key("options", "f" * 64))
        probes["lowering-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"].update({"loweringProfileDigest": "f" * 64}))
        probes["solver-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"].update({"solverProfileDigest": "f" * 64}))
        probes["isolation-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["isolationPolicy"].update({"isolationPolicyDigest": "f" * 64}))
        probes["observer-order-drift"] = lambda: self._attempt_kind_schema(execution, {"kind": "observed-exhaustive", "observationInputs": [key("event-trace", "f" * 64), key("event-trace", "e" * 64)]})
        probes["attempt-kind-drift"] = lambda: self._attempt_kind_schema(execution, {"kind": "observed-exhaustive", "observationInputs": [key("event-trace", "f" * 64)]})
        probes["query-coupling-drift"] = lambda: self._attempt_kind_schema(execution, {"kind": "query-coupled", "observationInputs": [key("event-trace", "f" * 64)], "patternSource": key("pattern-source", "f" * 64), "patternPlan": key("pattern-plan", "f" * 64), "patternQuery": key("pattern-query", "f" * 64), "searchPolicy": "exhaustive"})
        probes["search-policy-drift"] = lambda: self._bad_search_policy(execution)
        probes["operation-version-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["operation"].update({"operationVersion": 99}))
        probes["operation-id-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["operation"].update({"operationId": "unregistered-execution"}))
        probes["adapter-version-drift"] = lambda: semantic_record_mutation(lambda bad: bad["key"]["operation"].update({"adapterVersion": 99}))
        probes["oracle-operand-order"] = lambda: self._oracle_drift(comparison, lambda bad: bad["key"]["semanticInputs"].reverse())
        probes["baseline-policy-drift"] = lambda: self._declaration_reference_drift(comparison)
        probes["evaluator-drift"] = lambda: self._oracle_drift(comparison, lambda bad: bad["key"]["evaluator"].update({"evaluatorVersion": 99}))
        probes["evaluator-id-drift"] = lambda: self._oracle_drift(comparison, lambda bad: bad["key"]["evaluator"].update({"evaluatorId": "unregistered-evaluator"}))
        probes["wrong-resolver-material"] = lambda: self._wrong_resolver()
        probes["boolean-completion"] = lambda: self._boolean_completion(execution)
        probes["missing-baseline-gate"] = lambda: bad_report(lambda bad: bad["selectedRecords"].pop(next(index for index, item in enumerate(bad["selectedRecords"]) if item["slotId"].startswith("baseline-gate-"))), full)
        probes["cached-fold-difference"] = lambda: self._fold_drift()
        probes["query-kind-reuse"] = lambda: self._attempt_kind_schema(execution, {"kind": "ordinary", "patternQuery": key("pattern-query", "f" * 64)})
        probes["duplicate-json-key"] = lambda: self.expect_rejection(lambda: json.loads('{"a":1,"a":2}', object_pairs_hook=self.unique_object), "duplicate JSON cache material key survived")
        probes["nonportable-json-value"] = lambda: self.expect_rejection(lambda: canonical({"value": float("nan")}), "nonportable cache JSON value survived")
        probes["terminal-output-substitution"] = lambda: self._terminal_output_substitution(execution)
        probes["oracle-output-substitution"] = lambda: self._oracle_output_substitution(comparison)
        probes["requested-plan-reorder"] = lambda: self._plan_reorder(first_invocation)
        probes["status-self-assertion"] = lambda: bad_report(lambda bad: bad["testStatuses"][5].update({"status": "agree"}))
        probes["operator-template-operation-drift"] = lambda: self._operator_template_drift()
        probes["operator-selected-site-drift"] = lambda: self._operator_selected_site_drift()
        probes["same-key-output-conflict"] = lambda: self._output_conflict(execution)
        probes["same-key-provenance-conflict"] = lambda: self._provenance_conflict(execution)
        probes["definition-semantic-id-drift"] = lambda: self._definition_semantic_drift()
        probes["selector-semantic-id-drift"] = lambda: self._selector_semantic_drift()
        probes["operator-semantic-id-drift"] = lambda: self._operator_semantic_drift()
        probes["edit-semantic-id-drift"] = lambda: self._edit_semantic_drift()
        probes["patch-semantic-id-drift"] = lambda: self._patch_semantic_drift()
        probes["mutant-materialization-drift"] = lambda: self._mutant_materialization_drift()
        probes["terminal-semantic-id-drift"] = lambda: self._terminal_semantic_drift()
        probes["trace-semantic-id-drift"] = lambda: self._trace_semantic_drift()
        probes["declaration-semantic-id-drift"] = lambda: self._declaration_semantic_drift()
        probes["operand-semantic-id-drift"] = lambda: self._operand_semantic_drift()
        probes["gate-outcome-drift"] = lambda: self._gate_outcome_drift()
        probes["comparison-outcome-drift"] = lambda: self._comparison_outcome_drift()
        probes["incoherent-query-triple"] = lambda: self._incoherent_query_triple()
        probes["declaration-slot-reorder"] = lambda: self._declaration_slot_drift("reorder")
        probes["declaration-slot-removal"] = lambda: self._declaration_slot_drift("remove")
        probes["crash-profile-drift"] = lambda: self._crash_asset_drift("profile")
        probes["crash-terminal-drift"] = lambda: self._crash_asset_drift("terminal")
        probes["crash-side-role-drift"] = lambda: self._crash_side_role_drift()
        probes["crash-producer-trace-drift"] = lambda: self._crash_trace_drift()
        probes["same-key-normal-crash-result-substitution"] = lambda: self._same_key_crash_result_substitution()
        probes["fabricated-query-test-slot"] = lambda: self._fabricated_query_slot()
        probes["swapped-crash-comparison"] = lambda: self._swapped_crash_comparison()
        probes["mutant-crash-baseline-gate"] = lambda: self._mutant_crash_gate()
        probes["normal-only-crash-policy-drift"] = lambda: self._normal_only_crash_policy()
        probes["crash-policy-drift"] = lambda: self._crash_policy_drift()
        probes["catalog-key-self-id-mismatch"] = lambda: self._catalog_key_mismatch()
        probes["same-key-altered-execution-terminal-trace-row"] = lambda: self._same_key_execution_row_substitution()
        return probes

    def _incoherent_query_triple(self) -> None:
        bad = deepcopy(self.vector["queryCoupledRegression"])
        splice = read_json(self.fixtures / "pattern-query-single-write.json")
        bad["executionKey"]["attemptKind"]["patternPlan"] = splice["patternPlan"]
        bad["executionKey"]["keyDigest"] = digest(DOMAINS["execution-attempt"], without(bad["executionKey"], "keyDigest"))
        self.expect_rejection(lambda: self.validate_query_coupled_regression(bad), "ACCEPTED_INCOHERENT_QUERY_TRIPLE")

    def _declaration_slot_drift(self, mode: str) -> None:
        bad = deepcopy(self.manifest)
        if mode == "reorder":
            bad["tests"][0]["oracleDeclarations"].reverse()
        else:
            bad["tests"][0]["oracleDeclarations"].pop()
        bad["manifestId"] = digest("k-in-k/cache-campaign-manifest/v1", without(bad, "manifestId"))
        if mode == "reorder":
            self.expect_rejection(lambda: self.validate_manifest(bad), "refreshed declaration-slot order drift survived")
        else:
            invocation = deepcopy(next(iter(self.invocations.values())))
            invocation["manifest"] = key("cache-campaign-manifest", bad["manifestId"])
            invocation["campaignInvocationId"] = digest("k-in-k/campaign-invocation/v1", without(invocation, "campaignInvocationId"))
            self.expect_rejection(lambda: self.validate_invocation(invocation), "refreshed declaration-slot removal survived invocation/report binding")

    def _crash_asset_drift(self, mode: str) -> None:
        identity, bad = next((identity, deepcopy(value)) for (role, identity), value in self.assets.items() if role == "semantic-crash")
        if mode == "profile":
            bad["executionProfileDigest"] = "f" * 64
        else:
            bad["terminalState"] = next(key(role, candidate) for (role, candidate) in self.assets if role == "terminal-state" and candidate != bad["terminalState"]["digest"])
        self.expect_rejection(lambda: self.validate_crash_asset(identity, bad), "semantic-crash profile/terminal drift survived")

    def _crash_side_role_drift(self) -> None:
        bad = deepcopy(self.vector["crashOracleEvidence"][0]["key"])
        bad["semanticInputs"][0]["value"]["role"] = "oracle-operand"
        bad["keyDigest"] = digest(DOMAINS["oracle-evaluation"], without(bad, "keyDigest"))
        self.expect_rejection(lambda: self.validate_oracle_key(bad), "semantic-crash side role drift survived")

    def _crash_trace_drift(self) -> None:
        identity, bad = next((identity, deepcopy(value)) for (role, identity), value in self.assets.items() if role == "event-trace" and value["executionTerminal"]["kind"] == "semantic-crash")
        bad["testId"] = "another-test"
        self.expect_rejection(lambda: self.validate_trace_asset(identity, bad), "semantic-crash producer trace drift survived")

    def _same_key_crash_result_substitution(self) -> None:
        source = next(record for record in self.records.values() if record["kind"] == "oracle-evaluation" and record["key"]["evaluationKind"] == "baseline-mutant-comparison" and all(item["value"]["role"] == "oracle-operand" for item in record["key"]["semanticInputs"]))
        crash_result = self.vector["crashOracleEvidence"][1]["result"]
        bad = deepcopy(source)
        bad["terminalRecord"] = {"kind": "comparison", "result": deepcopy(crash_result)}
        bad["producedArtifacts"] = [deepcopy(crash_result)]
        bad["productionEvidence"]["outputKeys"] = [deepcopy(crash_result)]
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        registry = self.vector["finiteVectorRegistry"][bad["productionEvidence"]["vectorId"]]["rows"]
        index = next(index for index, row in enumerate(registry) if row["inputs"] == {"keyDigest": bad["keyDigest"]})
        original = deepcopy(registry[index])
        registry[index]["terminalRecord"] = deepcopy(bad["terminalRecord"])
        registry[index]["outputKeys"] = deepcopy(bad["producedArtifacts"])
        try:
            self.expect_rejection(lambda: self.validate_record(bad), "same-key normal-input key authorized substituted crash result after finite-row refresh")
        finally:
            registry[index] = original

    def _same_key_execution_row_substitution(self) -> None:
        source = next(record for record in self.records.values() if record["kind"] == "execution-attempt" and record["key"]["subject"]["kind"] == "mutant" and record["terminalRecord"]["kind"] == "stuck")
        replacement = next(record for record in self.records.values() if record["kind"] == "execution-attempt" and record["key"]["subject"]["kind"] == "mutant" and record["terminalRecord"]["kind"] == "normal")
        bad = deepcopy(source)
        bad["terminalRecord"] = deepcopy(replacement["terminalRecord"])
        bad["producedArtifacts"] = deepcopy(replacement["producedArtifacts"])
        bad["productionEvidence"]["outputKeys"] = deepcopy(bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        registry = self.vector["finiteVectorRegistry"][bad["productionEvidence"]["vectorId"]]["rows"]
        index = next(index for index, row in enumerate(registry) if row["inputs"] == {"keyDigest": bad["keyDigest"]})
        original = deepcopy(registry[index])
        registry[index]["terminalRecord"] = deepcopy(bad["terminalRecord"])
        registry[index]["outputKeys"] = deepcopy(bad["producedArtifacts"])
        try:
            self.expect_rejection(lambda: self.validate_record(bad), "same execution key authorized altered terminal/output/trace after record and finite-row refresh")
        finally:
            registry[index] = original

    def _fabricated_query_slot(self) -> None:
        bad = deepcopy(self.vector["queryCoupledRegression"])
        bad["slotOrdinal"] = 13
        bad["selectedDeclaration"] = deepcopy(read_json(self.fixtures / "mutation-manifest.json")["tests"][0]["oracleDeclarations"][13])
        self.expect_rejection(lambda: self.validate_query_coupled_regression(bad), "fabricated/refreshed active query slot survived")

    def _swapped_crash_comparison(self) -> None:
        source = self.resolve(self.vector["crashOracleEvidence"][1]["result"])
        bad = deepcopy(source)
        bad["sides"].reverse()
        for side, name in zip(bad["sides"], ("baseline", "mutant")):
            side["side"] = name
        bad["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(bad, "comparisonId"))
        self.expect_rejection(lambda: self.validate_comparison_asset(bad), "swapped crash keys survived refreshed comparison identity")

    def _mutant_crash_gate(self) -> None:
        source = self.resolve(self.vector["crashOracleEvidence"][0]["result"])
        mutant_crash = self.vector["crashOracleEvidence"][1]["key"]["semanticInputs"][1]["value"]
        bad = deepcopy(source)
        bad["actualSide"] = semantic_side("baseline", mutant_crash)
        bad["gateResultId"] = digest("k-in-k/baseline-oracle-gate-result/v1", without(bad, "gateResultId"))
        self.expect_rejection(lambda: self.validate_gate_asset(bad), "mutant crash was accepted as baseline gate provenance")

    def _normal_only_crash_policy(self) -> None:
        bad = deepcopy(self.vector["crashOracleEvidence"][0]["key"])
        bad["declaration"] = deepcopy(self.manifest["tests"][0]["oracleDeclarations"][0])
        bad["keyDigest"] = digest(DOMAINS["oracle-evaluation"], without(bad, "keyDigest"))
        self.expect_rejection(lambda: self.derive_oracle_result(bad), "normal-only declaration admitted crash-positive evidence")

    def _crash_policy_drift(self) -> None:
        evidence = self.vector["crashOracleEvidence"][1]
        declaration_key = evidence["key"]["declaration"]
        identity = (declaration_key["role"], declaration_key["digest"])
        original = self.assets[identity]
        bad_declaration = deepcopy(original)
        bad_declaration["crashPolicy"] = "semantic-crash-incomparable"
        self.assets[identity] = bad_declaration
        try:
            self.expect_rejection(lambda: self.derive_oracle_result(evidence["key"]), "crash-policy drift survived exact oracle derivation")
        finally:
            self.assets[identity] = original

    def _catalog_key_mismatch(self) -> None:
        (role, identity), source = next(((role, identity), value) for (role, identity), value in self.assets.items() if role == "cache-record")
        bad = deepcopy(source)
        bad["recordId"] = digest("k-in-k/cache-record/v1", {**without(bad, "recordId"), "reuseClass": "diagnostic-only"})
        self.expect_rejection(lambda: self.validate_catalog_identity(role, identity, bad), "refreshed embedded cache self ID survived catalog-key mismatch")

    def _record_drift(self, source: dict[str, Any], mutate: Callable[[dict[str, Any]], None]) -> None:
        bad = deepcopy(source); mutate(bad); bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_record(bad), "invalid completion/output record survived")

    def _oracle_drift(self, source: dict[str, Any], mutate: Callable[[dict[str, Any]], None]) -> None:
        bad = deepcopy(source); mutate(bad)
        bad["key"]["keyDigest"] = digest(DOMAINS["oracle-evaluation"], without(bad["key"], "keyDigest")); bad["keyDigest"] = bad["key"]["keyDigest"]
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_record(bad), "oracle key drift survived refreshed identities")

    def _bounded_drift(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source); bad["terminalRecord"]["boundsDigest"] = "f" * 64
        bad["productionEvidence"] = finite_production(bad["productionEvidence"]["vectorId"], bad["key"], bad["terminalRecord"], bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_record(bad), "bounded record was reused under different bounds")

    def _conflict(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source); bad["terminalRecord"]["kind"] = "stuck"
        bad["productionEvidence"] = finite_production(bad["productionEvidence"]["vectorId"], bad["key"], bad["terminalRecord"], bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_conflicts([source, bad]), "same-key conflict was silently selected")

    def _output_conflict(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source)
        replacement = next(
            key(role, identity)
            for (role, identity) in self.assets
            if role == "event-trace" and key(role, identity) != bad["producedArtifacts"][1]
        )
        bad["producedArtifacts"][1] = replacement
        bad["productionEvidence"]["outputKeys"] = deepcopy(bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_conflicts([source, bad]), "same-key output conflict was not quarantined")

    def _provenance_conflict(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source)
        bad["productionEvidence"]["vectorId"] = "alternate-finite-producer"
        bad["productionEvidence"]["inputDigest"] = "f" * 64
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_conflicts([source, bad]), "same-key producer-provenance conflict was not quarantined")

    def _open_key(self, source: dict[str, Any], field: str, message: str) -> None:
        bad = deepcopy(source["key"]); bad[field] = True
        self.schema_rejection(bad, f"{message} survived closed raw key schema")

    def _missing_schema(self, source: dict[str, Any], field: str) -> None:
        bad = deepcopy(source); bad.pop(field)
        self.schema_rejection(bad, f"missing {field} survived schema")

    def _manifest_test_drift(self, field: str, value: Any) -> None:
        bad = deepcopy(self.manifest); bad["tests"][0][field] = value; bad["manifestId"] = digest("k-in-k/cache-campaign-manifest/v1", without(bad, "manifestId"))
        self.expect_rejection(lambda: self.validate_manifest(bad), f"manifest {field} drift survived refreshed manifest identity")

    def _attempt_kind_schema(self, source: dict[str, Any], attempt_kind: dict[str, Any]) -> None:
        bad = deepcopy(source["key"]); bad["attemptKind"] = attempt_kind
        bad["keyDigest"] = digest(DOMAINS["execution-attempt"], without(bad, "keyDigest"))
        self.expect_rejection(lambda: self.validate_execution_key(bad), "attempt/query/observer coupling drift survived")

    def _bad_search_policy(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source["key"]); bad["attemptKind"] = {"kind": "query-coupled", "observationInputs": [key("event-trace", "f" * 64)], "patternSource": key("pattern-source", "f" * 64), "patternPlan": key("pattern-plan", "f" * 64), "patternQuery": key("pattern-query", "f" * 64), "searchPolicy": "all-witnesses"}
        self.schema_rejection(bad, "non-BAG-11 search vocabulary survived")

    def _declaration_reference_drift(self, source: dict[str, Any]) -> None:
        declaration = deepcopy(self.resolve(source["key"]["declaration"])); declaration["baselineTerminalPolicy"] = "normal-or-stuck"
        declaration["declarationId"] = digest("k-in-k/oracle-declaration/v1", without(declaration, "declarationId"))
        self.expect_rejection(lambda: self.ok(declaration["declarationId"] == source["key"]["declaration"]["digest"], "oracle declaration policy changed without changing key"), "baseline policy drift survived oracle key")

    def _wrong_resolver(self) -> None:
        entry = deepcopy(next(iter(self.catalog["entries"]))); entry.update({"availability": "external-required", "resolverId": "rust-artifact-store-v1", "logicalPath": "artifact://cache/missing"})
        self.expect_rejection(lambda: self.ok(entry["availability"] == "bundled" and entry["resolverId"] == "repo-v1", "wrong resolver asserted repo material"), "referential-only cache material survived repo lookup")

    def _boolean_completion(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source); bad["completion"] = {"complete": True}
        self.schema_rejection(bad, "boolean completion survived typed positive evidence schema")

    def _fold_drift(self) -> None:
        fold = deepcopy(self.vector["scheduleFolds"][0])
        fold["materializations"][0]["recordSources"].reverse()
        invocation = next(value for value in self.invocations.values() if value["scheduleMode"] == fold["scheduleMode"])
        mappings = [{"slotId": item["slotId"], "recordId": item["recordId"]} for item in fold["materializations"][0]["recordSources"]]
        self.expect_rejection(lambda: self.derive_semantic_report(invocation, mappings), "cached/uncached fold semantic difference survived")

    def _terminal_output_substitution(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source)
        other = next(key(role, identity) for (role, identity) in self.assets if role == "terminal-state" and identity != bad["terminalRecord"]["terminal"]["digest"])
        bad["producedArtifacts"][0] = other
        bad["productionEvidence"] = finite_production(bad["productionEvidence"]["vectorId"], bad["key"], bad["terminalRecord"], bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_record(bad), "same-role terminal output substitution survived refreshed record evidence")

    def _oracle_output_substitution(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source)
        other = next(key(role, identity) for (role, identity) in self.assets if role == "oracle-comparison-result" and identity != bad["terminalRecord"]["result"]["digest"])
        bad["producedArtifacts"] = [other]
        bad["productionEvidence"] = finite_production(bad["productionEvidence"]["vectorId"], bad["key"], bad["terminalRecord"], bad["producedArtifacts"])
        bad["recordId"] = digest("k-in-k/cache-record/v1", without(bad, "recordId"))
        self.expect_rejection(lambda: self.validate_record(bad), "same-role oracle output substitution survived refreshed record evidence")

    def _plan_reorder(self, source: dict[str, Any]) -> None:
        bad = deepcopy(source); bad["requestedPlan"][0], bad["requestedPlan"][1] = bad["requestedPlan"][1], bad["requestedPlan"][0]
        bad["campaignInvocationId"] = digest("k-in-k/campaign-invocation/v1", without(bad, "campaignInvocationId"))
        self.expect_rejection(lambda: self.validate_invocation(bad), "refreshed reordered request plan survived")

    def _operator_template_drift(self) -> None:
        operator = self.only("mutation-operator")
        patch = self.resolve(self.manifest["candidate"]["patch"])
        self.expect_rejection(lambda: self.ok([edit["operation"] for edit in patch["edits"]] == ["replace-term" for _ in operator["patchTemplateRoles"]], "mismatched template authorized cache patch"), "operator/template operation mismatch survived")

    def _operator_selected_site_drift(self) -> None:
        operator = self.only("mutation-operator")
        selector = deepcopy(self.resolve(key("mutation-selector", operator["selectorDigest"])))
        selector["clauses"][0].update({
            "label": "increment",
            "termPath": [{"kind": "field", "name": "body"}, {"kind": "field", "name": "rhs"}, {"kind": "argument", "index": 0}],
            "termSort": "Int",
            "termHeadLabel": "plusOne",
        })
        baseline = self.resolve(self.manifest["baselineDefinition"])
        patch = self.resolve(self.manifest["candidate"]["patch"])
        selected = {lineage for values in self.selected_lineages(baseline, selector).values() for lineage in values}
        self.expect_rejection(lambda: self.ok({edit["targetLineage"] for edit in patch["edits"]} == selected, "another selected site authorized the patch"), "operator/selector/patch site mismatch survived")

    def patch_graph(self) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
        baseline = self.resolve(self.manifest["baselineDefinition"])
        mutant = self.resolve(self.manifest["candidate"]["mutantDefinition"])
        operator = self.only("mutation-operator")
        selector = self.resolve(key("mutation-selector", operator["selectorDigest"]))
        patch = self.resolve(self.manifest["candidate"]["patch"])
        return baseline, mutant, operator, selector, patch

    def _definition_semantic_drift(self) -> None:
        baseline = deepcopy(self.resolve(self.manifest["baselineDefinition"]))
        baseline["family"]["familyName"] = "drifted-family"
        self.expect_rejection(lambda: self.validate_definition(baseline, "adversarial definition"), "definition semantic identity drift survived")

    def _selector_semantic_drift(self) -> None:
        baseline, mutant, operator, selector, patch = self.patch_graph()
        bad = deepcopy(selector); bad["clauses"][0]["termHeadLabel"] = "choose"
        self.expect_rejection(lambda: self.validate_patch_materialization(baseline, mutant, operator, bad, patch), "selector semantic identity drift survived")

    def _operator_semantic_drift(self) -> None:
        baseline, mutant, operator, selector, patch = self.patch_graph()
        bad = deepcopy(operator); bad["rationale"] = "drifted authority"
        self.expect_rejection(lambda: self.validate_patch_materialization(baseline, mutant, bad, selector, patch), "operator semantic identity drift survived")

    def _edit_semantic_drift(self) -> None:
        baseline, mutant, operator, selector, patch = self.patch_graph()
        bad = deepcopy(patch); bad["edits"][0]["expectedContent"] = "f" * 64
        self.expect_rejection(lambda: self.validate_patch_materialization(baseline, mutant, operator, selector, bad), "edit semantic identity drift survived")

    def _patch_semantic_drift(self) -> None:
        baseline, mutant, operator, selector, patch = self.patch_graph()
        bad = deepcopy(patch); bad["patchId"] = "f" * 64
        self.expect_rejection(lambda: self.validate_patch_materialization(baseline, mutant, operator, selector, bad), "patch semantic identity drift survived")

    def _mutant_materialization_drift(self) -> None:
        baseline, mutant, operator, selector, patch = self.patch_graph()
        bad = deepcopy(mutant)
        target = next(sentence for module in bad["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == patch["edits"][0]["targetLineage"])
        target["value"]["attributes"][-1]["value"] = {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "token", "text": "true"}}
        bad = refreshed_definition(bad)
        self.expect_rejection(lambda: self.validate_patch_materialization(baseline, bad, operator, selector, patch), "patch-to-mutant materialization drift survived")

    def _terminal_semantic_drift(self) -> None:
        terminal = deepcopy(next(value for (role, _), value in self.assets.items() if role == "terminal-state"))
        terminal["value"]["node"]["text"] = "drifted-terminal"
        self.expect_rejection(lambda: self.validate_terminal_asset(terminal), "terminal semantic identity drift survived")

    def _trace_semantic_drift(self) -> None:
        identity, trace = next((identity, deepcopy(value)) for (role, identity), value in self.assets.items() if role == "event-trace")
        trace["pathKey"] = "drifted/path"
        self.expect_rejection(lambda: self.validate_trace_asset(identity, trace), "trace semantic identity drift survived")

    def _declaration_semantic_drift(self) -> None:
        declaration = deepcopy(next(value for (role, _), value in self.assets.items() if role == "oracle-declaration"))
        declaration["slotId"] = "drifted-slot"
        declaration["declarationId"] = digest("k-in-k/oracle-declaration/v1", without(declaration, "declarationId"))
        self.expect_rejection(lambda: self.validate_declaration_asset(declaration), "refreshed declaration semantic drift survived")

    def _operand_semantic_drift(self) -> None:
        operand = deepcopy(next(value for (role, _), value in self.assets.items() if role == "oracle-operand"))
        operand["normalizedValue"]["terminalClass"] = "stuck"
        operand["operandId"] = digest("k-in-k/oracle-operand/v1", without(operand, "operandId"))
        self.expect_rejection(lambda: self.validate_operand_asset(operand), "refreshed operand semantic drift survived")

    def _gate_outcome_drift(self) -> None:
        gate = deepcopy(next(value for (role, _), value in self.assets.items() if role == "baseline-oracle-gate-result" and value["status"] == "accepted"))
        gate["status"] = "rejected"
        gate["gateResultId"] = digest("k-in-k/baseline-oracle-gate-result/v1", without(gate, "gateResultId"))
        self.expect_rejection(lambda: self.validate_gate_asset(gate), "refreshed baseline-gate assertion drift survived")

    def _comparison_outcome_drift(self) -> None:
        comparison = deepcopy(next(value for (role, _), value in self.assets.items() if role == "oracle-comparison-result"))
        comparison["outcome"] = "agree" if comparison["outcome"] == "distinguish" else "distinguish"
        comparison["comparisonId"] = digest("k-in-k/oracle-comparison-result/v1", without(comparison, "comparisonId"))
        self.expect_rejection(lambda: self.validate_comparison_asset(comparison), "refreshed comparison outcome drift survived")

    def validate_schedule_folds(self) -> None:
        folds = self.vector["scheduleFolds"]
        self.ok([fold["scheduleMode"] for fold in folds] == ["first-kill", "full"], "BAG-14 schedule folds are missing, duplicated, or reordered")
        reports = {report["scheduleMode"]: report for report in self.reports.values()}
        invocations = {invocation["scheduleMode"]: invocation for invocation in self.invocations.values()}
        for fold in folds:
            materializations = fold["materializations"]
            self.ok([item["cacheState"] for item in materializations] == ["uncached", "partial-hit", "full-hit"], "BAG-14 concrete cache-state folds are missing or reordered")
            rendered = []
            for materialization in materializations:
                sources = materialization["recordSources"]
                self.ok(all(set(item) == {"slotId", "recordId", "source"} and item["source"] in {"executed", "cache-hit"} for item in sources), "BAG-14 schedule fold source is open or invalid")
                source_values = [item["source"] for item in sources]
                if materialization["cacheState"] == "uncached":
                    self.ok(set(source_values) == {"executed"}, "BAG-14 uncached fold contains a cache hit")
                elif materialization["cacheState"] == "partial-hit":
                    self.ok(set(source_values) == {"executed", "cache-hit"}, "BAG-14 partial fold is not an actual mixed materialization")
                else:
                    self.ok(set(source_values) == {"cache-hit"}, "BAG-14 full-hit fold contains execution")
                mappings = [{"slotId": item["slotId"], "recordId": item["recordId"]} for item in sources]
                derived = self.derive_semantic_report(invocations[fold["scheduleMode"]], mappings)
                rendered.append(canonical(derived).encode("utf-8"))
                self.ok(derived == reports[fold["scheduleMode"]], "BAG-14 cache-state fold did not derive the schedule-specific report")
            self.ok(rendered[0] == rendered[1] == rendered[2], "BAG-14 uncached/partial/full semantic report bytes differ")

    def adversaries(self) -> None:
        advertised = [item["probe"] for item in self.vector["adversaries"]]
        probes = self.adversary_probes()
        self.ok(len(advertised) == len(set(advertised)) and set(advertised) == set(probes), "BAG-14 adversary registry is not one-to-one")
        executed = []
        for name in advertised:
            probes[name](); executed.append(name)
        self.ok(executed == advertised and len(executed) == len(probes), "BAG-14 adversary did not execute exactly once")

    def run(self) -> None:
        self.validate_manifest()
        self.validate_semantic_assets()
        self.validate_query_coupled_regression()
        for evidence in self.vector["crashOracleEvidence"]:
            expected_key, expected_value = self.derive_oracle_result(evidence["key"])
            self.ok(evidence["result"] == expected_key and self.resolve(evidence["result"]) == expected_value, "BAG-14 crash gate/comparison positive evidence is not exactly derived")
        self.validate_finite_registry()
        for record in self.records.values():
            self.validate_record(record)
        self.validate_conflicts(list(self.records.values()))
        for invocation in self.invocations.values():
            self.validate_invocation(invocation)
        for report in self.reports.values():
            self.validate_report(report)
        by_schedule = {report["scheduleMode"]: report for report in self.reports.values()}
        prefix_length = len(by_schedule["first-kill"]["selectedRecords"])
        self.ok(by_schedule["first-kill"]["selectedRecords"] == by_schedule["full"]["selectedRecords"][:prefix_length], "BAG-14 reports do not share the exact validated prefix")
        self.ok(not ({item["slotId"] for item in by_schedule["first-kill"]["selectedRecords"]} & set(by_schedule["first-kill"]["scheduledButUnexecuted"])), "BAG-14 first-kill report fabricated skipped suffix records")
        self.validate_schedule_folds()
        policy = read_json(self.fixtures / "mutation-execution-policy.json")
        self.ok(policy["policyId"] == digest("k-in-k/mutation-execution-policy/v1", without(policy, "policyId")) and policy["isolationPolicy"] == self.manifest["isolationPolicy"] and "cacheKey" not in policy, "suite cache key survived mutation policy migration")
        self.adversaries()


def new_official_fixtures(root: Path) -> dict[str, str]:
    fixtures = root / "fixtures"
    result = {"bag14-cache-artifact-catalog.json": "artifact-catalog.schema.json"}
    for path in fixtures.glob("bag14-cache-record-*.json"):
        result[path.name] = "cache-semantics.schema.json"
    for path in fixtures.glob("bag14-campaign-invocation-*.json"):
        result[path.name] = "cache-semantics.schema.json"
    for path in fixtures.glob("bag14-mutation-report-*.json"):
        result[path.name] = "cache-semantics.schema.json"
    result["bag14-cache-campaign-manifest.json"] = "cache-semantics.schema.json"
    for path in fixtures.glob("bag14-oracle-declaration-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("bag14-oracle-operand-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("bag14-baseline-gate-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("bag14-oracle-comparison-*.json"):
        result[path.name] = "oracle-semantics.schema.json"
    for path in fixtures.glob("bag14-terminal-*.json"):
        result[path.name] = "terminal-state.schema.json"
    for path in fixtures.glob("bag14-event-trace-*.json"):
        result[path.name] = "event-trace.schema.json"
    for path in fixtures.glob("bag14-semantic-crash-*.json"):
        result[path.name] = "semantic-crash.schema.json"
    result.update({
        "bag14-definition-baseline.json": "semantic-definition.schema.json",
        "bag14-definition-mutant.json": "semantic-definition.schema.json",
        "bag14-mutation-operator.json": "mutation-operator.schema.json",
        "bag14-patch.json": "patch.schema.json",
        "bag14-compatibility-profile.json": "compatibility-profile.schema.json",
    })
    return result


def verify_package(root: Path, api: dict[str, Any]) -> None:
    CacheVerifier(root, api).run()
