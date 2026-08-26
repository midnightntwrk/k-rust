#!/usr/bin/env python3
"""Zero-backend consistency verifier for the portable K-in-K package."""

from __future__ import annotations

import hashlib
import json
import math
import re
import tempfile
import sys
import unicodedata
from copy import deepcopy
from itertools import product
from pathlib import Path
from typing import Any

from bag12 import new_official_fixtures as bag12_official_fixtures
from bag12 import verify_package as verify_bag12_package
from bag14 import new_official_fixtures as bag14_official_fixtures
from bag14 import verify_package as verify_bag14_package
from bag15 import new_official_fixtures as bag15_official_fixtures
from bag15 import verify_package as verify_bag15_package
from bag16 import new_official_fixtures as bag16_official_fixtures
from bag16 import successor_failure_taxonomy as bag16_successor_failure_taxonomy
from bag16 import verify_package as verify_bag16_package


PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[1]
SCHEMAS = PACKAGE / "schemas"
VECTORS = PACKAGE / "vectors"
FIXTURES = PACKAGE / "fixtures"
CHECKS = 0
OFFICIAL_VALIDATORS: dict[str, Any] = {}
FROZEN_LOWERING_RELATION = {"states": ["lowering-a", "lowering-b"], "edges": [["lowering-a", "lowering-b"], ["lowering-b", "lowering-a"]]}


def ok(condition: bool, message: str) -> None:
    global CHECKS
    if not condition:
        raise AssertionError(message)
    CHECKS += 1


def load(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=unique_object)
    validate_portable_json(value, str(path.relative_to(ROOT)))
    return value


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key {key!r}")
        result[key] = value
    return result


def portable_json_failure(reason: str, where: str) -> None:
    raise AssertionError(f"{reason} at {where}")


def validate_portable_json(value: Any, where: str = "$", active: set[int] | None = None) -> None:
    """Validate the exact, acyclic host-value domain accepted by canonical JSON."""
    if active is None:
        active = set()
    if isinstance(value, float):
        portable_json_failure("floating-point-forbidden", where)
    if type(value) is int:
        if value < -(2**63) or value > 2**63 - 1:
            portable_json_failure("integer-out-of-range", where)
        return
    if type(value) is str:
        if unicodedata.normalize("NFC", value) != value:
            portable_json_failure("non-nfc-string", where)
        if any(0xD800 <= ord(character) <= 0xDFFF for character in value):
            portable_json_failure("surrogate-code-point", where)
        return
    if type(value) in (type(None), bool):
        return
    if type(value) not in (list, dict):
        portable_json_failure("unsupported-json-type", where)
    identity = id(value)
    if identity in active:
        portable_json_failure("cyclic-json-value", where)
    active.add(identity)
    try:
        if type(value) is list:
            for index, item in enumerate(value):
                validate_portable_json(item, f"{where}[{index}]", active)
        else:
            if any(type(key) is not str for key in value):
                portable_json_failure("non-string-object-key", f"{where}.<key>")
            ordered_keys = sorted(value)
            for key in ordered_keys:
                validate_portable_json(key, f"{where}.<key>", active)
            for key in ordered_keys:
                key_path = f"{where}/{key.replace('~', '~0').replace('/', '~1')}"
                validate_portable_json(value[key], key_path, active)
    finally:
        active.remove(identity)


def canonical(value: Any) -> str:
    validate_portable_json(value)
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def digest(domain: str, value: Any) -> str:
    return hashlib.sha256(domain.encode("ascii") + b"\0" + canonical(value).encode("utf-8")).hexdigest()


def pointer(document: Any, fragment: str) -> Any:
    current = document
    if fragment in ("", "#"):
        return current
    ok(fragment.startswith("#/"), f"unsupported schema fragment {fragment}")
    for raw in fragment[2:].split("/"):
        key = raw.replace("~1", "/").replace("~0", "~")
        current = current[key]
    return current


def is_type(value: Any, expected: str) -> bool:
    return {
        "object": isinstance(value, dict),
        "array": isinstance(value, list),
        "string": isinstance(value, str),
        "integer": isinstance(value, int) and not isinstance(value, bool),
        "boolean": isinstance(value, bool),
        "null": value is None,
    }.get(expected, True)


def validate_schema(value: Any, schema: dict[str, Any] | bool, schema_path: Path, root_schema: dict[str, Any], where: str = "$") -> None:
    if schema is True:
        return
    if schema is False:
        raise AssertionError(f"{where}: false schema rejected value")
    if "$ref" in schema:
        reference = schema["$ref"]
        if reference.startswith("#"):
            target_path, target_root = schema_path, root_schema
            target = pointer(root_schema, reference)
        else:
            file_name, _, fragment = reference.partition("#")
            if "://" in file_name:
                file_name = file_name.rsplit("/", 1)[-1]
            target_path = schema_path.parent / file_name
            target_root = load(target_path)
            target = pointer(target_root, f"#{fragment}" if fragment else "#")
        validate_schema(value, target, target_path, target_root, where)
        return
    for component in schema.get("allOf", []):
        validate_schema(value, component, schema_path, root_schema, where)
    if "if" in schema:
        try:
            validate_schema(value, schema["if"], schema_path, root_schema, where)
            condition = True
        except AssertionError:
            condition = False
        branch = schema.get("then") if condition else schema.get("else")
        if branch is not None:
            validate_schema(value, branch, schema_path, root_schema, where)
    if "not" in schema:
        try:
            validate_schema(value, schema["not"], schema_path, root_schema, where)
        except AssertionError:
            pass
        else:
            raise AssertionError(f"{where}: forbidden schema matched")
    if "oneOf" in schema:
        matches = 0
        for option in schema["oneOf"]:
            try:
                validate_schema(value, option, schema_path, root_schema, where)
                matches += 1
            except AssertionError:
                pass
        ok(matches == 1, f"{where}: expected exactly one schema alternative, got {matches}")
    if "const" in schema:
        ok(value == schema["const"], f"{where}: const mismatch")
    if "enum" in schema:
        ok(value in schema["enum"], f"{where}: {value!r} outside closed enum")
    expected_type = schema.get("type")
    if expected_type is not None:
        types = expected_type if isinstance(expected_type, list) else [expected_type]
        ok(any(is_type(value, item) for item in types), f"{where}: expected {types}, got {type(value).__name__}")
    if isinstance(value, str):
        if "minLength" in schema:
            ok(len(value) >= schema["minLength"], f"{where}: string too short")
        if "pattern" in schema:
            ok(re.search(schema["pattern"], value) is not None, f"{where}: pattern mismatch")
    if isinstance(value, int) and not isinstance(value, bool) and "minimum" in schema:
        ok(value >= schema["minimum"], f"{where}: below minimum")
    if isinstance(value, int) and not isinstance(value, bool) and "maximum" in schema:
        ok(value <= schema["maximum"], f"{where}: above maximum")
    if isinstance(value, list):
        if "minItems" in schema:
            ok(len(value) >= schema["minItems"], f"{where}: too few items")
        if "maxItems" in schema:
            ok(len(value) <= schema["maxItems"], f"{where}: too many items")
        if schema.get("uniqueItems"):
            canonical_items = [canonical(item) for item in value]
            ok(len(canonical_items) == len(set(canonical_items)), f"{where}: duplicate array item")
        prefix = schema.get("prefixItems", [])
        for index, item_schema in enumerate(prefix):
            if index < len(value):
                validate_schema(value[index], item_schema, schema_path, root_schema, f"{where}[{index}]")
        if "items" in schema:
            if schema["items"] is False:
                ok(len(value) <= len(prefix), f"{where}: additional tuple item")
            else:
                for index, item in enumerate(value[len(prefix):], start=len(prefix)):
                    validate_schema(item, schema["items"], schema_path, root_schema, f"{where}[{index}]")
    if isinstance(value, dict):
        for required in schema.get("required", []):
            ok(required in value, f"{where}: missing {required}")
        properties = schema.get("properties", {})
        for key, item in value.items():
            if key in properties:
                validate_schema(item, properties[key], schema_path, root_schema, f"{where}.{key}")
            elif schema.get("additionalProperties") is False:
                raise AssertionError(f"{where}: unexpected property {key}")
            elif isinstance(schema.get("additionalProperties"), dict):
                validate_schema(item, schema["additionalProperties"], schema_path, root_schema, f"{where}.{key}")


def validate_fixture(name: str, schema_name: str) -> None:
    schema_path = SCHEMAS / schema_name
    schema = load(schema_path)
    validate_schema(load(FIXTURES / name), schema, schema_path, schema)


def verify_official_draft_2020_12(fixtures: dict[str, str], package_instances: dict[str, str] | None = None) -> None:
    try:
        from jsonschema import Draft202012Validator
        from referencing import Registry, Resource
    except ImportError as error:
        raise AssertionError("official Draft 2020-12 jsonschema validator is required") from error
    schema_documents = [load(path) for path in sorted(SCHEMAS.glob("*.schema.json"))]
    registry = Registry().with_resources((schema["$id"], Resource.from_contents(schema)) for schema in schema_documents)
    for schema in schema_documents:
        Draft202012Validator.check_schema(schema)
    for fixture_name, schema_name in fixtures.items():
        schema = next(item for item in schema_documents if item["$id"].endswith(f"/{schema_name}"))
        errors = list(Draft202012Validator(schema, registry=registry).iter_errors(load(FIXTURES / fixture_name)))
        ok(not errors, f"official Draft 2020-12 validation failed for {fixture_name}: {errors[0].message if errors else ''}")
    for instance_name, schema_name in (package_instances or {}).items():
        schema = next(item for item in schema_documents if item["$id"].endswith(f"/{schema_name}"))
        errors = list(Draft202012Validator(schema, registry=registry).iter_errors(load(PACKAGE / instance_name)))
        ok(not errors, f"official Draft 2020-12 validation failed for {instance_name}: {errors[0].message if errors else ''}")
    role_schema = next(item for item in schema_documents if item["$id"].endswith("/artifact-role-specs.schema.json"))
    errors = list(Draft202012Validator(role_schema, registry=registry).iter_errors(load(PACKAGE / "artifact-role-specs.json")))
    ok(not errors, f"official Draft 2020-12 validation failed for artifact role specs: {errors[0].message if errors else ''}")


def validate_official_instance(value: Any, schema_name: str) -> None:
    from jsonschema import Draft202012Validator
    from referencing import Registry, Resource
    schema_documents = [load(path) for path in sorted(SCHEMAS.glob("*.schema.json"))]
    registry = Registry().with_resources((schema["$id"], Resource.from_contents(schema)) for schema in schema_documents)
    file_name, separator, fragment = schema_name.partition("#")
    schema_root = next(item for item in schema_documents if item["$id"].endswith(f"/{file_name}"))
    schema = {"$ref": f"{schema_root['$id']}#{fragment}"} if separator else schema_root
    errors = list(Draft202012Validator(schema, registry=registry).iter_errors(value))
    ok(not errors, f"official Draft 2020-12 validation failed for synthetic {schema_name}: {errors[0].message if errors else ''}")


def value_without(value: dict[str, Any], *keys: str) -> dict[str, Any]:
    result = deepcopy(value)
    for key in keys:
        result.pop(key, None)
    return result


def expect_schema_rejection(value: Any, schema_name: str, message: str) -> None:
    schema_path = SCHEMAS / schema_name
    schema = load(schema_path)
    try:
        validate_schema(value, schema, schema_path, schema)
    except AssertionError:
        ok(True, message)
    else:
        raise AssertionError(message)
    if schema_name not in OFFICIAL_VALIDATORS:
        from jsonschema import Draft202012Validator
        from referencing import Registry, Resource
        schema_documents = [load(path) for path in sorted(SCHEMAS.glob("*.schema.json"))]
        registry = Registry().with_resources((schema["$id"], Resource.from_contents(schema)) for schema in schema_documents)
        official_schema = next(item for item in schema_documents if item["$id"].endswith(f"/{schema_name}"))
        OFFICIAL_VALIDATORS[schema_name] = Draft202012Validator(official_schema, registry=registry)
    ok(bool(list(OFFICIAL_VALIDATORS[schema_name].iter_errors(value))), f"official Draft 2020-12 validator accepted: {message}")


def expect_semantic_rejection(checker: Any, value: Any, message: str) -> None:
    try:
        checker(value)
    except AssertionError:
        ok(True, message)
    else:
        raise AssertionError(message)


def reject_baseline_mismatch(failures: list[dict[str, Any]], placement: str) -> None:
    ok(all(failure["classification"] != "baseline-mismatch" for failure in failures), f"baseline-mismatch escaped into {placement}")


def failure_schema_placements() -> dict[tuple[str, str], str]:
    placements: dict[tuple[str, str], str] = {}

    def visit(value: Any, schema_name: str, location: str) -> None:
        if isinstance(value, dict):
            reference = value.get("$ref")
            if isinstance(reference, str) and (reference.endswith("Failure") or reference.endswith("common.schema.json#/$defs/failure")):
                placements[(schema_name, location or "/")] = reference
            for key, child in value.items():
                escaped = key.replace("~", "~0").replace("/", "~1")
                visit(child, schema_name, f"{location}/{escaped}")
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, schema_name, f"{location}/{index}")

    for schema_path in sorted(SCHEMAS.glob("*.schema.json")):
        visit(load(schema_path), schema_path.name, "")
    return placements


def verify_generic_failure_schema_inventory() -> None:
    expected = {
        ("observation-installation-result.schema.json", "/properties/failures/items"): "common.schema.json#/$defs/observationInstallationFailure",
        ("pattern-result.schema.json", "/properties/failures/items"): "common.schema.json#/$defs/patternTestFailure",
        ("pattern-result.schema.json", "/$defs/pathResult/properties/failures/items"): "common.schema.json#/$defs/patternPathFailure",
        ("corpus-result.schema.json", "/properties/failures/items"): "common.schema.json#/$defs/corpusSharedSetupFailure",
        ("corpus-result.schema.json", "/properties/components/items/properties/failures/items"): "common.schema.json#/$defs/patternTestFailure",
        ("corpus-result.schema.json", "/properties/components/items/properties/pathResults/items/properties/failures/items"): "common.schema.json#/$defs/patternPathFailure",
        ("mutation-site-registry.schema.json", "/properties/discovery/properties/failure/oneOf/1"): "common.schema.json#/$defs/mutationDiscoveryFailure",
        ("mutation-campaign.schema.json", "/properties/failures/items"): "#/$defs/campaignFailure",
        ("mutation-campaign.schema.json", "/properties/generation/properties/failures/items"): "common.schema.json#/$defs/candidateGenerationFailure",
        ("mutation-campaign.schema.json", "/properties/baseline/properties/failures/items"): "#/$defs/baselineFailure",
        ("mutation-campaign.schema.json", "/$defs/candidateRejection/properties/failures/items"): "common.schema.json#/$defs/candidateGenerationFailure",
        ("mutation-campaign.schema.json", "/$defs/oracleResult/properties/failure/oneOf/0/oneOf/0/properties/failure"): "common.schema.json#/$defs/baselineExecutionFailure",
        ("mutation-campaign.schema.json", "/$defs/oracleResult/properties/failure/oneOf/0/oneOf/1/properties/failure"): "common.schema.json#/$defs/oracleOperandProductionFailure",
        ("mutation-campaign.schema.json", "/$defs/oracleResult/properties/failure/oneOf/0/oneOf/2/properties/failure"): "common.schema.json#/$defs/mutantExecutionFailure",
        ("mutation-campaign.schema.json", "/$defs/oracleResult/properties/failure/oneOf/0/oneOf/3/properties/failure"): "common.schema.json#/$defs/oracleOperandProductionFailure",
        ("mutation-campaign.schema.json", "/$defs/oracleResult/properties/failure/oneOf/0/oneOf/4/properties/failure"): "common.schema.json#/$defs/oracleComparisonFailure",
        ("mutation-campaign.schema.json", "/$defs/mutant/properties/failures/items"): "#/$defs/mutantFailure",
        ("mutation-campaign.schema.json", "/$defs/campaignFailure/oneOf/0"): "common.schema.json#/$defs/campaignFailure",
        ("mutation-campaign.schema.json", "/$defs/campaignFailure/oneOf/1"): "common.schema.json#/$defs/reportPublicationFailure",
        ("mutation-campaign.schema.json", "/$defs/baselineFailure/oneOf/0"): "common.schema.json#/$defs/baselineValidationFailure",
        ("mutation-campaign.schema.json", "/$defs/baselineFailure/oneOf/1"): "common.schema.json#/$defs/baselineExecutionFailure",
        ("mutation-campaign.schema.json", "/$defs/baselineFailure/oneOf/2"): "common.schema.json#/$defs/baselineOracleGateFailure",
        ("mutation-campaign.schema.json", "/$defs/mutantFailure/oneOf/0"): "common.schema.json#/$defs/mutantValidationFailure",
        ("mutation-campaign.schema.json", "/$defs/mutantFailure/oneOf/1"): "common.schema.json#/$defs/mutantExecutionFailure",
        ("oracle-semantics.schema.json", "/$defs/baselineGateResult/properties/failure/oneOf/0"): "common.schema.json#/$defs/baselineOracleGateFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/0/properties/terminalRecord/oneOf/2/properties/failure/oneOf/0"): "common.schema.json#/$defs/baselineExecutionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/0/properties/terminalRecord/oneOf/2/properties/failure/oneOf/1"): "common.schema.json#/$defs/mutantExecutionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/0/properties/terminalRecord/oneOf/3/properties/failure/oneOf/0"): "common.schema.json#/$defs/baselineExecutionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/0/properties/terminalRecord/oneOf/3/properties/failure/oneOf/1"): "common.schema.json#/$defs/mutantExecutionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/1/properties/terminalRecord/oneOf/2/properties/failure/oneOf/0"): "common.schema.json#/$defs/oracleOperandProductionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/1/properties/terminalRecord/oneOf/2/properties/failure/oneOf/1"): "common.schema.json#/$defs/oracleComparisonFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/1/properties/terminalRecord/oneOf/3/properties/failure/oneOf/0"): "common.schema.json#/$defs/oracleOperandProductionFailure",
        ("cache-semantics.schema.json", "/$defs/cacheRecord/oneOf/1/properties/terminalRecord/oneOf/3/properties/failure/oneOf/1"): "common.schema.json#/$defs/oracleComparisonFailure",
    }
    actual = failure_schema_placements()
    bag15_failure_schemas = {
        "operation-receipt.schema.json", "mutation-materialization-result.schema.json",
        "oracle-operand-production-result.schema.json", "campaign-derivation-result.schema.json",
        "report-publication-result.schema.json", "baseline-admission-result.schema.json",
        "oracle-comparison-production-result.schema.json", "provenance-mutation-report.schema.json",
    }
    expected.update({placement: reference for placement, reference in actual.items() if placement[0] in bag15_failure_schemas})
    bag16_failure_schemas = {
        "bag16-common.schema.json", "branch-trace-collection.schema.json",
        "corpus-component-result.schema.json", "operation-receipt-v2.schema.json",
        "pattern-result-v2.schema.json",
    }
    expected.update({placement: reference for placement, reference in actual.items() if placement[0] in bag16_failure_schemas})
    expected.update({
        placement: reference for placement, reference in actual.items()
        if placement[0] == "cache-semantics.schema.json"
        and placement[1].startswith(("/$defs/executionTerminalRecord/", "/$defs/oracleTerminalRecord/"))
    })
    broad_spellings = (
        "common.schema.json#/$defs/failure",
        "https://starstream.dev/k-in-k/backend-agnostic/v1/common.schema.json#/$defs/failure",
    )
    ok(all(reference.endswith("common.schema.json#/$defs/failure") for reference in broad_spellings), "broad failure reference spelling adversary is incomplete")
    ok(all(not reference.endswith("common.schema.json#/$defs/failure") for reference in actual.values()), "broad raw failure schema placement remains")
    ok(actual == expected, "context-specific failure schema placement inventory drift")


def verify_inventory() -> None:
    inventory = load(PACKAGE / "evidence-inventory.json")
    manifest = load(PACKAGE / "completion-manifest.json")
    allowed = set(inventory["classifications"])
    ids: set[str] = set()
    for entry in inventory["entries"]:
        ok(entry["id"] not in ids, f"duplicate inventory id {entry['id']}")
        ids.add(entry["id"])
        ok(set(entry["classification"]) <= allowed, f"unknown inventory class in {entry['id']}")
        for relative in entry["paths"]:
            ok(not Path(relative).is_absolute(), f"absolute inventory path {relative}")
            ok((ROOT / relative).is_file(), f"missing inventory evidence {relative}")
    ok("r3-g-05-final-stop" in ids, "terminal stop missing from inventory")
    required = set(manifest["requiredEvidenceIds"])
    ok(required <= ids, f"mandatory evidence IDs omitted: {sorted(required - ids)}")
    for evidence_id in sorted(required):
        reduced = ids - {evidence_id}
        try:
            ok(required <= reduced, f"missing mandatory evidence {evidence_id}")
        except AssertionError:
            ok(True, f"omission adversary for evidence {evidence_id}")
        else:
            raise AssertionError(f"omitting mandatory evidence {evidence_id} was accepted")


def verify_completion_checklist() -> None:
    manifest = load(PACKAGE / "completion-manifest.json")
    checklist = load(PACKAGE / "completion-checklist.json")
    ok(manifest["completionStatus"] in ("pending-independent-audit", "complete"), "unknown completion status")
    ok((ROOT / manifest["completionAudit"]).is_file(), "completion audit is missing")
    ok(checklist["packageVersion"] == manifest["packageVersion"], "completion package version mismatch")
    for source in checklist["sources"]:
        ok((ROOT / source).is_file(), f"missing completion source {source}")
    allowed_states = set(checklist["states"])
    inventory_ids = {entry["id"] for entry in load(PACKAGE / "evidence-inventory.json")["entries"]}
    ids: set[str] = set()
    for entry in checklist["entries"]:
        ok(entry["id"] not in ids, f"duplicate checklist ID {entry['id']}")
        ids.add(entry["id"])
        ok(entry["goal"] in ("execution-pattern", "semantic-mutation", "scope"), f"unknown checklist goal {entry['id']}")
        ok(entry["state"] in allowed_states, f"unknown checklist state {entry['id']}")
        ok(bool(entry["source"]) and bool(entry["rustProof"]), f"incomplete checklist boundary {entry['id']}")
        ok(bool(entry["artifacts"]), f"checklist entry without artifact {entry['id']}")
        for artifact in entry["artifacts"]:
            ok((ROOT / artifact).is_file(), f"missing checklist artifact {artifact}")
        ok(set(entry["historicalEvidence"]) <= inventory_ids, f"unknown historical evidence in {entry['id']}")
    required = set(manifest["requiredChecklistIds"])
    ok(ids == required, f"completion checklist ID mismatch: missing={sorted(required - ids)}, extra={sorted(ids - required)}")
    for checklist_id in sorted(required):
        reduced = ids - {checklist_id}
        try:
            ok(required <= reduced, f"missing mandatory checklist item {checklist_id}")
        except AssertionError:
            ok(True, f"omission adversary for checklist {checklist_id}")
        else:
            raise AssertionError(f"omitting mandatory checklist item {checklist_id} was accepted")
    for artifact in manifest["requiredArtifacts"]:
        ok(not Path(artifact).is_absolute() and (ROOT / artifact).is_file(), f"missing required package artifact {artifact}")


def verify_closure_matrix() -> None:
    matrix = load(PACKAGE / "closure-matrix.json")
    allowed = set(matrix["states"])
    ids: set[str] = set()
    for item in matrix["requirements"]:
        ok(item["id"] not in ids, f"duplicate closure requirement {item['id']}")
        ids.add(item["id"])
        ok(item["state"] in allowed, f"unknown closure state for {item['id']}")
        ok(bool(item["rustOpen"]), f"missing Rust boundary for {item['id']}")
        for artifact in item["artifacts"]:
            ok((ROOT / artifact).is_file(), f"missing closure artifact {artifact}")


def verify_taxonomy() -> None:
    historical_taxonomy = load(PACKAGE / "failure-taxonomy.json")
    taxonomy = load(FIXTURES / "bag16-failure-taxonomy.json")
    schema_path = SCHEMAS / "failure-taxonomy.schema.json"
    schema = load(schema_path)
    validate_schema(historical_taxonomy, schema, schema_path, schema)
    validate_schema(taxonomy, schema, schema_path, schema)
    validate_official_instance(historical_taxonomy, "failure-taxonomy.schema.json")
    validate_official_instance(taxonomy, "failure-taxonomy.schema.json")
    ok(
        historical_taxonomy["taxonomyId"]
        == digest("k-in-k/failure-taxonomy/v1", value_without(historical_taxonomy, "taxonomyId")),
        "historical failure taxonomy ID drift",
    )
    ok(taxonomy["taxonomyId"] == digest("k-in-k/failure-taxonomy/v1", value_without(taxonomy, "taxonomyId")), "failure taxonomy ID drift")
    ok(taxonomy == bag16_successor_failure_taxonomy(PACKAGE), "BAG-16 successor taxonomy is not the exact five-placement derivation")
    pairs = [(item["stage"], item["classification"]) for item in taxonomy["entries"]]
    ok(len(pairs) == len(set(pairs)), "duplicate failure stage/classification")
    common = load(SCHEMAS / "common.schema.json")
    schema_pairs = []
    for branch in common["$defs"]["failure"]["allOf"][0]["oneOf"]:
        stage = branch["properties"]["stage"]["const"]
        schema_pairs.extend((stage, classification) for classification in branch["properties"]["classification"]["enum"])
    ok(pairs == schema_pairs, "schema and canonically ordered taxonomy stage/class pairs differ")
    ok("semantic-crash" not in {classification for _, classification in pairs}, "semantic crash remains a generic failure classification")
    context_order = {name: index for index, name in enumerate(common["$defs"]["failure"]["properties"]["context"]["enum"])}
    scope_order = {name: index for index, name in enumerate(common["$defs"]["failure"]["properties"]["scope"]["enum"])}
    placements: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    for entry in taxonomy["entries"]:
        keys = [(item["context"], item["scope"]) for item in entry["placements"]]
        ok(keys == sorted(keys, key=lambda item: (context_order[item[0]], scope_order[item[1]])) and len(keys) == len(set(keys)), "failure placements are duplicate or noncanonical")
        expected_policy = "checked-lowering-cycle-receipt-v1" if (entry["stage"], entry["classification"]) == ("lowering", "lowering-nontermination") else "none"
        ok(entry["evidencePolicy"] == expected_policy, "failure evidence policy is not exact")
        for item in entry["placements"]:
            key = (item["context"], item["scope"], entry["stage"], entry["classification"])
            ok(key not in placements, "duplicate conflicting failure placement")
            placements[key] = item["consequence"]

    from jsonschema import Draft202012Validator
    from referencing import Registry, Resource
    resources = [load(path) for path in sorted(SCHEMAS.glob("*.schema.json"))]
    registry = Registry().with_resources((item["$id"], Resource.from_contents(item)) for item in resources)
    schema_placements: set[tuple[str, str, str, str]] = set()
    def_names = {context: "".join([context.split("-")[0], *[part.title() for part in context.split("-")[1:]]]) + "Failure" for context in context_order}
    retry_by_pair = {(item["stage"], item["classification"]): item["retryability"] for item in taxonomy["entries"]}
    for context, definition_name in def_names.items():
        context_schema = deepcopy(common)
        context_schema["$ref"] = f"#/$defs/{definition_name}"
        validator = Draft202012Validator(context_schema, registry=registry)
        for stage, classification in pairs:
            retryability = retry_by_pair[(stage, classification)]
            for scope in scope_order:
                evidence = [{"role": "lowering-proof-check-receipt", "digest": "0" * 64}] if (stage, classification) == ("lowering", "lowering-nontermination") else []
                candidate = {"stage": stage, "classification": classification, "context": context, "scope": scope, "retryability": retryability, "semanticEvidence": evidence, "details": {}}
                if validator.is_valid(candidate):
                    schema_placements.add((context, scope, stage, classification))
    # BAG-16 adds producer-only pattern-test infrastructure failures through
    # its successor schema.  They are deliberately absent from the frozen v1
    # common.schema.json context union.
    bag16_common = load(SCHEMAS / "bag16-common.schema.json")
    bag16_producer_schema = deepcopy(bag16_common)
    bag16_producer_schema["$ref"] = "#/$defs/patternProducerFailure"
    bag16_producer_validator = Draft202012Validator(bag16_producer_schema, registry=registry)
    producer_retryability = {
        "process-launch": "after-external-repair", "io": "after-external-repair",
        "worker-lost": "after-external-repair", "artifact-corruption": "never",
        "internal": "never",
    }
    retry_values = {"never", "same-input-after-resource-change", "after-external-repair"}
    for classification, expected_retryability in producer_retryability.items():
        for retryability in sorted(retry_values - {expected_retryability}):
            wrong_retry = {
                "stage": "infrastructure", "classification": classification,
                "context": "pattern-test", "scope": "test",
                "retryability": retryability, "semanticEvidence": [], "details": {},
            }
            ok(not bag16_producer_validator.is_valid(wrong_retry), f"BAG-16 producer failure accepted wrong retryability for {classification}")
        wrong_evidence = {
            "stage": "infrastructure", "classification": classification,
            "context": "pattern-test", "scope": "test",
            "retryability": expected_retryability,
            "semanticEvidence": [{"role": "lowering-proof-check-receipt", "digest": "0" * 64}],
            "details": {},
        }
        ok(not bag16_producer_validator.is_valid(wrong_evidence), f"BAG-16 producer failure accepted semantic evidence for {classification}")
    for stage, classification in pairs:
        retryability = retry_by_pair[(stage, classification)]
        candidate = {
            "stage": stage, "classification": classification,
            "context": "pattern-test", "scope": "test",
            "retryability": retryability, "semanticEvidence": [], "details": {},
        }
        if bag16_producer_validator.is_valid(candidate):
            schema_placements.add(("pattern-test", "test", stage, classification))
    ok(schema_placements == set(placements), f"taxonomy/schema placement reachability differs: schema-only={sorted(schema_placements - set(placements))}, taxonomy-only={sorted(set(placements) - schema_placements)}")

    taxonomy_contexts = {context for context, _, _, _ in placements}
    ok(len(taxonomy_contexts) == 15 and taxonomy_contexts == set(FAILURE_CONTEXT_CONSUMERS), "failure consumer inventory does not exactly cover all 15 taxonomy contexts")
    ok(all(consumers for consumers in FAILURE_CONTEXT_CONSUMERS.values()), "failure consumer inventory contains an unowned context")
    context_samples: dict[str, tuple[int, int]] = {}
    for entry_index, entry in enumerate(taxonomy["entries"]):
        for placement_index, placement in enumerate(entry["placements"]):
            context_samples.setdefault(placement["context"], (entry_index, placement_index))
    for context in sorted(taxonomy_contexts):
        entry_index, placement_index = context_samples[context]
        entry = taxonomy["entries"][entry_index]
        placement = entry["placements"][placement_index]
        evidence = [{"role": "lowering-proof-check-receipt", "digest": "0" * 64}] if (entry["stage"], entry["classification"]) == ("lowering", "lowering-nontermination") else []
        failure = {"stage": entry["stage"], "classification": entry["classification"], "context": context, "scope": placement["scope"], "retryability": entry["retryability"], "semanticEvidence": evidence, "details": {}}
        stale_disposition = placement["consequence"]["disposition"]
        drifted_taxonomy = deepcopy(taxonomy)
        drifted_consequence = drifted_taxonomy["entries"][entry_index]["placements"][placement_index]["consequence"]
        drifted_consequence["disposition"] = "unknown" if stale_disposition == "error" else "error"
        drifted_taxonomy["taxonomyId"] = digest("k-in-k/failure-taxonomy/v1", value_without(drifted_taxonomy, "taxonomyId"))
        validate_schema(drifted_taxonomy, schema, schema_path, schema)
        for consumer in sorted(FAILURE_CONTEXT_CONSUMERS[context]):
            expect_semantic_rejection(lambda value, consumer=consumer, drifted_taxonomy=drifted_taxonomy, stale_disposition=stale_disposition: ok(consume_failure_disposition(value, consumer, drifted_taxonomy) == stale_disposition, "stale consumer consequence survived taxonomy drift"), failure, f"{context}/{consumer} accepted a stale taxonomy consequence")
        if context == "report-publication":
            expect_semantic_rejection(lambda value: report_publication_disposition(value, drifted_taxonomy), failure, "report publication accepted a stale unpublishable-report consequence")

    def validate_failure(failure: dict[str, Any]) -> None:
        key = (failure["context"], failure["scope"], failure["stage"], failure["classification"])
        ok(key in placements, "unregistered or unreachable failure placement")
        ok(failure["retryability"] == retry_by_pair[(failure["stage"], failure["classification"])], "failure retryability contradicts taxonomy")
        expected_evidence = 1 if (failure["stage"], failure["classification"]) == ("lowering", "lowering-nontermination") else 0
        ok(len(failure["semanticEvidence"]) == expected_evidence, "failure semantic evidence cardinality contradicts taxonomy")

    def walk(value: Any) -> None:
        if isinstance(value, dict):
            if {"stage", "classification", "context", "scope", "retryability", "semanticEvidence", "details"} <= set(value) and isinstance(value["stage"], str) and isinstance(value["classification"], str):
                validate_failure(value)
            for item in value.values():
                walk(item)
        elif isinstance(value, list):
            for item in value:
                walk(item)

    for path in sorted(PACKAGE.rglob("*.json")):
        if path.name != "failure-taxonomy.json":
            walk(load(path))
    invalid_scope = {"stage": "input", "classification": "malformed", "context": "corpus-shared-setup", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
    expect_semantic_rejection(validate_failure, invalid_scope, "invalid failure scope was accepted")
    invalid_retry = {"stage": "execution", "classification": "time-limit", "context": "mutant-execution", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
    expect_semantic_rejection(validate_failure, invalid_retry, "invalid failure retryability was accepted")


def verify_lowering_proof_protocol() -> None:
    data = load(VECTORS / "lowering-proof-vectors.json")
    relation = data["frozenRelation"]
    relation_id = digest("k-in-k/frozen-lowering-relation/v1", relation)
    ok(data["relationId"] == relation_id, "frozen toy lowering relation drift")
    registry = {(item["checkerId"], item["checkerVersion"]): item for item in data["checkerRegistry"]}
    ok(set(registry) == {("portable-finite-cycle-checker", 1)}, "portable lowering checker registry drift")
    artifacts = {(item["key"]["role"], item["key"]["digest"]): item["value"] for item in data["artifacts"]}
    ok(len(artifacts) == len(data["artifacts"]), "duplicate lowering proof artifact key")
    for item in data["artifacts"]:
        role = item["key"]["role"]
        schema_name = "lowering-cycle-proof.schema.json" if role == "lowering-cycle-proof" else "lowering-proof-check-receipt.schema.json"
        validate_official_instance(item["value"], schema_name)
        expected = digest(f"k-in-k/{role}/v1", value_without(item["value"], "proofId" if role == "lowering-cycle-proof" else "receiptId"))
        self_id = item["value"]["proofId" if role == "lowering-cycle-proof" else "receiptId"]
        ok(item["key"]["digest"] == self_id == expected, "lowering proof artifact identity drift")

    def check_receipt(receipt_key: dict[str, str], expected_subject: dict[str, Any] | None = None, expected_lowering: str | None = None, expected_execution: str | None = None, artifact_map: dict[tuple[str, str], Any] | None = None) -> dict[str, Any]:
        available = artifacts if artifact_map is None else artifact_map
        ok(receipt_key["role"] == "lowering-proof-check-receipt", "semantic evidence has the wrong role")
        receipt = available.get((receipt_key["role"], receipt_key["digest"]))
        ok(receipt is not None, "lowering receipt is dangling")
        ok(receipt["receiptId"] == digest("k-in-k/lowering-proof-check-receipt/v1", value_without(receipt, "receiptId")), "lowering receipt ID drift")
        registration = registry.get((receipt["checkerId"], receipt["checkerVersion"]))
        ok(registration is not None and registration["proofKind"] == "finite-cycle-witness-v1", "unknown lowering checker or checker version")
        proof = available.get((receipt["proof"]["role"], receipt["proof"]["digest"]))
        ok(proof is not None and receipt["proof"]["role"] == "lowering-cycle-proof", "lowering proof is dangling or wrong-role")
        ok(proof["proofId"] == digest("k-in-k/lowering-cycle-proof/v1", value_without(proof, "proofId")), "lowering proof ID drift")
        ok(proof["proofKind"] == registration["proofKind"], "unknown lowering proof kind")
        for key in ("subject", "loweringProfileDigest", "executionProfileDigest", "relationId"):
            ok(receipt[key] == proof[key], f"lowering proof/receipt {key} drift")
        ok(receipt["relationId"] == registration["relationId"] == data["relationId"] == relation_id, "lowering relation root drift")
        if expected_subject is not None: ok(receipt["subject"] == expected_subject, "lowering subject drift or baseline/mutant reversal")
        if expected_lowering is not None: ok(receipt["loweringProfileDigest"] == expected_lowering, "lowering profile drift")
        if expected_execution is not None: ok(receipt["executionProfileDigest"] == expected_execution, "execution profile drift")
        cycle = proof["cycleStates"]
        ok(len(cycle) >= 3 and cycle[0] == cycle[-1] and len(set(cycle[:-1])) >= 2, "lowering cycle is empty, nonclosing, or degenerate")
        states = set(relation["states"])
        edges = {tuple(edge) for edge in relation["edges"]}
        ok(all(state in states for state in cycle), "lowering cycle has a missing state")
        ok(all((left, right) in edges for left, right in zip(cycle, cycle[1:])), "lowering cycle has a broken or reordered edge")
        ok(receipt["checkedResult"] == "nontermination-confirmed", "self-asserted receipt verdict differs from recomputed result")
        return receipt

    subjects = {}
    for case in data["cases"]:
        receipt = check_receipt(case["receiptKey"])
        subjects[case["subjectRole"]] = receipt["subject"]
    ok(set(subjects) == {"baseline", "mutant"}, "baseline/mutant lowering proof subjects are not both represented")
    failure = data["authorizedFailure"]
    ok(failure["classification"] == "lowering-nontermination" and failure["context"] == "mutant-validation" and failure["scope"] == "mutant", "checked lowering cycle did not bind the nontermination classification")
    receipt = check_receipt(failure["semanticEvidence"][0], subjects["mutant"])
    ok(receipt["checkedResult"] == "nontermination-confirmed", "checked lowering cycle did not authorize mutant invalid")

    def reject_mutation(mutator: Any, message: str) -> None:
        altered = deepcopy(data)
        mutator(altered)
        altered_artifacts = {(item["key"]["role"], item["key"]["digest"]): item["value"] for item in altered["artifacts"]}
        key = altered["authorizedFailure"]["semanticEvidence"][0]
        expect_semantic_rejection(lambda _: check_receipt(key, subjects["mutant"], artifact_map=altered_artifacts), altered, message)

    expect_semantic_rejection(lambda _: check_receipt({"role": "lowering-proof-check-receipt", "digest": "f" * 64}), data, "dangling nontermination evidence was accepted")
    expect_semantic_rejection(lambda _: check_receipt({"role": "lowering-cycle-proof", "digest": next(iter(artifacts))[1]}), data, "wrong-role nontermination evidence was accepted")
    reject_mutation(lambda value: value["artifacts"][2]["value"].update({"cycleStates": ["lowering-a", "lowering-b"]}), "nonclosing cycle was accepted")
    reject_mutation(lambda value: value["artifacts"][2]["value"].update({"cycleStates": ["lowering-a", "lowering-a", "lowering-a"]}), "degenerate cycle was accepted")
    reject_mutation(lambda value: value["artifacts"][2]["value"].update({"cycleStates": ["lowering-a", "missing", "lowering-a"]}), "missing-state cycle was accepted")
    reject_mutation(lambda value: value["artifacts"][2]["value"].update({"cycleStates": ["lowering-a", "lowering-b", "lowering-b", "lowering-a"]}), "broken-edge cycle was accepted")
    reject_mutation(lambda value: value["artifacts"][3]["value"].update({"checkerVersion": 2}), "unknown checker version was accepted")
    reject_mutation(lambda value: value["artifacts"][3]["value"].update({"checkedResult": "cycle-confirmed"}), "self-asserted receipt verdict was accepted")
    reject_mutation(lambda value: value["artifacts"][2]["value"].update({"proofKind": "supplied-relation-v1"}), "unknown proof kind was accepted")
    reject_mutation(lambda value: value["artifacts"][3]["value"].update({"loweringProfileDigest": "e" * 64}), "lowering profile drift was accepted")
    reject_mutation(lambda value: value["artifacts"][3]["value"]["proof"].update({"digest": "f" * 64}), "receipt proof-key drift was accepted")
    mutant_receipt_key = next(case["receiptKey"] for case in data["cases"] if case["subjectRole"] == "mutant")
    expect_semantic_rejection(lambda _: check_receipt(mutant_receipt_key, subjects["baseline"]), data, "baseline failure accepted a mutant-only receipt")
    reversed_subject = deepcopy(subjects["mutant"])
    reversed_subject["baselineDefinitionDigest"] = reversed_subject["mutantDefinitionDigest"]
    expect_semantic_rejection(lambda _: check_receipt(mutant_receipt_key, reversed_subject), data, "baseline/mutant subject reversal was accepted")
    drifted_subject = deepcopy(subjects["mutant"])
    drifted_subject["mutantDefinitionDigest"] = "d" * 64
    expect_semantic_rejection(lambda _: check_receipt(mutant_receipt_key, drifted_subject), data, "mutant definition drift was accepted")
    expect_semantic_rejection(lambda _: check_receipt(mutant_receipt_key, subjects["mutant"], expected_execution="c" * 64), data, "execution-profile drift was accepted")
    drifted_relation = deepcopy(data["frozenRelation"])
    drifted_relation["edges"].reverse()
    expect_semantic_rejection(lambda value: ok(digest("k-in-k/frozen-lowering-relation/v1", value) == data["relationId"], "toy relation drift"), drifted_relation, "frozen toy relation drift was accepted")
    hidden = deepcopy(failure)
    hidden["semanticEvidence"] = []
    hidden["details"] = {"verified": True, "cycle-confirmed": True, "receipt": failure["semanticEvidence"][0]}
    common = load(SCHEMAS / "common.schema.json")
    expect_semantic_rejection(lambda value: validate_schema(value, common["$defs"]["failure"], SCHEMAS / "common.schema.json", common), hidden, "evidence hidden in details authorized nontermination")
    ordinary = {"stage": "execution", "classification": "time-limit", "context": "mutant-execution", "scope": "mutant", "retryability": "same-input-after-resource-change", "semanticEvidence": [failure["semanticEvidence"][0]], "details": {}}
    expect_semantic_rejection(lambda value: validate_schema(value, common["$defs"]["failure"], SCHEMAS / "common.schema.json", common), ordinary, "ordinary failure carried semantic evidence")
    expect_semantic_rejection(lambda value: ok((value["stage"], value["classification"]) == ("lowering", "lowering-nontermination"), "receipt attached to another failure"), ordinary, "valid receipt attached to another failure was accepted")


def verify_canonicalization() -> None:
    from decimal import Decimal
    from enum import Enum

    data = load(VECTORS / "canonicalization-vectors.json")
    by_id = {case["id"]: case for case in data["cases"]}
    case = by_id["object-key-order-is-irrelevant"]
    rendered = [canonical(value) for value in case["values"]]
    ok(rendered[0] == rendered[1] == case["expectedCanonicalJson"], "object canonicalization mismatch")
    ok(digest(case["domain"], case["values"][0]) == case["expectedSha256"], "object digest mismatch")
    case = by_id["array-order-is-semantic"]
    hashes = [digest(case["domain"], value) for value in case["values"]]
    ok(hashes == case["expectedSha256"], "array digest mismatch")
    ok((hashes[0] == hashes[1]) == case["expectedEqual"], "array order expectation mismatch")
    case = by_id["digest-domains-are-separated"]
    hashes = [digest(domain, case["value"]) for domain in case["domains"]]
    ok(hashes == case["expectedSha256"], "domain digest mismatch")
    ok((hashes[0] == hashes[1]) == case["expectedEqual"], "digest domain separation mismatch")
    case = by_id["canonical-edit-order"]
    ordered = sorted(range(len(case["unorderedEdits"])), key=lambda index: (case["unorderedEdits"][index]["targetLineage"], canonical(case["unorderedEdits"][index]["targetPath"]), case["unorderedEdits"][index]["operation"], case["unorderedEdits"][index]["editId"]))
    ok(ordered == case["expectedOrder"], "canonical edit order mismatch")
    case = by_id["unicode-nfc-and-control-escaping"]
    ok(canonical(case["value"]) == case["expectedCanonicalJson"], "Unicode/control canonicalization mismatch")
    ok(digest(case["domain"], case["value"]) == case["expectedSha256"], "Unicode/control digest mismatch")
    case = by_id["signed-64-boundaries"]
    for value in case["valid"]:
        validate_portable_json(value, "signed-64-valid")
        ok(canonical(value) == str(value), "signed-64 boundary spelling changed")
    for decimal in case["invalidDecimal"]:
        try:
            validate_portable_json(int(decimal), "signed-64-invalid")
        except AssertionError as error:
            ok(str(error).startswith("integer-out-of-range at signed-64-invalid"), "signed-64 rejection reason/location drift")
        else:
            raise AssertionError("out-of-range integer accepted")
    try:
        json.loads(by_id["duplicate-keys-rejected"]["invalidJson"], object_pairs_hook=unique_object)
    except ValueError:
        pass
    else:
        raise AssertionError("duplicate JSON keys accepted")
    try:
        validate_portable_json("".join(chr(item) for item in by_id["non-nfc-rejected"]["invalidCodePoints"]), "non-nfc")
    except AssertionError as error:
        ok(str(error).startswith("non-nfc-string at non-nfc"), "non-NFC rejection reason/location drift")
    else:
        raise AssertionError("non-NFC string accepted")

    boundary = by_id["in-memory-portable-domain"]
    ok(set(boundary["reasonCodes"]) == {"unsupported-json-type", "non-string-object-key", "floating-point-forbidden", "integer-out-of-range", "non-nfc-string", "surrogate-code-point", "cyclic-json-value"}, "canonicalization reason-code vector drift")

    def expect_direct_rejection(value: Any, reason: str, where: str) -> None:
        expected = f"{reason} at {where}"
        for operation in (canonical, lambda item: digest("k-in-k/direct-canonical-adversary/v1", item)):
            failures: list[str] = []
            for _ in range(2):
                try:
                    operation(value)
                except AssertionError as error:
                    failures.append(str(error))
                except Exception as error:  # pragma: no cover - this is the adversary being excluded
                    raise AssertionError(f"incidental {type(error).__name__} escaped portable JSON validation")
                else:
                    raise AssertionError(f"{reason} adversary was accepted")
            ok(failures == [expected, expected], f"{reason} failure is not deterministic: {failures}")

    for value in (0.5, -0.0, float("nan"), float("inf"), float("-inf")):
        expect_direct_rejection(value, "floating-point-forbidden", "$")
    for value in (-(2**63) - 1, 2**63):
        expect_direct_rejection(value, "integer-out-of-range", "$")
    decomposed = "e\N{COMBINING ACUTE ACCENT}"
    surrogate = "\ud800"
    expect_direct_rejection(decomposed, "non-nfc-string", "$")
    expect_direct_rejection({decomposed: 1}, "non-nfc-string", "$.<key>")
    expect_direct_rejection(surrogate, "surrogate-code-point", "$")
    expect_direct_rejection({surrogate: 1}, "surrogate-code-point", "$.<key>")

    class ExplosiveObject:
        def __repr__(self) -> str:
            raise RuntimeError("repr must not be called")

    class IntSubclass(int):
        pass

    class StrSubclass(str):
        pass

    class ListSubclass(list):
        pass

    class DictSubclass(dict):
        pass

    class ExampleEnum(Enum):
        VALUE = "value"

    unsupported = ((), set(), b"x", bytearray(b"x"), 1 + 2j, Decimal("1.0"), Path("x"), ExampleEnum.VALUE, ExplosiveObject(), IntSubclass(1), StrSubclass("x"), ListSubclass(), DictSubclass())
    for value in unsupported:
        expect_direct_rejection(value, "unsupported-json-type", "$")
    for key in (1, True, None, ("tuple",)):
        expect_direct_rejection({key: "value"}, "non-string-object-key", "$.<key>")

    direct_list_cycle: list[Any] = []
    direct_list_cycle.append(direct_list_cycle)
    expect_direct_rejection(direct_list_cycle, "cyclic-json-value", "$[0]")
    direct_dict_cycle: dict[str, Any] = {}
    direct_dict_cycle["self"] = direct_dict_cycle
    expect_direct_rejection(direct_dict_cycle, "cyclic-json-value", "$/self")
    mixed_list: list[Any] = []
    mixed_dict = {"back": mixed_list}
    mixed_list.append(mixed_dict)
    expect_direct_rejection(mixed_list, "cyclic-json-value", "$[0]/back")

    expect_direct_rejection({"z": 0, "a": 0.5}, "floating-point-forbidden", "$/a")
    expect_direct_rejection({"valid": 1, 2: "mixed"}, "non-string-object-key", "$.<key>")
    first_fault_a = {"z": 0.5, "a": 2**63}
    first_fault_b = {"a": 2**63, "z": 0.5}
    expect_direct_rejection(first_fault_a, "integer-out-of-range", "$/a")
    expect_direct_rejection(first_fault_b, "integer-out-of-range", "$/a")

    shared_child = {"é": [None, True, -(2**63), 2**63 - 1]}
    shared_value = [shared_child, shared_child]
    snapshot = deepcopy(shared_value)
    shared_rendered = canonical(shared_value)
    ok(shared_rendered == canonical(snapshot) and shared_value == snapshot, "shared acyclic value was rejected or canonicalization mutated its input")
    ok(canonical({"日本語": 1, "é": 2}) == '{"é":2,"日本語":1}', "NFC non-ASCII key ordering drift")


def identity_anchor(case: dict[str, Any], side: dict[str, Any]) -> Any:
    if "transformationId" in side:
        return [side["transformationId"], side["parents"], side["anchorIdentity"], side["role"], side["ordinal"]]
    return [case["baselineFamilyId"], side["module"], side["source"], side["location"], side["kind"], side.get("sourceOccurrenceOrdinal", 0)]


def baseline_family_payload(family: dict[str, Any]) -> dict[str, Any]:
    entries = family["entryModules"]
    ok(len(entries) == len(set(entries)), "baseline family has duplicate entry modules")
    return {"familyName": family["familyName"], "entryModules": sorted(entries), "compatibilityProfile": family["compatibilityProfile"]}


def verify_identity() -> None:
    for case in load(VECTORS / "identity-vectors.json")["cases"]:
        left, right, expected = case["left"], case["right"], case["expected"]
        ok((identity_anchor(case, left) == identity_anchor(case, right)) == expected["sameLineage"], f"{case['id']}: lineage")
        if "sameBody" in expected:
            ok((left["body"] == right["body"]) == expected["sameBody"], f"{case['id']}: body")
        if "sameContent" in expected:
            content_keys = ("module", "source", "location", "kind", "label", "body")
            left_content = [left.get(key) for key in content_keys]
            right_content = [right.get(key) for key in content_keys]
            ok((left_content == right_content) == expected["sameContent"], f"{case['id']}: content")
    fixture = load(FIXTURES / "semantic-identity.json")
    inputs = fixture["digestInputs"]
    family_id = digest("k-in-k/baseline-family/v1", baseline_family_payload(inputs["baselineFamily"]))
    ok(family_id == fixture["baselineFamilyId"] == inputs["inputLineage"]["baselineFamilyId"], "baseline-family ID derivation")
    two_entries = {"familyName": "permutation-proof", "entryModules": ["B", "A"], "compatibilityProfile": "portable-v1"}
    reversed_entries = {**two_entries, "entryModules": list(reversed(two_entries["entryModules"]))}
    ok(digest("k-in-k/baseline-family/v1", baseline_family_payload(two_entries)) == digest("k-in-k/baseline-family/v1", baseline_family_payload(reversed_entries)), "entry-module set permutation changed baseline-family identity")
    duplicate_entries = {**two_entries, "entryModules": ["A", "A"]}
    expect_semantic_rejection(baseline_family_payload, duplicate_entries, "duplicate family entry module was accepted")
    lineage_id = digest("k-in-k/input-lineage/v1", inputs["inputLineage"])
    ok(lineage_id == fixture["sentences"][0]["lineageId"] == inputs["sentenceContent"]["lineageId"], "input lineage ID derivation")
    body_id = digest("k-in-k/sentence-body/v1", inputs["sentenceBody"])
    ok(body_id == fixture["sentences"][0]["bodyFingerprint"] == inputs["sentenceContent"]["bodyFingerprint"], "body fingerprint derivation")
    content_id = digest("k-in-k/sentence-content/v1", inputs["sentenceContent"])
    ok(content_id == fixture["sentences"][0]["contentFingerprint"] == inputs["definition"]["modules"][0]["sentenceContentFingerprints"][0], "content fingerprint derivation")
    sentence_provenance = fixture["sentences"][0]
    sentence_content = inputs["sentenceContent"]
    for key in ("lineageId", "module", "label", "kind", "source", "location", "generated", "bodyFingerprint", "transformationChain"):
        ok(sentence_provenance[key] == sentence_content[key], f"standalone sentence provenance {key} differs from sentence-content digest input")
    definition_id = digest("k-in-k/definition/v1", inputs["definition"])
    ok(definition_id == fixture["definitionDigest"] == inputs["transformation"]["inputDefinitionDigest"], "definition digest derivation")
    transformation_id = digest("k-in-k/transformation/v1", inputs["transformation"])
    ok(transformation_id == fixture["transformationId"] == inputs["generatedLineage"]["transformationId"], "transformation ID derivation")
    generated_id = digest("k-in-k/generated-lineage/v1", inputs["generatedLineage"])
    ok(generated_id == fixture["generatedLineageId"], "generated lineage ID derivation")
    verify_standalone_identity_semantics(fixture)
    provenance_drift = deepcopy(fixture)
    provenance_drift["sentences"][0]["source"] = "repo://wrong/provenance.k"
    expect_semantic_rejection(verify_standalone_identity_semantics, provenance_drift, "standalone human provenance drift from sentence-content inputs was accepted")
    missing_label = deepcopy(fixture)
    missing_label["sentences"][0].pop("label")
    expect_schema_rejection(missing_label, "semantic-identity.schema.json", "standalone provenance without an explicit nullable label was accepted")
    open_kind = deepcopy(fixture)
    open_kind["digestInputs"]["sentenceContent"]["kind"] = "generated-rule"
    expect_schema_rejection(open_kind, "semantic-identity.schema.json", "standalone identity accepted an open/generated-rule sentence kind")
    open_role = deepcopy(fixture)
    open_role["digestInputs"]["generatedLineage"]["role"] = "arbitrary-generated-role"
    expect_schema_rejection(open_role, "semantic-identity.schema.json", "standalone generated identity accepted an unregistered role")
    output_definition = load(FIXTURES / "semantic-definition-identity-output.json")
    parented_sentence = next(sentence for module in output_definition["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None and sentence["generatedIdentity"]["role"] == "insert-before-lineage")
    parented = deepcopy(fixture)
    parented["digestInputs"]["generatedLineage"] = deepcopy(parented_sentence["generatedIdentity"])
    parented["generatedLineageId"] = parented_sentence["provenance"]["lineageId"]
    validate_official_instance(parented, "semantic-identity.schema.json")
    verify_standalone_identity_semantics(parented)
    duplicate_parents = deepcopy(parented)
    duplicate_parents["digestInputs"]["generatedLineage"]["parentLineages"] *= 2
    expect_schema_rejection(duplicate_parents, "semantic-identity.schema.json", "standalone generated identity accepted duplicate parents")
    false_parent = deepcopy(fixture)
    false_parent["digestInputs"]["generatedLineage"]["parentLineages"] = [false_parent["digestInputs"]["sentenceContent"]["lineageId"]]
    expect_schema_rejection(false_parent, "semantic-identity.schema.json", "parentless module insertion role was forced to carry a false parent")
    parentless_derived = deepcopy(fixture)
    parentless_derived["digestInputs"]["generatedLineage"]["role"] = "derived-rule"
    expect_schema_rejection(parentless_derived, "semantic-identity.schema.json", "parentless derived-rule standalone identity was accepted")
    invented_parent = deepcopy(parented)
    invented_parent["digestInputs"]["generatedLineage"]["parentLineages"] = ["f" * 64]
    invented_parent["generatedLineageId"] = digest("k-in-k/generated-lineage/v1", invented_parent["digestInputs"]["generatedLineage"])
    expect_semantic_rejection(verify_standalone_identity_semantics, invented_parent, "invented standalone parent was trusted without reviewed output evidence")
    invented_anchor = deepcopy(fixture)
    invented_anchor["digestInputs"]["generatedLineage"]["anchorIdentity"] = "f" * 64
    invented_anchor["generatedLineageId"] = digest("k-in-k/generated-lineage/v1", invented_anchor["digestInputs"]["generatedLineage"])
    expect_semantic_rejection(verify_standalone_identity_semantics, invented_anchor, "invented parentless module anchor was trusted without reviewed input evidence")
    stale_definition = deepcopy(fixture)
    stale_definition["transformationEvidence"]["outputDefinition"]["digest"] = load(FIXTURES / "semantic-definition-counter.json")["definitionDigest"]
    expect_semantic_rejection(verify_standalone_identity_semantics, stale_definition, "stale standalone output definition evidence was accepted")


def verify_standalone_identity_semantics(fixture: dict[str, Any]) -> None:
    input_definition = load(FIXTURES / "semantic-definition-memory.json")
    output_definition = load(FIXTURES / "semantic-definition-identity-output.json")
    validate_definition_semantics(input_definition)
    output_transformation_inputs = {sentence["generatedIdentity"]["transformationId"]: input_definition for module in output_definition["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None}
    validate_definition_semantics(output_definition, transformation_inputs=output_transformation_inputs)
    evidence = fixture["transformationEvidence"]
    ok(evidence == {"inputDefinition": {"role": "definition", "digest": input_definition["definitionDigest"]}, "outputDefinition": {"role": "mutant-definition", "digest": output_definition["definitionDigest"]}}, "standalone transformation evidence does not resolve to the exact reviewed input/output definition artifacts")
    catalog = load(FIXTURES / "artifact-catalog.json")
    catalog_keys = {(entry["role"], entry["digest"]) for entry in catalog["entries"]}
    ok({("definition", input_definition["definitionDigest"]), ("mutant-definition", output_definition["definitionDigest"])} <= catalog_keys, "standalone reviewed definition evidence is absent from the artifact catalog")
    inputs = fixture["digestInputs"]
    ok(inputs["baselineFamily"] == input_definition["family"] and fixture["baselineFamilyId"] == input_definition["baselineFamilyId"], "standalone baseline-family inputs differ from the reviewed input definition")
    ok(inputs["definition"] == definition_summary_payload(input_definition) and fixture["definitionDigest"] == input_definition["definitionDigest"], "standalone definition digest inputs differ from the reviewed input definition summary")
    content = inputs["sentenceContent"]
    ok(len(fixture["sentences"]) == 1, "standalone identity must expose exactly its human input sentence provenance")
    provenance = fixture["sentences"][0]
    for key in ("lineageId", "module", "label", "kind", "source", "location", "generated", "bodyFingerprint", "transformationChain"):
        ok(provenance[key] == content[key], f"standalone sentence provenance {key} differs from sentence-content digest input")
    resolved_sources = [sentence for module in input_definition["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == content["lineageId"]]
    ok(len(resolved_sources) == 1 and provenance == resolved_sources[0]["provenance"], "standalone human provenance does not resolve exactly in the reviewed input definition")
    source = resolved_sources[0]
    ok(inputs["sentenceBody"] == {"body": source["value"]["body"], "requires": source["value"]["requires"], "ensures": source["value"]["ensures"]} and content["attributes"] == source["value"]["attributes"], "standalone sentence body/content inputs differ from the reviewed input sentence")
    generated = inputs["generatedLineage"]
    role = generated["role"]
    parentless_roles = {"insert-module-end", "insert-module-start"}
    ok(role in {"derived-claim", "derived-rule", "insert-after-lineage", "insert-before-lineage", *parentless_roles, "observation-update"}, "standalone generated role is outside the closed portable registry")
    ok(inputs["transformation"]["inputDefinitionDigest"] == input_definition["definitionDigest"] and fixture["transformationId"] == digest("k-in-k/transformation/v1", inputs["transformation"]) == generated["transformationId"], "standalone transformation identity is not bound to the reviewed input definition")
    resolved_generated = [sentence for module in output_definition["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == fixture["generatedLineageId"]]
    ok(len(resolved_generated) == 1 and resolved_generated[0]["generatedIdentity"] == generated, "standalone generated identity does not resolve exactly in the reviewed output definition")
    parents = generated["parentLineages"]
    ok(parents == sorted(set(parents)), "standalone generated parent lineages are duplicate or noncanonical")
    input_lineages = {sentence["provenance"]["lineageId"] for module in input_definition["modules"] for sentence in module["sentences"]}
    output_lineages = {sentence["provenance"]["lineageId"] for module in output_definition["modules"] for sentence in module["sentences"]}
    input_module_anchors = {module["fingerprint"] for module in input_definition["modules"]}
    if role in parentless_roles:
        ok(not parents and generated["anchorIdentity"] in input_module_anchors, "parentless generated role has parents or an unresolved reviewed-input module anchor")
    else:
        ok(bool(parents) and set(parents) <= input_lineages | output_lineages and generated["anchorIdentity"] in input_lineages | output_lineages, "parented generated role has empty/dangling parents or lineage anchor")
        if role in {"insert-after-lineage", "insert-before-lineage"}:
            ok(generated["anchorIdentity"] in parents, "sentence-relative insertion anchor is not one of its reviewed parent lineages")


def validate_claim_boundary_artifact() -> dict[str, Any]:
    boundary = load(PACKAGE / "claim-boundary.json")
    schema_path = SCHEMAS / "claim-boundary.schema.json"
    schema = load(schema_path)
    validate_schema(boundary, schema, schema_path, schema)
    validate_official_instance(boundary, "claim-boundary.schema.json")
    ok(boundary == {
        "schemaVersion": 1,
        "representation": "portable-mutation-semantic-slice-v1",
        "portableScope": "explicitly-declared-supported-surface-only",
        "wholeKAdapterStatus": "not-proven",
        "nativeAdapterStatus": "future-proof-required",
        "parsedKRoundTripStatus": "future-proof-required",
        "unsupportedForms": "reject",
    }, "structured claim boundary drift")
    return boundary


def validate_whole_k_claim_boundary(claim: str, boundary: dict[str, Any] | None = None) -> None:
    boundary = validate_claim_boundary_artifact() if boundary is None else boundary
    declared_scope = boundary["portableScope"].replace("-only", "").replace("-", " ")
    normalized_claim = " ".join(claim.lower().replace("_", " ").split())
    clauses = re.split(r"(?<=[.!?;:])\s+|,\s*(?=(?:but|while|although|whereas|however|yet)\b)", normalized_claim)
    for normalized in clauses:
        completeness = re.search(
            r"\b(complete|completely|completeness|lossless|losslessly|losslessness|bijective|bijectively|bijection|bijectivity|"
            r"exact[- ]round[- ]trip|exactly[- ](?:round[- ]?trips?|round[- ]?tripped|round[- ]?tripping)|"
            r"(?:round[- ]?trips?|round[- ]?tripped|round[- ]?tripping)[- ]exactly|"
            r"full[- ]fidelity|faithful|faithfully|faithfulness|fully[- ]represented|injective|injectivity)\b",
            normalized,
        )
        quantified_k_surface = re.search(r"\b(?:all|every)[- ](?:whole[- ])?k(?:[- ](?:constructs?|forms?|modules?|definitions?))?\b", normalized)
        whole_k_target = re.search(
            r"\b(whole[- ]k|parsed[- ]k|native[- ]k|(?:all|every)[- ]k|"
            r"k[- ](?:definition|adapter|mapping|representation|frontend|semantic[- ]ir|constructs?|forms?|modules?)|"
            r"(?:definition|adapter|mapping|representation|frontend|semantic[- ]ir)[- ](?:for|of|from|to)[- ](?:whole[- ]|parsed[- ]|native[- ])?k)\b",
            normalized,
        )
        if (completeness is None and quantified_k_surface is None) or whole_k_target is None:
            continue
        claim_start = min(match.start() for match in (completeness, quantified_k_surface, whole_k_target) if match is not None)
        claim_end = max(match.end() for match in (completeness, quantified_k_surface, whole_k_target) if match is not None)
        denial = re.search(r"\b(?:does[- ]not[- ]claim|do[- ]not[- ]claim|without[- ]claiming)\b", normalized)
        denial_qualifies_claim = denial is not None and denial.start() <= claim_start
        proof_status = (
            r"(?:not[- ](?:yet[- ])?proven|unproven|pending|future[- ]proof[- ]required|"
            r"proof[- ]required|remains?[- ]to[- ]be[- ]proven)"
        )
        attached_status_suffix = re.fullmatch(
            r"^(?:[- ]+(?:definition|adapter|mapping|representation|frontend|semantic[- ]ir|construct|form|module)s?)?"
            r"(?:[- ]+(?:proof|status))?[- ,]*(?:(?:is|are|remain|remains)[- ])?" + proof_status + r"[.!?]*$",
            normalized[claim_end:],
        ) is not None
        attached_status_prefix = re.search(proof_status + r"(?:[- ]+(?:for|of))?[- ]*$", normalized[:claim_start]) is not None
        negative_proof_status = denial_qualifies_claim or attached_status_prefix or attached_status_suffix
        scoped = declared_scope in normalized or re.search(r"\bdeclared[- ]supported[- ]surface\b", normalized) is not None
        future_boundary = re.search(r"\b(must[- ]prove|prove|proof[- ](?:is[- ])?(?:pending|required)|future[- ]proof[- ]required|pending|requires?|required|rejects?|rejected)\b", normalized) is not None
        ok(negative_proof_status or scoped and future_boundary, "completion text overclaims a complete/lossless whole-K, native-K, or parsed-K adapter")


def json_text_values(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [text for item in value for text in json_text_values(item)]
    if isinstance(value, dict):
        return [text for item in value.values() for text in json_text_values(item)]
    return []


def markdown_claim_blocks(document: str) -> list[str]:
    blocks: list[str] = []
    current: list[str] = []
    for line in document.splitlines():
        stripped = line.strip()
        starts_claim = stripped.startswith(("#", "- ", "* ")) or re.match(r"\d+\.\s", stripped) is not None
        if not stripped or starts_claim and current:
            if current:
                blocks.append(" ".join(current))
                current = []
            if not stripped:
                continue
        current.append(stripped)
    if current:
        blocks.append(" ".join(current))
    return blocks


def terminal_artifact_registry() -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    terminal_values = [load(FIXTURES / name) for name in ("terminal-state.json", "terminal-state-mutant.json")]
    crash_values = [load(FIXTURES / name) for name in ("semantic-crash.json", "semantic-crash-mutant.json")]
    terminals = {terminal["terminalStateDigest"]: terminal for terminal in terminal_values}
    for terminal in terminal_values:
        validate_terminal_state_semantics(terminal)
    for crash in crash_values:
        ok(crash["crashDigest"] == digest("k-in-k/semantic-crash/v1", value_without(crash, "crashDigest")), "semantic crash self ID derivation")
        ok(crash["terminalState"]["role"] == "terminal-state" and crash["terminalState"]["digest"] in terminals, "semantic crash terminal state is dangling")
    return terminals, {crash["crashDigest"]: crash for crash in crash_values}


def validate_terminal_state_semantics(terminal: dict[str, Any]) -> None:
    ok(terminal["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", value_without(terminal, "terminalStateDigest")), "terminal state self ID derivation")
    signatures = definition_signatures_for_reference(definition_digest=terminal["definitionDigest"])
    validate_portable_term(terminal["value"], signatures, {})


def validate_oracle_value_semantics(value: dict[str, Any]) -> None:
    ok(value["oracleValueDigest"] == digest("k-in-k/oracle-value/v1", value_without(value, "oracleValueDigest")), "oracle value self ID derivation")
    signatures = definition_signatures_for_reference(definition_digest=value["definitionDigest"])
    validate_portable_term(value["value"], signatures, {})


def oracle_value_registry() -> dict[str, dict[str, Any]]:
    values = [load(FIXTURES / name) for name in ("oracle-value-baseline.json", "oracle-value-mutant.json")]
    for value in values:
        validate_oracle_value_semantics(value)
    return {value["oracleValueDigest"]: value for value in values}


def execution_terminal_definition_digest(terminal: Any, terminals: dict[str, dict[str, Any]], crashes: dict[str, dict[str, Any]]) -> str | None:
    if terminal is None:
        return None
    artifact = terminal["artifact"]
    if terminal["kind"] in ("normal", "stuck"):
        ok(artifact["role"] == "terminal-state" and artifact["digest"] in terminals, "terminal evidence is dangling or has the wrong role")
        return terminals[artifact["digest"]]["definitionDigest"]
    else:
        ok(terminal["kind"] == "semantic-crash" and artifact["role"] == "semantic-crash" and artifact["digest"] in crashes, "semantic crash evidence is dangling or has the wrong role")
        terminal_key = crashes[artifact["digest"]]["terminalState"]
        ok(terminal_key["role"] == "terminal-state" and terminal_key["digest"] in terminals, "semantic crash terminal state is dangling")
        return terminals[terminal_key["digest"]]["definitionDigest"]


def validate_execution_terminal(terminal: Any, terminals: dict[str, dict[str, Any]], crashes: dict[str, dict[str, Any]], expected_definition_digest: str | None = None) -> None:
    resolved_definition = execution_terminal_definition_digest(terminal, terminals, crashes)
    if terminal is not None and expected_definition_digest is not None:
        ok(resolved_definition == expected_definition_digest, "terminal/crash evidence belongs to another definition")


def validate_trace_semantics(trace: dict[str, Any], terminal_registry: tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]] | None = None, seed_signatures: SignatureRegistry | None = None) -> tuple[SignatureRegistry, dict[str, str]]:
    terminals, crashes = terminal_registry or terminal_artifact_registry()
    identity_payload = value_without(trace, "pathOrdinal", "pathKey", "pathIdentityDigest")
    ok(trace["pathIdentityDigest"] == digest("k-in-k/unkeyed-path/v1", identity_payload), "trace path identity digest derivation")
    events = trace["events"]
    ok([event["index"] for event in events] == list(range(len(events))), "event indices must be zero-based and contiguous")
    terminal = trace["executionTerminal"]
    validate_execution_terminal(terminal, terminals, crashes, trace["definitionDigest"])
    ok(trace["complete"] == (terminal is not None), "trace completeness and terminal evidence disagree")
    if trace["stopReason"] == "terminal":
        ok(terminal is not None and terminal["kind"] in ("normal", "semantic-crash"), "terminal stop lacks normal/crash terminal evidence")
    elif trace["stopReason"] == "stuck":
        ok(terminal is not None and terminal["kind"] == "stuck", "stuck stop lacks stuck terminal evidence")
    else:
        ok(terminal is None and not trace["complete"], "limit/query/error stop retained terminal evidence")
    previous_transition = -1
    expected_emission = 0
    referenced_signatures = definition_signatures_for_reference(definition_digest=trace["definitionDigest"])
    if seed_signatures is not None:
        ok(referenced_signatures == seed_signatures, "trace definition differs from its enclosing pattern definition")
    path_signatures: SignatureRegistry = dict(referenced_signatures)
    path_variables: dict[str, str] = {}
    validate_portable_term(trace["pathPredicate"], path_signatures, path_variables)
    ok(trace["pathPredicate"]["sort"] == "Bool", "trace path predicate is not Bool-sorted")
    for event in events:
        transition = event["transitionOrdinal"]
        ok(transition >= previous_transition, "transition ordinals must be monotonic")
        if transition != previous_transition:
            expected_emission = 0
        ok(event["emissionOrdinal"] == expected_emission, "emission ordinals must reset and remain contiguous per transition")
        expected_emission += 1
        previous_transition = transition
        for payload_term in event["payload"]:
            validate_portable_term(payload_term, path_signatures, path_variables)
    return path_signatures, path_variables


def witness_order_key(witness: dict[str, Any]) -> tuple[Any, ...]:
    return (witness["pathKey"], tuple(witness["eventIndices"]), digest("k-in-k/bindings/v1", witness["bindings"]), witness["armOrdinal"])


def unkeyed_witness_order_key(witness: dict[str, Any], path_identities: dict[int, str]) -> tuple[Any, ...]:
    schedule_independent = value_without(witness, "pathOrdinal")
    return (path_identities[witness["pathOrdinal"]], tuple(witness["eventIndices"]), digest("k-in-k/bindings/v1", witness["bindings"]), witness["armOrdinal"], digest("k-in-k/unkeyed-witness-order/v1", schedule_independent))


def resolved_fixture_query(inputs: dict[str, Any], query_id: str) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    ok(inputs["patternSource"]["role"] == "pattern-source" and inputs["patternPlan"]["role"] == "pattern-plan" and inputs["patternQuery"]["role"] == "pattern-query", "pattern result query roots are not role typed")
    ok(query_id == inputs["patternQuery"]["digest"], "pattern result query ID/key is inconsistent")
    catalog = load(FIXTURES / "artifact-catalog.json")
    vocabularies = load(VECTORS / "execution-pattern-vectors.json")["eventVocabularies"]
    plan, query = resolve_pattern_query_root(pattern_query_root(inputs), catalog, vocabularies, observation_vocabulary_digest(inputs["observationManifestDigest"]))
    observations = [load(FIXTURES / "observation-manifest.json"), load(FIXTURES / "mutation-observation-manifest.json")]
    observation = next((item for item in observations if item["manifestId"] == inputs["observationManifestDigest"]), None)
    ok(observation is not None, "pattern result observation manifest is unresolved")
    vocabulary = {"resolved": {"eventVocabularyDigest": observation["eventVocabularyDigest"], "constructors": observation["eventVocabulary"]}}
    validate_event_vocabulary_record(vocabulary["resolved"])
    validate_pattern_plan(plan, vocabulary, {(entry["role"], entry["digest"]) for entry in catalog["entries"]})
    table = load(FIXTURES / "side-condition-conformance-table.json")
    validate_side_condition_table(table)
    return plan, query, observation, table


def derive_trace_plan_witnesses(result: dict[str, Any], plan: dict[str, Any], table: dict[str, Any], trace: dict[str, Any], path: dict[str, Any]) -> tuple[list[dict[str, Any]], bool]:
    matches: list[dict[str, Any]] = []
    indeterminate = False
    table_rows = {(row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]): row["result"] for row in table["rows"]}

    def match_atom(atom: dict[str, Any], event: dict[str, Any], bindings: dict[str, Any]) -> dict[str, Any] | None:
        if atom["constructor"] != event["constructor"]:
            return None
        resolved = deepcopy(bindings)
        for clause in atom["payload"]:
            if clause["position"] >= len(event["payload"]):
                return None
            term = event["payload"][clause["position"]]
            variable = clause["variable"]
            if clause["mode"] == "bind":
                if variable in resolved:
                    return None
                resolved[variable] = term
            elif variable not in resolved or canonical(resolved[variable]) != canonical(term):
                return None
        return resolved

    def extend(arm: dict[str, Any], arm_ordinal: int, atom_ordinal: int, indices: list[int], bindings: dict[str, Any]) -> None:
        nonlocal indeterminate
        if atom_ordinal == len(arm["atoms"]):
            ordered_bindings = [{"name": variable["name"], "term": deepcopy(bindings[variable["name"]])} for variable in plan["variables"]]
            if plan["sideCondition"] is not None:
                by_name = {binding["name"]: binding for binding in ordered_bindings}
                condition_bindings = [deepcopy(by_name[name]) for name in plan["sideCondition"]["inputVariables"]]
                key = (plan["sideCondition"]["artifact"]["digest"], digest("k-in-k/bindings/v1", condition_bindings), digest("k-in-k/path-predicate/v1", trace["pathPredicate"]))
                condition_result = table_rows.get(key, "unknown")
                if condition_result == "false":
                    return
                if condition_result == "unknown":
                    indeterminate = True
                    return
            witness = {
                "pathOrdinal": path["pathOrdinal"], "armOrdinal": arm_ordinal,
                "eventIndices": indices, "events": [deepcopy(trace["events"][index]) for index in indices],
                "bindings": ordered_bindings, "pathPredicate": deepcopy(trace["pathPredicate"]),
                "stopReason": path["stopReason"], "executionStopReason": trace["stopReason"],
            }
            if path["pathKey"] is not None:
                witness["pathKey"] = path["pathKey"]
                witness["replayKey"] = digest("k-in-k/witness-replay-key/v1", {"testId": result["testId"], "pathKey": path["pathKey"], "eventIndices": indices})
            matches.append(witness)
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
            next_bindings = match_atom(arm["atoms"][atom_ordinal], trace["events"][index], bindings)
            if next_bindings is not None:
                extend(arm, arm_ordinal, atom_ordinal + 1, [*indices, index], next_bindings)

    for arm_ordinal, arm in enumerate(plan["arms"]):
        extend(arm, arm_ordinal, 0, [], {})
    return matches, indeterminate


def validate_pattern_result_semantics(result: dict[str, Any], trace_registry: dict[str, dict[str, Any]] | None = None, taxonomy: dict[str, Any] | None = None) -> None:
    expected_result_id = digest("k-in-k/pattern-result/v1", value_without(result, "resultId"))
    ok(result["resultId"] == expected_result_id, "pattern result ID derivation")
    witnesses = result["witnesses"]
    referenced_signatures = definition_signatures_for_reference(definition_digest=result["inputs"]["definitionDigest"])
    paths = result["pathResults"]
    plan, _query, _observation, side_table = resolved_fixture_query(result["inputs"], result["queryId"])
    path_graphs: dict[int, tuple[SignatureRegistry, dict[str, str]]] = {}
    ok([path["pathOrdinal"] for path in paths] == list(range(len(paths))), "pattern path ordinals are not contiguous")
    path_key_presence = [path["pathKey"] is not None for path in paths]
    ok(not path_key_presence or all(path_key_presence) or not any(path_key_presence), "pattern result mixes keyed and unkeyed paths")
    has_stable_path_keys = bool(path_key_presence) and all(path_key_presence)
    keyed_paths = [path["pathKey"] for path in paths if path["pathKey"] is not None]
    ok(len(keyed_paths) == len(set(keyed_paths)), "pattern result has duplicate path keys")
    if has_stable_path_keys:
        ok(keyed_paths == sorted(keyed_paths), "stable pattern paths are not in canonical key order")
    else:
        path_identities = [path["pathIdentityDigest"] for path in paths]
        ok(len(path_identities) == len(set(path_identities)) and path_identities == sorted(path_identities), "unkeyed pattern paths are duplicate or not in intrinsic identity order")
    ok(all(failure["scope"] == "test" for failure in result["failures"]), "pattern result failure does not have test scope")
    reject_baseline_mismatch(result["failures"], "pattern test failures")
    for path in paths:
        failures = path["failures"]
        reject_baseline_mismatch(failures, "pattern path failures")
        expected_execution_stop = "query-satisfied" if path["stopReason"] == "match-found" else path["stopReason"]
        ok(path["executionStopReason"] == expected_execution_stop, "query stop and execution termination are conflated or inconsistent")
        ok(all(failure["scope"] == "path" for failure in failures), "pattern path failure does not have path scope")
        dispositions = [consume_failure_disposition(failure, "pattern", taxonomy) for failure in failures]
        if path["status"] in ("match", "no-match") and path["completeCoverage"]:
            ok(path["stopReason"] in ("terminal", "stuck") and not failures, "complete pattern path lacks exhaustive stop evidence")
        elif path["status"] == "no-match":
            raise AssertionError("no-match pattern path is incomplete")
        elif path["status"] == "match" and path["stopReason"] == "match-found":
            ok(result["inputs"]["searchPolicy"] == "existential-first" and not failures, "match-found path is not a clean existential stop")
        elif path["status"] == "unknown":
            ok(not path["completeCoverage"] and dispositions and all(disposition == "unknown" for disposition in dispositions) and any(failure["classification"] == path["stopReason"] for failure in failures), "unknown pattern path differs from its taxonomy consequence")
        elif path["status"] == "error":
            ok(not path["completeCoverage"] and dispositions and all(disposition == "error" for disposition in dispositions) and path["stopReason"] == "error", "error pattern path differs from its taxonomy consequence")
        else:
            expected_failure_status = dispositions[0] if dispositions and len(set(dispositions)) == 1 else None
            stop_matches = expected_failure_status == "unknown" and any(failure["classification"] == path["stopReason"] for failure in failures) or expected_failure_status == "error" and path["stopReason"] == "error"
            ok(not path["completeCoverage"] and expected_failure_status in {"unknown", "error"} and stop_matches, "incomplete matching path differs from its taxonomy consequence")
        if trace_registry is not None:
            ok(path["traceDigest"] in trace_registry, "pattern path trace digest is dangling")
            trace = trace_registry[path["traceDigest"]]
            path_graphs[path["pathOrdinal"]] = validate_trace_semantics(trace, seed_signatures=referenced_signatures)
            ok(digest("k-in-k/event-trace/v1", trace) == path["traceDigest"], "resolved pattern path trace digest is invalid")
            ok(trace["pathIdentityDigest"] == path["pathIdentityDigest"], "pattern path identity differs from resolved trace")
            ok(trace["testId"] == result["testId"] and (path["pathKey"] is None or trace["pathKey"] == path["pathKey"]), "pattern path trace test/path identity mismatch")
            ok(trace["complete"] == path["completeCoverage"] and trace["stopReason"] == path["executionStopReason"], "pattern path completion/execution termination differs from resolved trace")
            ok(trace["executionTerminal"] == path["executionTerminal"], "pattern path terminal differs from resolved trace")
            if path["executionTerminal"] is not None and path["executionTerminal"]["kind"] == "semantic-crash":
                _, crashes = terminal_artifact_registry()
                crash = crashes[path["executionTerminal"]["artifact"]["digest"]]
                ok(crash["executionProfileDigest"] == result["inputs"]["executionProfileDigest"], "semantic crash execution profile differs from pattern inputs")
                ok(not failures, "semantic crash path carries a generic failure")
    if trace_registry is not None and not result["failures"]:
        complete_denotation: list[dict[str, Any]] = []
        for path in paths:
            trace = trace_registry[path["traceDigest"]]
            derived, indeterminate = derive_trace_plan_witnesses(result, plan, side_table, trace, path)
            expected_status = "match" if derived else "unknown" if indeterminate or not trace["complete"] else "no-match"
            ok(path["status"] == expected_status, "persisted path status differs from independently derived plan denotation")
            complete_denotation.extend(derived)
        has_stable = bool(complete_denotation) and all("replayKey" in witness for witness in complete_denotation)
        path_identities = {path["pathOrdinal"]: path["pathIdentityDigest"] for path in paths}
        complete_denotation.sort(key=witness_order_key if has_stable else lambda witness: unkeyed_witness_order_key(witness, path_identities))
        ok(result["witnesses"] == complete_denotation, "persisted witnesses/bindings/arms/path status differ from complete finite denotation")
        if complete_denotation and has_stable:
            ok(result.get("primaryWitness") == complete_denotation[0], "persisted primary witness differs from complete denotation order")
    top_dispositions = [consume_failure_disposition(failure, "pattern", taxonomy) for failure in result["failures"]]
    ok(all(disposition in {"unknown", "error"} for disposition in top_dispositions), "pattern test failure has a non-pattern taxonomy consequence")
    top_failure_status = "error" if "error" in top_dispositions else "unknown" if top_dispositions else None
    top_limit_failure = top_failure_status == "unknown"
    derived_components = [path["status"] for path in paths] + ([] if top_failure_status is None else [top_failure_status])
    derived_outcome = aggregate(derived_components, top_failure_status == "error")
    ok(result["outcome"] == derived_outcome, "pattern outcome does not derive from per-path evidence")
    derived_coverage = not result["failures"] and all(path["completeCoverage"] for path in paths)
    ok(result["completeCoverage"] == derived_coverage, "pattern coverage does not derive from per-path evidence")
    if result["outcome"] == "match":
        ok(bool(witnesses), "match must contain a witness")
    else:
        ok(not witnesses and "primaryWitness" not in result, "non-match result exposed a witness")
    if result["outcome"] == "no-match":
        ok(result["inputs"]["searchPolicy"] == "exhaustive" and result["completeCoverage"], "no-match requires exhaustive complete coverage")
    if result["outcome"] == "unknown":
        ok(not result["completeCoverage"] and (bool(paths) or top_limit_failure), "unknown lacks path or test-limit evidence")
    if result["outcome"] == "error":
        ok(not result["completeCoverage"] and bool(result["failures"]) and not top_limit_failure, "error result lacks a non-limit test failure")
    keyed = ["pathKey" in witness and "replayKey" in witness for witness in witnesses]
    ok(not keyed or all(keyed) or not any(keyed), "pattern result mixes keyed and unkeyed witnesses")
    has_stable_keys = bool(keyed) and all(keyed)
    if witnesses:
        ok(has_stable_keys == has_stable_path_keys, "witness key mode differs from its path records")
    path_identity_by_ordinal = {path["pathOrdinal"]: path["pathIdentityDigest"] for path in paths}
    canonical_witnesses = sorted(witnesses, key=witness_order_key if has_stable_keys else lambda witness: unkeyed_witness_order_key(witness, path_identity_by_ordinal))
    ok(witnesses == canonical_witnesses, "witness list is not canonical")
    normalized_witnesses = [canonical(witness) for witness in witnesses]
    ok(len(normalized_witnesses) == len(set(normalized_witnesses)), "pattern result has duplicate witnesses")
    if "primaryWitness" in result:
        ok(has_stable_keys and result["primaryWitness"] == witnesses[0], "primary witness requires stable keys and must be first")
    if witnesses and not has_stable_keys:
        ok("primaryWitness" not in result, "unkeyed witnesses cannot select a primary")
    for witness in witnesses:
        events = witness["events"]
        indices = witness["eventIndices"]
        ok(len(events) == len(indices), "witness event/index arity mismatch")
        ok(indices == sorted(set(indices)), "witness indices are not strictly increasing and unique")
        ok([event["index"] for event in events] == indices, "witness indices differ from embedded events")
        binding_names = [binding["name"] for binding in witness["bindings"]]
        expected_binding_names = [variable["name"] for variable in plan["variables"]]
        ok(binding_names == expected_binding_names, "witness bindings do not preserve the exact plan declaration interface order")
        witness_signatures, witness_variables = path_graphs.setdefault(witness["pathOrdinal"], (dict(referenced_signatures), {}))
        validate_portable_term(witness["pathPredicate"], witness_signatures, witness_variables)
        ok(witness["pathPredicate"]["sort"] == "Bool", "witness path predicate is not Bool-sorted")
        for event in events:
            for payload_term in event["payload"]:
                validate_portable_term(payload_term, witness_signatures, witness_variables)
        for binding in witness["bindings"]:
            validate_portable_term(binding["term"], witness_signatures, witness_variables)
        if has_stable_keys:
            replay_payload = {"testId": result["testId"], "pathKey": witness["pathKey"], "eventIndices": indices}
            ok(witness["replayKey"] == digest("k-in-k/witness-replay-key/v1", replay_payload), "witness replay key derivation")
        if witness["stopReason"] == "match-found":
            ok(result["inputs"]["searchPolicy"] == "existential-first" and not result["completeCoverage"], "match-found requires incomplete existential-first search")
        ok(witness["executionStopReason"] == ("query-satisfied" if witness["stopReason"] == "match-found" else witness["stopReason"]), "witness query stop and execution termination disagree")
        ok(witness["pathOrdinal"] < len(paths) and paths[witness["pathOrdinal"]]["status"] == "match", "witness does not resolve to a matching path")
        path = paths[witness["pathOrdinal"]]
        if has_stable_keys:
            ok(path["pathKey"] == witness["pathKey"], "witness path key differs from its path record")
        if trace_registry is not None:
            ok(path["traceDigest"] in trace_registry, "witness path trace digest is dangling")
            trace = trace_registry[path["traceDigest"]]
            ok(digest("k-in-k/event-trace/v1", trace) == path["traceDigest"], "resolved trace digest is invalid")
            ok(trace["testId"] == result["testId"] and (path["pathKey"] is None or trace["pathKey"] == path["pathKey"]), "resolved trace test/path identity mismatch")
            ok(trace["complete"] == path["completeCoverage"] and trace["stopReason"] == path["executionStopReason"], "path record differs from resolved trace completion")
            ok(trace["executionTerminal"] == path["executionTerminal"], "witness path terminal differs from resolved trace")
            ok(witness["executionStopReason"] == trace["stopReason"] and witness["stopReason"] == path["stopReason"] and witness["pathPredicate"] == trace["pathPredicate"], "witness predicate/query stop/execution stop differs from resolved trace")
            ok(all(index < len(trace["events"]) for index in indices) and events == [trace["events"][index] for index in indices], "witness events do not equal indexed trace events")
    if trace_registry is not None:
        trace_artifacts = [artifact["digest"] for artifact in result["inputs"]["artifacts"] if artifact["role"] == "event-trace"]
        path_trace_digests = [path["traceDigest"] for path in paths]
        ok(len(trace_artifacts) == len(set(trace_artifacts)) and set(trace_artifacts) == set(path_trace_digests), "pattern trace artifacts do not exactly cover path records")
    ok({path["pathOrdinal"] for path in paths if path["status"] == "match"} == {witness["pathOrdinal"] for witness in witnesses}, "matching paths and witness path coverage differ")


def pattern_oracle_projection(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "queryId": result["queryId"],
        "testId": result["testId"],
        "outcome": result["outcome"],
        "completeCoverage": result["completeCoverage"],
        "bounds": result["bounds"],
        "failures": result["failures"],
        "pathResults": [value_without(path, "traceDigest") for path in result["pathResults"]],
        "witnesses": result["witnesses"],
    }


def pattern_query_root(value: dict[str, Any]) -> dict[str, Any]:
    return {field: value[field] for field in ("patternSource", "patternPlan", "patternQuery")}


def flatten_mutation_pattern_queries(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    """Flatten test declaration order, then oracleIds selection order; retain duplicates."""
    return [deepcopy(root) for test in manifest["tests"] for root in test["patternQueries"]]


def validate_mutation_query_roots(manifest: dict[str, Any], catalog: dict[str, Any] | None = None) -> None:
    if "oracles" in manifest:  # synthetic pre-BAG-12 vectors only
        declarations = {oracle["oracleId"]: oracle for oracle in manifest["oracles"]}
        ok(len(declarations) == len(manifest["oracles"]), "duplicate mutation oracle declaration")
        for test in manifest["tests"]:
            selected = [pattern_query_root(declarations[oracle_id]) for oracle_id in test["oracleIds"] if declarations[oracle_id]["kind"] == "execution-pattern"]
            ok(test["patternQueries"] == selected, "mutation test invocation does not retain each oracle-local query root in oracle order")
        return
    ok(catalog is not None and manifest["artifactCatalogDigest"] == catalog["catalogId"], "typed mutation query roots lack their exact active catalog")
    by_key = {(entry["role"], entry["digest"]): entry for entry in catalog["entries"]}

    def resolved(role: str, identity: str, identity_field: str, domain: str) -> dict[str, Any]:
        entry = by_key.get((role, identity))
        ok(entry is not None and entry["availability"] == "bundled" and entry["contentModel"] == "canonical-json", f"typed mutation {role} root is absent from the active catalog")
        value = load(resolve_bundled(entry))
        ok(value[identity_field] == identity and value[identity_field] == digest(domain, value_without(value, identity_field)), f"typed mutation {role} active material identity drift")
        return value

    corpus = resolved("corpus-manifest", manifest["corpusManifestDigest"], "manifestId", "k-in-k/corpus-manifest/v1")
    observation = resolved("observation-manifest", corpus["observationManifestDigest"], "manifestId", "k-in-k/observation-manifest/v1")
    expected_vocabulary = digest("k-in-k/event-vocabulary/v1", observation["eventVocabulary"])
    ok(observation["eventVocabularyDigest"] == expected_vocabulary, "active corpus observation vocabulary identity drift")
    vocabularies = {"active-corpus": {"eventVocabularyDigest": expected_vocabulary, "constructors": observation["eventVocabulary"]}}
    available = {}
    for entry in catalog["entries"]:
        if entry["role"] == "oracle-declaration":
            declaration = resolved("oracle-declaration", entry["digest"], "declarationId", "k-in-k/oracle-declaration/v1")
            available[entry["digest"]] = declaration
    corpus_tests = {test["testId"]: test for test in corpus["tests"]}
    selected_declaration_ids: list[str] = []
    for test in manifest["tests"]:
        ok(test["testId"] in corpus_tests, "typed mutation test ID is absent from the selected corpus")
        corpus_test = corpus_tests[test["testId"]]
        ok(all(test[field] == corpus_test[field] for field in ("programDigest", "parserDigest", "startSymbol", "optionsDigest")), "typed mutation test roots differ from selected corpus")
        ok(test["boundsDigest"] == digest("k-in-k/bounds/v1", corpus["bounds"]), "typed mutation test bounds differ from selected corpus")
        invocation = {"testId": test["testId"], "programDigest": test["programDigest"], "parserDigest": test["parserDigest"], "startSymbol": test["startSymbol"], "optionsDigest": test["optionsDigest"], "bounds": corpus["bounds"], "executionMode": corpus["executionMode"], "solverProfileDigest": corpus["solverProfileDigest"], "executionProfileDigest": corpus["executionProfileDigest"], "compatibilityProfileDigest": corpus["compatibilityProfileDigest"], "observationManifestDigest": corpus["observationManifestDigest"], "patternQueries": test["patternQueries"]}
        ok(test["invocationDigest"] == digest("k-in-k/test-invocation/v1", invocation), "typed mutation test invocation is stale")
        ok(all(item["digest"] in available for item in test["oracleDeclarations"]), "typed mutation declaration is absent from active catalog")
        declarations = [available[item["digest"]] for item in test["oracleDeclarations"]]
        ok(all(declaration["testInvocationDigest"] == test["invocationDigest"] for declaration in declarations), "typed mutation declaration spans another test invocation")
        ok([declaration["slotOrdinal"] for declaration in declarations] == list(range(len(declarations))), "typed mutation declaration slot order/coverage drift")
        selected_declaration_ids.extend(item["digest"] for item in test["oracleDeclarations"])
        selected = [pattern_query_root(declaration["kindConfig"]) for declaration in declarations if declaration["kind"] == "execution-pattern"]
        ok(test["patternQueries"] == selected, "typed mutation test invocation does not retain each declaration-local query root in slot order")
        for root in selected:
            resolve_pattern_query_root(root, catalog, vocabularies, expected_vocabulary)
    ok(len(selected_declaration_ids) == len(set(selected_declaration_ids)) and set(selected_declaration_ids) == set(available), "typed mutation declarations do not exactly cover the active catalog registry")


def validate_corpus_result_semantics(manifest: dict[str, Any], result: dict[str, Any], pattern_registry: dict[str, dict[str, Any]] | None = None, taxonomy: dict[str, Any] | None = None) -> None:
    reject_baseline_mismatch(result["failures"], "corpus pattern campaign failures")
    ok(result["manifestDigest"] == manifest["manifestId"], "corpus result references another manifest")
    ok(result["resultId"] == digest("k-in-k/corpus-result/v1", value_without(result, "resultId")), "corpus result ID derivation")
    expected_test_ids = [test["testId"] for test in manifest["tests"]]
    actual_test_ids = [component["testId"] for component in result["components"]]
    ok(actual_test_ids == expected_test_ids, "corpus components must retain manifest order and coverage")
    statuses = [component["status"] for component in result["components"]]
    expected_counts = {
        "match": statuses.count("match"),
        "noMatch": statuses.count("no-match"),
        "unknown": statuses.count("unknown"),
        "error": statuses.count("error"),
        "skipped": statuses.count("skipped"),
    }
    ok(result["counts"] == expected_counts, "corpus counts do not derive from components")
    global_failure = bool(result["failures"])
    if global_failure:
        ok(all(consume_failure_disposition(failure, "corpus", taxonomy) == "error" for failure in result["failures"]), "corpus global failure does not derive shared-setup error from the taxonomy")
        ok(all(component["status"] == "skipped" and component["skipReason"] == "shared-setup-failed" for component in result["components"]), "shared setup failure did not stop before every test")
    else:
        ok(all(component["skipReason"] != "shared-setup-failed" for component in result["components"]), "shared-setup skip lacks a global failure")
    early_stop = manifest["aggregation"]["question"] == "corpus-exists" and manifest["aggregation"]["earlyStopAfterMatch"]
    match_indices = [index for index, component in enumerate(result["components"]) if component["status"] == "match"]
    if not global_failure and early_stop and match_indices:
        first_match = match_indices[0]
        ok(all(component["status"] != "skipped" for component in result["components"][:first_match + 1]), "corpus stopped before its first conclusive match")
        ok(all(component["status"] == "skipped" and component["skipReason"] == "corpus-match-found" for component in result["components"][first_match + 1:]), "early corpus match did not skip exactly the remaining tests")
    elif not global_failure:
        ok(all(component["status"] != "skipped" for component in result["components"]), "corpus skipped tests without a legal early stop")
    for component in result["components"]:
        reject_baseline_mismatch(component["failures"], "corpus pattern test failures")
        ok([path["pathOrdinal"] for path in component["pathResults"]] == list(range(len(component["pathResults"]))), "corpus path ordinals are not contiguous")
        path_keys = [path["pathKey"] for path in component["pathResults"] if path["pathKey"] is not None]
        ok(len(path_keys) == len(set(path_keys)), "duplicate corpus path key")
        matching_ordinals = [path["pathOrdinal"] for path in component["pathResults"] if path["status"] == "match"]
        matching_keys = [path["pathKey"] for path in component["pathResults"] if path["status"] == "match" and path["pathKey"] is not None]
        ok(component["matchingPathOrdinals"] == matching_ordinals and component["matchingPathKeys"] == matching_keys, "matching path indexes are inconsistent")
        if component["status"] == "skipped":
            ok(component["patternResultDigest"] is None and not component["pathResults"] and not component["failures"] and component["skipReason"] is not None, "skipped test must be explicit and artifact-free")
        elif component["failures"]:
            ok(all(failure["scope"] == "test" for failure in component["failures"]), "component failure does not have test scope")
            dispositions = [consume_failure_disposition(failure, "corpus", taxonomy) for failure in component["failures"]]
            ok(all(disposition in {"unknown", "error"} for disposition in dispositions), "component failure has a non-pattern taxonomy consequence")
            expected_status = "error" if "error" in dispositions else "unknown"
            ok(component["status"] == expected_status and component["patternResultDigest"] is not None and not component["pathResults"] and component["skipReason"] is None, "test-level failure status/digest does not derive from its taxonomy")
        else:
            ok(component["patternResultDigest"] is not None and component["pathResults"] and component["skipReason"] is None, "executed test has invalid digest/skip relation")
            derived_component = aggregate([path["status"] for path in component["pathResults"]], False)
            ok(component["status"] == derived_component, "component status does not derive from path results")
        for path in component["pathResults"]:
            reject_baseline_mismatch(path["failures"], "corpus pattern path failures")
            ok(all(failure["scope"] == "path" for failure in path["failures"]), "path failure does not have path scope")
            ok(path["executionStopReason"] == ("query-satisfied" if path["stopReason"] == "match-found" else path["stopReason"]), "corpus query stop and execution termination disagree")
            dispositions = [consume_failure_disposition(failure, "corpus", taxonomy) for failure in path["failures"]]
            if path["status"] == "match":
                if path["completeCoverage"]:
                    ok(path["stopReason"] in ("terminal", "stuck") and not path["failures"], "complete matching path lacks an exhaustive stop")
                elif path["stopReason"] == "match-found":
                    ok(not path["failures"], "existential match stop retained a failure")
                else:
                    expected_failure_status = dispositions[0] if dispositions and len(set(dispositions)) == 1 else None
                    stop_matches = expected_failure_status == "unknown" and any(failure["classification"] == path["stopReason"] for failure in path["failures"]) or expected_failure_status == "error" and path["stopReason"] == "error"
                    ok(expected_failure_status in {"unknown", "error"} and stop_matches, "incomplete matching path differs from its taxonomy consequence")
            elif path["status"] == "no-match":
                ok(path["completeCoverage"] and path["stopReason"] in ("terminal", "stuck") and not path["failures"], "path no-match lacks exhaustive evidence")
            elif path["status"] == "unknown":
                ok(not path["completeCoverage"] and dispositions and all(disposition == "unknown" for disposition in dispositions), "unknown path differs from its taxonomy consequence")
                ok(any(failure["classification"] == path["stopReason"] for failure in path["failures"]), "unknown path stop reason differs from its failure")
            elif path["status"] == "error":
                ok(not path["completeCoverage"] and path["stopReason"] == "error" and dispositions and all(disposition == "error" for disposition in dispositions), "error path differs from its taxonomy consequence")
            if path["stopReason"] == "match-found":
                ok(path["status"] == "match" and not path["completeCoverage"], "match-found path claimed exhaustive coverage")
        if pattern_registry is not None and component["status"] != "skipped":
            ok(component["patternResultDigest"] in pattern_registry, "corpus component pattern result is dangling")
            pattern = pattern_registry[component["patternResultDigest"]]
            test = next(test for test in manifest["tests"] if test["testId"] == component["testId"])
            ok(pattern["testId"] == component["testId"] and pattern["outcome"] == component["status"], "corpus component identity/status differs from pattern result")
            ok(pattern["bounds"] == manifest["bounds"], "corpus component pattern bounds differ from manifest")
            inputs = pattern["inputs"]
            ok(inputs["definitionDigest"] == manifest["definitionDigest"] and inputs["observationManifestDigest"] == manifest["observationManifestDigest"] and pattern_query_root(inputs) == test["patternQueries"][0], "corpus component pattern inputs differ from the test's primary ordered query selection")
            ok(inputs["programDigest"] == test["programDigest"] and inputs["parserDigest"] == test["parserDigest"] and inputs["startSymbol"] == test["startSymbol"] and inputs["optionsDigest"] == test["optionsDigest"] and inputs["executionMode"] == manifest["executionMode"] and inputs["executionProfileDigest"] == manifest["executionProfileDigest"] and inputs["solverProfileDigest"] == manifest["solverProfileDigest"] and inputs["compatibilityProfileDigest"] == manifest["compatibilityProfileDigest"], "corpus component execution inputs differ from test/manifest")
            ok(component["failures"] == pattern["failures"] and len(component["pathResults"]) == len(pattern["pathResults"]), "corpus component failure/path coverage differs from pattern result")
            for corpus_path, pattern_path in zip(component["pathResults"], pattern["pathResults"]):
                ok(corpus_path["patternResultDigest"] == pattern["resultId"], "corpus path references another pattern result")
                ok({key: corpus_path[key] for key in ("pathOrdinal", "pathKey", "pathIdentityDigest", "status", "completeCoverage", "stopReason", "executionStopReason", "failures")} == {key: pattern_path[key] for key in ("pathOrdinal", "pathKey", "pathIdentityDigest", "status", "completeCoverage", "stopReason", "executionStopReason", "failures")}, "corpus path evidence differs from resolved pattern path")
    derived = aggregate([status for status in statuses if status != "skipped"], bool(result["failures"]))
    ok(result["outcome"] == derived, "corpus outcome does not derive from components")
    expected_complete = not result["failures"] and all(component["status"] != "skipped" and not component["failures"] and bool(component["pathResults"]) and all(path["completeCoverage"] for path in component["pathResults"]) for component in result["components"])
    ok(result["completeCoverage"] == expected_complete, "corpus coverage flag is inconsistent")
    ok(all(failure["scope"] == "campaign" for failure in result["failures"]), "top-level corpus failure is not shared/global")


def replay_invocation_payload(replay: dict[str, Any]) -> dict[str, Any]:
    payload = {key: deepcopy(value) for key, value in replay.items() if key not in {"replayId", "invocationDigest", "expectedResultDigest"}}
    payload["steps"] = [{key: deepcopy(value) for key, value in step.items() if key != "expectedArtifacts"} for step in replay["steps"]]
    return payload


def refresh_replay_ids(replay: dict[str, Any]) -> None:
    replay["invocationDigest"] = digest("k-in-k/replay-invocation/v1", replay_invocation_payload(replay))
    replay["replayId"] = digest("k-in-k/replay-manifest/v1", value_without(replay, "replayId"))


def validate_replay_semantics(replay: dict[str, Any]) -> None:
    ok(replay["invocationDigest"] == digest("k-in-k/replay-invocation/v1", replay_invocation_payload(replay)), "replay invocation digest derivation")
    ok(replay["replayId"] == digest("k-in-k/replay-manifest/v1", value_without(replay, "replayId")), "replay manifest ID derivation")
    ok([step["ordinal"] for step in replay["steps"]] == list(range(len(replay["steps"]))), "replay steps are not contiguous")
    ok(all(step["optionsDigest"] == replay["optionsDigest"] for step in replay["steps"]), "replay step options differ from invocation options")
    artifacts = replay["artifacts"]
    artifact_keys = [(artifact["role"], artifact["digest"]) for artifact in artifacts]
    ok(len(artifact_keys) == len(set(artifact_keys)), "replay has duplicate logical artifacts")
    artifacts_by_role: dict[str, list[dict[str, Any]]] = {}
    for artifact in artifacts:
        artifacts_by_role.setdefault(artifact["role"], []).append(artifact)
    if replay["kind"] == "pattern-query":
        ok(all(replay[field] is not None for field in ("programDigest", "parserDigest", "startSymbol", "testId", "queryId", "executionMode", "observerDigest", "observationManifestDigest", "patternSource", "patternPlan", "patternQuery")), "pattern replay lacks complete source/plan/query execution identity")
        ok(replay["queryId"] == replay["patternQuery"]["digest"], "pattern replay query ID differs from its typed query key")
        ok([step["role"] for step in replay["steps"]] == ["ingest", "transform", "execute", "match"], "pattern replay has an invalid step sequence")
        ok([([item["role"] for item in step["inputArtifacts"]], [item["role"] for item in step["expectedArtifacts"]]) for step in replay["steps"]] == [(["definition"], ["definition"]), (["definition", "transformation"], ["instrumented-definition"]), (["instrumented-definition", "program"], ["event-trace"]), (["event-trace", "pattern-source", "pattern-plan", "pattern-query"], ["pattern-result"])], "pattern replay roles do not type the required query dataflow")
        ok(set(artifacts_by_role) == {"program", "pattern-source", "pattern-plan", "pattern-query"} and all(len(items) == 1 for items in artifacts_by_role.values()), "pattern replay lacks singleton program/source/plan/query artifacts")
        ok(artifacts_by_role["program"][0]["digest"] == replay["programDigest"], "pattern replay program artifact mismatch")
        ok(all(artifacts_by_role[replay[field]["role"]][0] == replay[field] for field in ("patternSource", "patternPlan", "patternQuery")), "pattern replay typed query artifacts mismatch")
        ok(replay["steps"][0]["inputArtifacts"] == [{"role": "definition", "digest": replay["definitionDigest"]}], "pattern ingest does not consume exactly the definition")
        ok(replay["steps"][1]["inputArtifacts"] == [{"role": "definition", "digest": replay["definitionDigest"]}, *({"role": "transformation", "digest": item} for item in replay["transformationDigests"])], "pattern transform inputs differ from definition/transformation chain")
        ok(replay["steps"][2]["inputArtifacts"] == [replay["steps"][1]["expectedArtifacts"][0], {"role": "program", "digest": replay["programDigest"]}], "pattern execute inputs are not transformed definition plus program")
        ok(replay["steps"][3]["inputArtifacts"] == [replay["steps"][2]["expectedArtifacts"][0], replay["patternSource"], replay["patternPlan"], replay["patternQuery"]], "pattern match inputs are not trace plus exact source/plan/query")
        catalogs = [load(FIXTURES / name) for name in ("artifact-catalog.json", "execution-artifact-catalog.json")]
        matches = [item for item in catalogs if item["catalogId"] == replay["artifactCatalogDigest"]]
        ok(len(matches) == 1, "pattern replay artifact catalog is dangling or ambiguous")
        catalog = matches[0]
        ok(replay["artifactCatalogDigest"] == catalog["catalogId"], "pattern replay query resolution used another catalog")
        resolve_pattern_query_root(pattern_query_root(replay), catalog, load(VECTORS / "execution-pattern-vectors.json")["eventVocabularies"], observation_vocabulary_digest(replay["observationManifestDigest"]))
    else:
        ok(all(replay[field] is None for field in ("programDigest", "parserDigest", "startSymbol", "testId", "queryId", "executionMode", "observerDigest", "observationManifestDigest", "patternSource", "patternPlan", "patternQuery", "solverProfileDigest")) and replay["searchPolicy"] == "exhaustive", "patch-only mutation replay carries query/search identity")
        ok([step["role"] for step in replay["steps"]] == ["ingest", "transform", "validate"], "mutation replay has an invalid step sequence")
        ok([([item["role"] for item in step["inputArtifacts"]], [item["role"] for item in step["expectedArtifacts"]]) for step in replay["steps"]] == [(["definition"], ["definition"]), (["definition", "patch"], ["mutant-definition", "structural-diff"]), (["mutant-definition", "structural-diff"], ["mutant-definition", "structural-diff"])], "mutation replay roles do not type the required dataflow")
        ok(set(artifacts_by_role) == {"patch", "structural-diff"} and all(len(items) == 1 for items in artifacts_by_role.values()), "mutation replay lacks singleton patch/diff artifacts")
        ok(artifacts_by_role["patch"][0]["digest"] == replay["mutation"]["patchId"], "mutation replay patch artifact mismatch")
        ok(replay["expectedResultDigest"] == replay["mutation"]["outputDefinitionDigest"], "mutation replay result is not its declared output definition")
        ok(replay["steps"][0]["inputArtifacts"] == [{"role": "definition", "digest": replay["definitionDigest"]}], "mutation ingest does not consume exactly the baseline definition")
        diff_digest = artifacts_by_role["structural-diff"][0]["digest"]
        ok(replay["steps"][1]["inputArtifacts"] == [{"role": "definition", "digest": replay["definitionDigest"]}, {"role": "patch", "digest": replay["mutation"]["patchId"]}] and replay["steps"][1]["expectedArtifacts"] == [{"role": "mutant-definition", "digest": replay["mutation"]["outputDefinitionDigest"]}, {"role": "structural-diff", "digest": diff_digest}], "mutation transform flow differs from baseline+patch to output+diff")
        ok(replay["steps"][2]["inputArtifacts"] == [{"role": "mutant-definition", "digest": replay["mutation"]["outputDefinitionDigest"]}, {"role": "structural-diff", "digest": diff_digest}] and replay["steps"][2]["expectedArtifacts"] == replay["steps"][2]["inputArtifacts"], "mutation validation does not certify the declared output+diff")
    roots = {("definition", replay["definitionDigest"]), ("compatibility-profile", replay["compatibilityProfileDigest"]), ("execution-profile", replay["executionProfileDigest"]), ("options", replay["optionsDigest"]), *(("transformation", item) for item in replay["transformationDigests"]), *((artifact["role"], artifact["digest"]) for artifact in artifacts)}
    roots.update((role, item) for role, item in (("observer", replay["observerDigest"]), ("observation-manifest", replay["observationManifestDigest"]), ("program", replay["programDigest"]), ("parser", replay["parserDigest"]), ("solver-profile", replay["solverProfileDigest"])) if item is not None)
    roots.update((replay[field]["role"], replay[field]["digest"]) for field in ("patternSource", "patternPlan", "patternQuery") if replay[field] is not None)
    produced: set[tuple[str, str]] = set()
    for index, step in enumerate(replay["steps"]):
        inputs = [(item["role"], item["digest"]) for item in step["inputArtifacts"]]
        outputs = [(item["role"], item["digest"]) for item in step["expectedArtifacts"]]
        ok(len(inputs) == len(set(inputs)) and len(outputs) == len(set(outputs)), "replay step has duplicate input/output identities")
        ok(all(item in roots or item in produced for item in inputs), "replay step input is neither a root nor a prior output")
        repeated = produced & set(outputs)
        ok(repeated <= set(inputs), "replay step ambiguously reproduces an earlier artifact")
        produced.update(outputs)
        if index < len(replay["steps"]) - 1:
            later_inputs = {(item["role"], item["digest"]) for later in replay["steps"][index + 1:] for item in later["inputArtifacts"]}
            ok(all(output in later_inputs or output in roots for output in outputs), "replay produced a dangling intermediate artifact")
    ok(replay["expectedResultDigest"] in [item["digest"] for item in replay["steps"][-1]["expectedArtifacts"]], "replay result is not produced by final step")


def validate_corpus_manifest_semantics(manifest: dict[str, Any], catalog: dict[str, Any] | None = None) -> None:
    ok(manifest["manifestId"] == digest("k-in-k/corpus-manifest/v1", value_without(manifest, "manifestId")), "corpus manifest ID derivation")
    test_ids = [test["testId"] for test in manifest["tests"]]
    ok(test_ids and len(test_ids) == len(set(test_ids)), "corpus manifest has empty/duplicate test identity")
    selected = [root for test in manifest["tests"] for root in test["patternQueries"]]
    ok(manifest["patternQueries"] == selected, "corpus ordered query roots do not exactly flatten test order then per-test oracle-selection order")
    if catalog is not None:
        ok(manifest["artifactCatalogDigest"] == catalog["catalogId"], "corpus query selections resolve through another catalog")
        vocabularies = load(VECTORS / "execution-pattern-vectors.json")["eventVocabularies"]
        for root in selected:
            resolve_pattern_query_root(root, catalog, vocabularies, observation_vocabulary_digest(manifest["observationManifestDigest"]))


def validate_operator_declaration(operator: dict[str, Any]) -> None:
    ok(operator["operatorDigest"] == digest("k-in-k/mutation-operator/v1", value_without(operator, "operatorDigest")), "mutation operator digest derivation")
    ok(operator["sentenceKinds"] == sorted(set(operator["sentenceKinds"])), "mutation operator sentence kinds are not canonical")
    template_roles = operator["patchTemplateRoles"]
    role_names = [role["name"] for role in template_roles]
    ok(role_names == sorted(role_names) and len(role_names) == len(set(role_names)), "mutation patch-template roles are duplicate or noncanonical")
    ok(all(len(role["sourceSelectorRoles"]) == len(set(role["sourceSelectorRoles"])) for role in template_roles), "mutation patch-template source roles are duplicate")
    ok((operator["policy"] == "exact") == (operator["expectedTupleCount"] is not None), "mutation operator policy/count relation")
    ok(operator["expectedTupleArity"] >= 1 and operator["candidateCap"] >= 1, "mutation operator has a nonpositive tuple arity/cap")
    if operator["policy"] in ("each", "all-matches"):
        ok(operator["joinDigest"] is None and operator["expectedTupleArity"] == 1, "unary mutation policy requires a null join")
    if operator["policy"] == "tuple-each":
        ok(operator["joinDigest"] is not None and operator["expectedTupleArity"] >= 2, "tuple-each requires a non-null multi-role join")


def validate_patch_template_interface(operator: dict[str, Any], selector: dict[str, Any]) -> None:
    selector_roles = [clause["role"] for clause in selector["clauses"]]
    template_source_roles = [source_role for template_role in operator["patchTemplateRoles"] for source_role in template_role["sourceSelectorRoles"]]
    ok(set(template_source_roles) == set(selector_roles), "patch-template source roles do not exactly cover the selector interface")
    for template_role in operator["patchTemplateRoles"]:
        declared_sources = template_role["sourceSelectorRoles"]
        ok(declared_sources == [role for role in selector_roles if role in set(declared_sources)], "patch-template source roles do not follow selector declaration order")


def canonical_discovery_bindings(site_tuple: list[str], sites_by_id: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    by_name: dict[str, dict[str, Any]] = {}
    for site_id in site_tuple:
        for binding in sites_by_id[site_id]["bindings"]:
            previous = by_name.get(binding["name"])
            ok(previous is None or previous == binding, "joined discovery tuple has conflicting same-named bindings")
            by_name[binding["name"]] = binding
    return [by_name[name] for name in sorted(by_name)]


def mutation_instance_payload(operator: dict[str, Any], baseline_digest: str, policy: str, origin: dict[str, Any], patch_id: str) -> dict[str, Any]:
    return {
        "operatorId": operator["id"], "operatorVersion": operator["version"],
        "baselineDefinitionDigest": baseline_digest, "policy": policy,
        "siteTuple": origin["siteTuple"], "discoveryTuples": origin["discoveryTuples"],
        "patchId": patch_id, "editReceipts": origin["editReceipts"],
    }


def validate_edit_receipts(operator: dict[str, Any], declaration: dict[str, Any], origin: dict[str, Any], edits: list[dict[str, Any]], sites_by_id: dict[str, dict[str, Any]]) -> None:
    receipts = origin["editReceipts"]
    ok([receipt["editId"] for receipt in receipts] == [edit["editId"] for edit in edits], "mutation edit receipts do not exactly follow patch edit order")
    template_roles = {role["name"]: role for role in declaration["patchTemplateRoles"]}
    ok(len(template_roles) == len(declaration["patchTemplateRoles"]), "duplicate mutation patch-template role")
    for receipt, edit in zip(receipts, edits):
        ok(receipt["operator"] == operator, "mutation edit receipt operator drift")
        ok(receipt["patchTemplateDigest"] == declaration["patchTemplateDigest"], "mutation edit receipt patch-template drift")
        ok(receipt["templateRole"] in template_roles, "mutation edit receipt uses an undeclared template role")
        template_role = template_roles[receipt["templateRole"]]
        ok(template_role["operation"] == edit["operation"], "mutation edit receipt operation differs from its template role")
        sources = receipt["sources"]
        source_positions: list[tuple[int, int]] = []
        source_roles: list[str] = []
        cited_lineages: set[str] = set()
        seen_sources: set[tuple[int, str]] = set()
        for source in sources:
            tuple_index = source["discoveryTupleIndex"]
            ok(tuple_index < len(origin["discoveryTuples"]), "mutation edit receipt discovery-tuple index is out of range")
            discovery_tuple = origin["discoveryTuples"][tuple_index]
            ok(source["siteId"] in discovery_tuple["siteTuple"], "mutation edit receipt site is not in its indexed discovery tuple")
            site_position = discovery_tuple["siteTuple"].index(source["siteId"])
            source_positions.append((tuple_index, site_position))
            ok((tuple_index, source["siteId"]) not in seen_sources, "mutation edit receipt repeats a source")
            seen_sources.add((tuple_index, source["siteId"]))
            site = sites_by_id[source["siteId"]]
            ok(source["siteId"] in origin["siteTuple"] and source["selectorRole"] == site["selectorRole"], "mutation edit receipt source role/site is outside its origin")
            ok(source["tupleBindings"] == discovery_tuple["bindings"], "mutation edit receipt tuple bindings drift")
            source_roles.append(source["selectorRole"])
            cited_lineages.add(site["sentenceLineage"])
        ok(source_positions == sorted(source_positions), "mutation edit receipt sources are not canonical")
        ok(source_roles == template_role["sourceSelectorRoles"], "mutation edit receipt sources differ from its template-role interface")
        if edit["operation"] == "insert-sentence":
            position = edit["position"]
            ok(position["kind"] in ("before-lineage", "after-lineage"), "module-boundary insertion has no provenance-complete campaign receipt")
            ok(position["anchorLineage"] in cited_lineages, "mutation insertion receipt does not authorize its anchor lineage")
        else:
            ok(edit["targetLineage"] in cited_lineages, "mutation edit receipt does not authorize its target lineage")


def validate_policy_registry_shape(site_registry: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> None:
    ok(site_registry["registryId"] == digest("k-in-k/mutation-site-registry/v1", value_without(site_registry, "registryId")), "mutation site registry ID derivation")
    discovery = site_registry["discovery"]
    ok(discovery["exhaustive"] == (discovery["failure"] is None), "mutation discovery exhaustion/failure relation")
    if discovery["failure"] is not None:
        failure = discovery["failure"]
        ok((failure["stage"], failure["classification"], failure["scope"]) == ("selection", "incomplete-generation", "campaign") and consume_failure_disposition(failure, "policy-registry", taxonomy) == "incomplete-generation", "non-exhaustive discovery differs from its exact taxonomy consequence")
    sites = site_registry["sites"]
    site_ids = [site["siteId"] for site in sites]
    ok(len(site_ids) == len(set(site_ids)), "mutation site registry contains duplicate sites")
    sites_by_id = {site["siteId"]: site for site in sites}
    for site in sites:
        binding_names = [binding["name"] for binding in site["bindings"]]
        ok(binding_names == sorted(binding_names) and len(binding_names) == len(set(binding_names)), "mutation site bindings are not canonical and unique")
    tuples = site_registry["tuples"]
    ok(len({canonical(site_tuple) for site_tuple in tuples}) == len(tuples), "mutation registry contains duplicate discovery tuples")
    ok(all(site_tuple and len(site_tuple) == len(set(site_tuple)) and set(site_tuple) <= set(site_ids) for site_tuple in tuples), "mutation discovery tuple is empty, duplicate, or dangling")
    join = site_registry["join"]
    if join is None:
        ok(tuples == [[site_id] for site_id in site_ids], "null join does not contain exactly one singleton tuple per discovered site")
    else:
        roles = join["orderedRoles"]
        ok(len(roles) == len(set(roles)), "mutation join roles are duplicate")
        ok(all(len(site_tuple) == len(roles) and [sites_by_id[site_id]["selectorRole"] for site_id in site_tuple] == roles for site_tuple in tuples), "mutation joined tuple does not follow declared role order")
        site_rank = {site_id: index for index, site_id in enumerate(site_ids)}
        tuple_keys = [tuple(site_rank[site_id] for site_id in site_tuple) for site_tuple in tuples]
        ok(tuple_keys == sorted(tuple_keys), "mutation joined tuples are not in canonical registry order")


def derive_policy_instances(operator: dict[str, Any], site_registry: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> dict[str, Any]:
    """Derive the only permitted instance prefix from discovery and policy."""
    validate_operator_declaration(operator)
    validate_policy_registry_shape(site_registry, taxonomy)
    join = site_registry["join"]
    tuples = site_registry["tuples"]
    arity = operator["expectedTupleArity"]
    failure: str | None = None
    if operator["policy"] in ("each", "all-matches") and join is not None:
        failure = "invalid-join"
    elif operator["policy"] == "tuple-each" and join is None:
        failure = "invalid-join"
    elif any(len(site_tuple) != arity for site_tuple in tuples):
        failure = "invalid-join"
    elif join is None and arity != 1:
        failure = "invalid-join"
    elif join is not None and arity != len(join["orderedRoles"]):
        failure = "invalid-join"
    elif operator["policy"] == "exact" and site_registry["discovery"]["exhaustive"] and len(tuples) != operator["expectedTupleCount"]:
        failure = "cardinality-mismatch"
    sites_by_id = {site["siteId"]: site for site in site_registry["sites"]}
    derived: list[dict[str, Any]] = []
    if failure is None:
        if operator["policy"] == "all-matches":
            if tuples:
                derived.append({
                    "siteTuple": [site_tuple[0] for site_tuple in tuples],
                    "discoveryTuples": [{"siteTuple": site_tuple, "bindings": canonical_discovery_bindings(site_tuple, sites_by_id)} for site_tuple in tuples],
                })
        else:
            derived = [{
                "siteTuple": site_tuple,
                "discoveryTuples": [{"siteTuple": site_tuple, "bindings": canonical_discovery_bindings(site_tuple, sites_by_id)}],
            } for site_tuple in tuples]
    retained = derived[:operator["candidateCap"]]
    discovery_failure = site_registry["discovery"]["failure"]
    discovery_disposition = None if discovery_failure is None else consume_failure_disposition(discovery_failure, "policy-registry", taxonomy)
    complete = failure is None and discovery_disposition is None and len(retained) == len(derived)
    return {"selectionFailure": failure, "discoveryDisposition": discovery_disposition, "derived": derived, "retained": retained, "complete": complete}


def artifact_role_specs() -> dict[str, dict[str, Any]]:
    registry = load(PACKAGE / "artifact-role-specs.json")
    schema_path = SCHEMAS / "artifact-role-specs.schema.json"
    schema = load(schema_path)
    validate_schema(registry, schema, schema_path, schema)
    specs = {item["role"]: item for item in registry["specs"]}
    ok(len(specs) == len(registry["specs"]), "artifact role registry contains a duplicate role")
    common_roles = set(load(SCHEMAS / "common.schema.json")["$defs"]["artifactRole"]["enum"])
    ok(set(specs) == common_roles, "schema role vocabulary and role-spec registry differ")
    ok(all((item["contentModel"] == "canonical-json") == (item["schema"] is not None) for item in specs.values()), "structured role lacks a schema or opaque role names one")
    for spec in specs.values():
        projection = spec["projection"]
        kind = projection["kind"]
        if spec["contentModel"] == "opaque-bytes":
            ok(kind == "opaque-envelope" and spec["selfIdField"] is None, "opaque role has a structured projection or self ID")
        else:
            ok(kind != "opaque-envelope", "canonical-JSON role uses an opaque projection")
        ok((kind == "field") == ("field" in projection), "field projection has the wrong parameters")
        ok((kind == "select-fields") == ("fields" in projection), "selected-fields projection has the wrong parameters")
        if kind == "without-field":
            ok(spec["selfIdField"] is not None, "without-field projection has no self ID field")
        if kind == "definition-summary":
            ok(spec["role"] in {"definition", "instrumented-definition", "mutant-definition"} and spec["selfIdField"] == "definitionDigest", "definition summary projection is assigned to an incompatible role")
    return specs


def opaque_artifact_digest(role: str, media_type: str, content_sha256: str) -> str:
    return digest("k-in-k/opaque-artifact/v1", {"role": role, "mediaType": media_type, "contentSha256": content_sha256})


def definition_summary_payload(value: dict[str, Any]) -> dict[str, Any]:
    module_payloads = [{"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": [sentence["provenance"]["contentFingerprint"] for sentence in module["sentences"]]} for module in value["modules"]]
    return {"schemaVersion": value["schemaVersion"], "representation": value["representation"], "baselineFamilyId": value["baselineFamilyId"], "modules": module_payloads}


def semantic_artifact_digest(role: str, value: Any, specs: dict[str, dict[str, Any]] | None = None) -> str:
    specs = artifact_role_specs() if specs is None else specs
    spec = specs[role]
    projection = spec["projection"]
    kind = projection["kind"]
    ok(spec["contentModel"] == "canonical-json" and kind != "opaque-envelope", "structured semantic digest requested for an opaque role")
    if kind == "complete":
        payload = value
    elif kind == "definition-summary":
        payload = definition_summary_payload(value)
    elif kind == "without-field":
        payload = value_without(value, spec["selfIdField"])
    elif kind == "field":
        payload = value[projection["field"]]
    elif kind == "select-fields":
        payload = {field: value[field] for field in projection["fields"]}
    else:  # role-spec validation closes this branch
        raise AssertionError(f"unknown structured semantic projection {kind}")
    return digest(spec["digestDomain"], payload)


def normalized_locator(entry: dict[str, Any]) -> tuple[str, str]:
    scheme, separator, tail = entry["logicalPath"].partition("://")
    ok(bool(separator) and scheme in {"repo", "artifact"}, "artifact locator has an unknown scheme")
    segments = tail.split("/")
    ok(bool(tail) and all(segments) and all(segment not in {".", ".."} for segment in segments), "artifact locator has an empty or traversal segment")
    ok(all(all(0x20 <= ord(character) < 0x7f for character in segment) for segment in segments), "artifact locator segment is not printable ASCII")
    ok("\\" not in tail and "%" not in tail and not tail.startswith("/"), "artifact locator uses an alternate separator, escape, or absolute tail")
    expected = ("repo-v1", "bundled") if scheme == "repo" else ("rust-artifact-store-v1", "external-required")
    ok((entry["resolverId"], entry["availability"]) == expected, "artifact resolver/scheme/availability combination is invalid")
    return scheme, tail


def resolve_bundled(entry: dict[str, Any]) -> Path:
    scheme, tail = normalized_locator(entry)
    ok(scheme == "repo", "zero-backend resolver attempted to dereference an external artifact")
    real_root = ROOT.resolve()
    try:
        target = (ROOT / tail).resolve(strict=True)
    except (FileNotFoundError, RuntimeError) as error:
        raise AssertionError("bundled artifact target cannot be resolved") from error
    ok(target.is_file() and target.is_relative_to(real_root), "bundled artifact is missing, non-regular, or escapes the repository")
    return target


def verify_catalog_entry_bytes(entry: dict[str, Any], specs: dict[str, dict[str, Any]]) -> None:
    target = resolve_bundled(entry)
    raw = target.read_bytes()
    verify_artifact_bytes(entry, raw, specs)


def verify_artifact_bytes(entry: dict[str, Any], raw: bytes, specs: dict[str, dict[str, Any]]) -> None:
    actual_content_hash = hashlib.sha256(raw).hexdigest()
    ok(actual_content_hash == entry["contentSha256"], "bundled artifact exact-byte hash drift")
    if entry["contentModel"] == "opaque-bytes":
        ok(entry["digest"] == opaque_artifact_digest(entry["role"], entry["mediaType"], actual_content_hash), "opaque artifact semantic envelope drift")
        return
    try:
        text = raw.decode("utf-8", errors="strict")
        value = json.loads(text, object_pairs_hook=unique_object)
    except (UnicodeDecodeError, ValueError, json.JSONDecodeError) as error:
        raise AssertionError("canonical artifact bytes do not decode as unique-key UTF-8 JSON") from error
    validate_portable_json(value, entry["logicalPath"])
    ok(raw == canonical(value).encode("utf-8"), "canonical artifact uses a noncanonical but decodable byte representation")
    schema_reference = specs[entry["role"]]["schema"]
    file_name, _, fragment = schema_reference.partition("#")
    schema_path = SCHEMAS / file_name
    schema_root = load(schema_path)
    schema = pointer(schema_root, f"#{fragment}" if fragment else "#")
    validate_schema(value, schema, schema_path, schema_root)
    semantic_digest = semantic_artifact_digest(entry["role"], value, specs)
    ok(entry["digest"] == semantic_digest, "canonical artifact resolves to another semantic identity")
    self_id_field = specs[entry["role"]]["selfIdField"]
    if self_id_field is not None:
        ok(value[self_id_field] == semantic_digest, "canonical artifact self ID differs from its semantic identity")


def validate_artifact_catalog(catalog: dict[str, Any]) -> None:
    specs = artifact_role_specs()
    ok(catalog["catalogId"] == digest("k-in-k/artifact-catalog/v1", value_without(catalog, "catalogId")), "artifact catalog ID derivation")
    keys = [(entry["role"], entry["digest"]) for entry in catalog["entries"]]
    locators = [normalized_locator(entry) for entry in catalog["entries"]]
    ok(keys == sorted(keys) and len(keys) == len(set(keys)) and len(locators) == len(set(locators)), "artifact catalog entries are duplicate or noncanonical")
    for entry in catalog["entries"]:
        spec = specs[entry["role"]]
        ok((entry["contentModel"], entry["mediaType"]) == (spec["contentModel"], spec["mediaType"]), "artifact catalog metadata differs from its role spec")
        if entry["contentModel"] == "opaque-bytes":
            ok(entry["digest"] == opaque_artifact_digest(entry["role"], entry["mediaType"], entry["contentSha256"]), "opaque catalog identity does not derive from its envelope")
        if entry["availability"] == "bundled":
            verify_catalog_entry_bytes(entry, specs)
    requirement_ids = [item["requirementId"] for item in catalog["unboundRequirements"]]
    ok(requirement_ids == sorted(requirement_ids) and len(requirement_ids) == len(set(requirement_ids)), "unbound requirements are duplicate or noncanonical")


def verify_artifact_boundary_adversaries(catalog: dict[str, Any]) -> None:
    specs = artifact_role_specs()
    definition = load(FIXTURES / "semantic-definition-memory.json")
    summary = definition_summary_payload(definition)
    ok(set(summary) == {"schemaVersion", "representation", "baselineFamilyId", "modules"} and summary["representation"] == definition["representation"], "definition-summary projection omits the representation discriminator")
    for role in ("definition", "instrumented-definition", "mutant-definition"):
        ok(specs[role]["projection"] == {"kind": "definition-summary"}, f"{role} does not use the registered definition-summary projection")
        ok(semantic_artifact_digest(role, definition, specs) == definition["definitionDigest"], f"{role} definition-summary positive identity differs from the definition self ID")
    representation_drift = deepcopy(definition)
    representation_drift["representation"] = "whole-k-adapter-v1"
    drift_digest = semantic_artifact_digest("definition", representation_drift, specs)
    ok(drift_digest != definition["definitionDigest"], "changing only representation did not change definition-summary identity")
    representation_drift["definitionDigest"] = drift_digest
    drift_raw = canonical(representation_drift).encode("utf-8")
    definition_entry = next(entry for entry in catalog["entries"] if (entry["role"], entry["digest"]) == ("definition", definition["definitionDigest"]))
    bad_representation_entry = deepcopy(definition_entry)
    bad_representation_entry.update({"digest": drift_digest, "contentSha256": hashlib.sha256(drift_raw).hexdigest()})
    expect_semantic_rejection(lambda entry: verify_artifact_bytes(entry, drift_raw, specs), bad_representation_entry, "definition artifact accepted a representation-only drift outside the declared slice")
    canonical_entry = next(entry for entry in catalog["entries"] if entry["availability"] == "bundled" and entry["contentModel"] == "canonical-json")
    opaque_entry = next(entry for entry in catalog["entries"] if entry["availability"] == "bundled" and entry["contentModel"] == "opaque-bytes")
    canonical_raw = resolve_bundled(canonical_entry).read_bytes()
    opaque_raw = resolve_bundled(opaque_entry).read_bytes()
    ok(canonical_entry["digest"] != canonical_entry["contentSha256"], "semantic and exact-byte identities were conflated")
    same_bytes = [entry for entry in catalog["entries"] if entry["contentSha256"] == next(item for item in catalog["entries"] if item["role"] == "solver-profile")["contentSha256"]]
    ok({item["role"] for item in same_bytes} >= {"program", "solver-profile"} and len({item["digest"] for item in same_bytes}) == len(same_bytes), "identical bytes did not remain role-separated")

    bad = deepcopy(canonical_entry)
    bad["contentSha256"] = "f" * 64
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, canonical_raw, specs), bad, "canonical byte-hash drift was accepted")
    bad = deepcopy(canonical_entry)
    bad["digest"] = "f" * 64
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, canonical_raw, specs), bad, "canonical semantic-digest drift was accepted")
    selector_entry = next(entry for entry in catalog["entries"] if entry["availability"] == "bundled" and entry["role"] == "mutation-selector")
    selector_value = json.loads(resolve_bundled(selector_entry).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    selector_value["selectorDigest"] = "f" * 64 if selector_value["selectorDigest"] != "f" * 64 else "e" * 64
    selector_raw = canonical(selector_value).encode("utf-8")
    bad = deepcopy(selector_entry)
    bad["contentSha256"] = hashlib.sha256(selector_raw).hexdigest()
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, selector_raw, specs), bad, "canonical artifact self-ID drift was accepted")
    noncanonical_raw = b" " + canonical_raw
    bad = deepcopy(canonical_entry)
    bad["contentSha256"] = hashlib.sha256(noncanonical_raw).hexdigest()
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, noncanonical_raw, specs), bad, "noncanonical but decodable JSON artifact was accepted")
    duplicate_key_raw = b'{"clauses":[],"clauses":[]}'
    bad = deepcopy(canonical_entry)
    bad["contentSha256"] = hashlib.sha256(duplicate_key_raw).hexdigest()
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, duplicate_key_raw, specs), bad, "duplicate-key canonical artifact was accepted")
    bad = deepcopy(opaque_entry)
    bad["role"] = "solver-profile" if bad["role"] != "solver-profile" else "program"
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, opaque_raw, specs), bad, "opaque identity was reused across roles")
    bad = deepcopy(opaque_entry)
    bad["mediaType"] = "application/json"
    expect_semantic_rejection(lambda value: verify_artifact_bytes(value, opaque_raw, specs), bad, "opaque media-type envelope drift was accepted")

    duplicate = deepcopy(catalog)
    duplicate["entries"].append(deepcopy(duplicate["entries"][0]))
    duplicate["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(duplicate, "catalogId"))
    expect_semantic_rejection(validate_artifact_catalog, duplicate, "duplicate role/digest catalog key was accepted")
    duplicate = deepcopy(catalog)
    duplicate["entries"][1]["logicalPath"] = duplicate["entries"][0]["logicalPath"]
    duplicate["entries"][1]["resolverId"] = duplicate["entries"][0]["resolverId"]
    duplicate["entries"][1]["availability"] = duplicate["entries"][0]["availability"]
    duplicate["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(duplicate, "catalogId"))
    expect_semantic_rejection(validate_artifact_catalog, duplicate, "duplicate normalized locator was accepted")
    expect_semantic_rejection(lambda value: ok(set(value) == {"role", "digest"}, "artifact key repeats catalog metadata"), {"role": "program", "digest": "0" * 64, "mediaType": "application/octet-stream"}, "artifact reference repeated catalog metadata")
    expect_semantic_rejection(lambda value: ok(value["role"] in specs, "unknown artifact role"), {"role": "projection", "digest": "0" * 64}, "aliased artifact role was accepted")

    for locator in ("repo://investigations/../escape", "repo://investigations/%2e%2e/escape", "repo://investigations\\escape"):
        bad = deepcopy(opaque_entry)
        bad.update({"logicalPath": locator, "resolverId": "repo-v1", "availability": "bundled"})
        expect_semantic_rejection(normalized_locator, bad, f"unsafe locator {locator} was accepted")
    bad = deepcopy(opaque_entry)
    bad.update({"logicalPath": "artifact://external/object", "resolverId": "missing-resolver", "availability": "external-required"})
    expect_semantic_rejection(normalized_locator, bad, "unknown artifact resolver was accepted")
    bad = deepcopy(opaque_entry)
    bad["logicalPath"] = "repo://investigations/backend-agnostic-goal-closure/material/missing.bin"
    expect_semantic_rejection(resolve_bundled, bad, "missing bundled target was accepted")
    with tempfile.TemporaryDirectory(prefix="bag08-", dir=PACKAGE) as temporary:
        link = Path(temporary) / "escape"
        link.symlink_to(Path("/etc/passwd"))
        bad = deepcopy(opaque_entry)
        bad["logicalPath"] = f"repo://{link.relative_to(ROOT).as_posix()}"
        expect_semantic_rejection(resolve_bundled, bad, "bundled symlink escape was accepted")
    missing_hash = deepcopy(catalog)
    external = next(entry for entry in missing_hash["entries"] if entry["availability"] == "external-required")
    external.pop("contentSha256")
    expect_schema_rejection(missing_hash, "artifact-catalog.schema.json", "external artifact without a known content hash was accepted")
    expect_semantic_rejection(lambda value: ok(not value["materialClosure"] or (not value["unboundInputs"] and not value["externalRequiredInputs"] and not value["unresolvedConcreteKeys"]), "material closure retained an unavailable input"), {"materialClosure": True, "unboundInputs": [{"role": "program", "requirementId": "future-program"}], "externalRequiredInputs": [], "unresolvedConcreteKeys": []}, "material closure with an unbound input was accepted")


def require_catalog_entries(catalog: dict[str, Any], requirements: list[tuple[str, str | None]], context: str) -> None:
    available = {(entry["role"], entry["digest"]) for entry in catalog["entries"]}
    missing = [(role, artifact_digest) for role, artifact_digest in requirements if artifact_digest is not None and (role, artifact_digest) not in available]
    ok(not missing, f"{context} has unresolved role-typed artifact roots: {missing}")


def walk_artifact_keys(value: Any) -> list[dict[str, str]]:
    if isinstance(value, dict):
        if set(value) == {"role", "digest"} and isinstance(value["role"], str) and isinstance(value["digest"], str):
            return [value]
        return [item for child in value.values() for item in walk_artifact_keys(child)]
    if isinstance(value, list):
        return [item for child in value for item in walk_artifact_keys(child)]
    return []


def catalog_pattern_registries(catalog: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    plans: dict[str, dict[str, Any]] = {}
    queries: dict[str, dict[str, Any]] = {}
    for entry in catalog["entries"]:
        if entry["role"] not in {"pattern-plan", "pattern-query"}:
            continue
        ok(entry["availability"] == "bundled", "selected pattern plan/query artifact is not bundled for zero-backend resolution")
        value = load(resolve_bundled(entry))
        identity_field = "patternPlanDigest" if entry["role"] == "pattern-plan" else "queryId"
        ok(value[identity_field] == entry["digest"], "catalog pattern artifact key differs from resolved self identity")
        target = plans if entry["role"] == "pattern-plan" else queries
        ok(entry["digest"] not in target, "catalog resolves duplicate pattern artifact identity")
        target[entry["digest"]] = value
    return plans, queries


def observation_vocabulary_digest(manifest_digest: str) -> str:
    observations = [load(FIXTURES / name) for name in ("observation-manifest.json", "mutation-observation-manifest.json")]
    matches = [item for item in observations if item["manifestId"] == manifest_digest]
    ok(len(matches) == 1, "pattern invocation observation manifest is dangling or ambiguous")
    return matches[0]["eventVocabularyDigest"]


def resolve_pattern_query_root(root: dict[str, Any], catalog: dict[str, Any], vocabularies: dict[str, dict[str, Any]], expected_vocabulary_digest: str | None = None) -> tuple[dict[str, Any], dict[str, Any]]:
    catalog_keys = {(entry["role"], entry["digest"]) for entry in catalog["entries"]}
    require_catalog_entries(catalog, [(value["role"], value["digest"]) for value in root.values()], "pattern query selection")
    plans, queries = catalog_pattern_registries(catalog)
    query_digest = root["patternQuery"]["digest"]
    ok(query_digest in queries, "pattern query selection does not resolve to an exact query artifact")
    query = queries[query_digest]
    validate_pattern_query(query, plans, catalog_keys)
    ok(query["patternSource"] == root["patternSource"] and query["patternPlan"] == root["patternPlan"], "consumer source/plan/query triple differs from the resolved query's nested roots")
    plan = plans[root["patternPlan"]["digest"]]
    validate_pattern_plan(plan, vocabularies, catalog_keys)
    if expected_vocabulary_digest is not None:
        ok(plan["eventVocabularyDigest"] == expected_vocabulary_digest, "selected pattern plan vocabulary differs from the exact resolved observation manifest")
    return plan, query


def replay_catalog_requirements(replay: dict[str, Any]) -> list[tuple[str, str | None]]:
    requirements = [("definition", replay["definitionDigest"]), ("compatibility-profile", replay["compatibilityProfileDigest"]), ("execution-profile", replay["executionProfileDigest"]), ("solver-profile", replay["solverProfileDigest"]), ("options", replay["optionsDigest"])]
    if replay["kind"] == "pattern-query":
        requirements.extend(("transformation", value) for value in replay["transformationDigests"])
        requirements.extend([("program", replay["programDigest"]), ("parser", replay["parserDigest"]), ("observer", replay["observerDigest"]), ("observation-manifest", replay["observationManifestDigest"])])
        requirements.extend((replay[field]["role"], replay[field]["digest"]) for field in ("patternSource", "patternPlan", "patternQuery"))
    else:
        requirements.extend([("mutation-operator", replay["mutation"]["operatorDigest"]), ("patch", replay["mutation"]["patchId"]), ("structural-diff", next(artifact["digest"] for artifact in replay["artifacts"] if artifact["role"] == "structural-diff"))])
    return requirements


def validate_replay_catalog(replay: dict[str, Any], catalog: dict[str, Any]) -> None:
    ok(replay["artifactCatalogDigest"] == catalog["catalogId"], "replay references another artifact catalog")
    requirements = replay_catalog_requirements(replay)
    require_catalog_entries(catalog, requirements, "replay")


def derive_replay_closure(replay: dict[str, Any], catalog: dict[str, Any]) -> dict[str, Any]:
    by_key = {(entry["role"], entry["digest"]): entry for entry in catalog["entries"]}
    required = {(role, value) for role, value in replay_catalog_requirements(replay) if value is not None}
    produced: set[tuple[str, str]] = set()
    pre_execution: set[tuple[str, str]] = set(required)
    for step in replay["steps"]:
        for item in step["inputArtifacts"]:
            key = (item["role"], item["digest"])
            if key not in produced:
                required.add(key)
                pre_execution.add(key)
        produced.update((item["role"], item["digest"]) for item in step["expectedArtifacts"])
    unresolved = sorted(required - set(by_key))
    external = sorted(key for key in pre_execution if key in by_key and by_key[key]["availability"] == "external-required")
    unbound: list[dict[str, Any]] = []
    referential = not unresolved
    material = referential and not external and not unbound
    as_keys = lambda values: [{"role": role, "digest": artifact_digest} for role, artifact_digest in values]
    return {"replayId": replay["replayId"], "referentialClosure": referential, "materialClosure": material, "unresolvedConcreteKeys": as_keys(unresolved), "externalRequiredInputs": as_keys(external), "unboundInputs": unbound, "executionConformance": "not-proven"}


def validate_execution_profile_consistency(pattern: dict[str, Any], replay: dict[str, Any], corpus: dict[str, Any]) -> None:
    expected = corpus["executionProfileDigest"]
    ok(pattern["inputs"]["executionProfileDigest"] == expected, "pattern execution profile differs from corpus")
    ok(replay["executionProfileDigest"] == expected, "replay execution profile differs from corpus")


def validate_definition_graph(definition: dict[str, Any]) -> None:
    module_names = [module["name"] for module in definition["modules"]]
    ok(len(module_names) == len(set(module_names)), "definition has duplicate module names")
    module_name_set = set(module_names)
    entries = definition["family"]["entryModules"]
    ok(len(entries) == len(set(entries)) and set(entries) <= module_name_set, "definition family entry modules do not resolve uniquely")
    lineage_ids: list[str] = []
    content_ids: list[str] = []
    occurrence_groups: dict[str, list[int]] = {}
    for module in definition["modules"]:
        ok(len(module["imports"]) == len(set(module["imports"])) and set(module["imports"]) <= module_name_set, "definition imports do not resolve uniquely")
        lineage_ids.extend(sentence["provenance"]["lineageId"] for sentence in module["sentences"])
        content_ids.extend(sentence["provenance"]["contentFingerprint"] for sentence in module["sentences"])
        for sentence in module["sentences"]:
            if not sentence["provenance"]["generated"]:
                value = sentence["value"]
                anchor = canonical({"module": module["name"], "source": value["source"], "location": value["location"], "kind": value["kind"]})
                occurrence_groups.setdefault(anchor, []).append(sentence["sourceOccurrenceOrdinal"])
    ok(len(lineage_ids) == len(set(lineage_ids)), "definition has duplicate sentence lineages")
    ok(len(content_ids) == len(set(content_ids)), "definition has duplicate sentence content identities")
    ok(all(ordinals == list(range(len(ordinals))) for ordinals in occurrence_groups.values()), "input sentence occurrence ordinals are not contiguous per source anchor")


def validate_location(location: dict[str, int]) -> None:
    ok((location["endLine"], location["endColumn"]) >= (location["startLine"], location["startColumn"]), "source location ends before it starts")


SignatureRegistry = dict[str, tuple[str, str, int, tuple[str, ...]]]


def validate_portable_term(
    term: dict[str, Any],
    signatures: SignatureRegistry | None = None,
    variables: dict[str, str] | None = None,
) -> None:
    signatures = {} if signatures is None else signatures
    variables = {} if variables is None else variables
    node = term["node"]
    kind = node["kind"]
    if kind == "variable":
        prior = variables.setdefault(node["name"], term["sort"])
        ok(prior == term["sort"], "variable name has conflicting sorts in one local scope")
    if kind == "rewrite":
        validate_portable_term(node["left"], signatures, variables)
        validate_portable_term(node["right"], signatures, variables)
        ok(node["left"]["sort"] == node["right"]["sort"], "rewrite children have different sorts")
    elif kind == "application":
        for argument in node["args"]:
            validate_portable_term(argument, signatures, variables)
        signature = (node["label"], term["sort"], len(node["args"]), tuple(argument["sort"] for argument in node["args"]))
        previous = signatures.setdefault(node["symbolId"], signature)
        ok(previous == signature, "symbol ID has conflicting display label or signature")
    elif kind == "sequence":
        for item in node["items"]:
            validate_portable_term(item, signatures, variables)
    elif kind == "injection":
        validate_portable_term(node["term"], signatures, variables)
        ok(node["term"]["sort"] == node["fromSort"] and term["sort"] == node["toSort"], "injection child/wrapper sorts contradict fromSort/toSort")


def validate_sentence_local_well_formedness(value: dict[str, Any], signatures: SignatureRegistry) -> None:
    variables: dict[str, str] = {}
    validate_portable_term(value["body"], signatures, variables)
    for condition_name in ("requires", "ensures"):
        condition = value[condition_name]
        if condition is not None:
            ok(condition["sort"] == "Bool", f"{condition_name} is not Bool-sorted")
            validate_portable_term(condition, signatures, variables)
    attribute_names = [attribute["name"] for attribute in value["attributes"]]
    ok(attribute_names == sorted(attribute_names) and len(attribute_names) == len(set(attribute_names)), "sentence attributes are not a canonical name-keyed set")
    for attribute in value["attributes"]:
        if attribute["value"] is not None:
            validate_portable_term(attribute["value"], signatures, variables)


def definition_signature_registry(definition: dict[str, Any], seed: SignatureRegistry | None = None) -> SignatureRegistry:
    signatures = {} if seed is None else dict(seed)
    for module in definition["modules"]:
        for sentence in module["sentences"]:
            validate_sentence_local_well_formedness(sentence["value"], signatures)
    return signatures


def definition_signatures_for_reference(definition_digest: str) -> SignatureRegistry:
    ok(bool(definition_digest), "semantic term graph lacks an exact referenced definition identity")
    definitions = [load(FIXTURES / name) for name in ("semantic-definition-memory.json", "semantic-definition-counter.json", "semantic-definition-generated.json")]
    for definition in definitions:
        if definition_digest == definition["definitionDigest"]:
            return definition_signature_registry(definition)
    campaign = load(FIXTURES / "mutation-campaign.json")
    for mutant, candidate in zip(campaign["mutants"], campaign["generation"]["candidates"]):
        if mutant["outputDefinitionDigest"] == definition_digest:
            output, _, failure = apply_portable_patch(definitions[0], candidate["patch"])
            ok(failure is None and output is not None, "referenced mutant definition cannot seed its signature registry")
            return definition_signature_registry(output, definition_signature_registry(definitions[0]))
    raise AssertionError("referenced definition identity is unavailable")


def validate_definition_semantics(definition: dict[str, Any], immutable_signature_seed: SignatureRegistry | None = None, transformation_inputs: dict[str, dict[str, Any]] | None = None) -> None:
    validate_definition_graph(definition)
    ok(definition["representation"] == "portable-mutation-semantic-slice-v1", "definition representation is not the portable mutation semantic slice")
    definition_signature_registry(definition, immutable_signature_seed)
    family_id = digest("k-in-k/baseline-family/v1", baseline_family_payload(definition["family"]))
    ok(definition["baselineFamilyId"] == family_id, f"{definition['family']['familyName']}: baseline family ID")
    module_payloads: list[dict[str, Any]] = []
    for expected_ordinal, module in enumerate(definition["modules"]):
        ok(module["ordinal"] == expected_ordinal, "definition module ordinals are not contiguous")
        content_fingerprints: list[str] = []
        for sentence in module["sentences"]:
            provenance, value = sentence["provenance"], sentence["value"]
            validate_location(value["location"])
            attribute_names = [attribute["name"] for attribute in value["attributes"]]
            ok(attribute_names == sorted(attribute_names) and len(attribute_names) == len(set(attribute_names)), "sentence attributes are unsorted or duplicated")
            ok(value["module"] == module["name"] == provenance["module"], "sentence module mismatch")
            for key in ("label", "kind", "source", "location"):
                ok(value[key] == provenance[key], f"sentence {key} provenance mismatch")
            if provenance["generated"]:
                ok(sentence["sourceOccurrenceOrdinal"] is None, "generated sentence retained a source occurrence ordinal")
                ok(sentence["generatedIdentity"] is not None, "generated sentence lacks identity input")
                ok(provenance["transformationChain"] and provenance["transformationChain"][-1] == sentence["generatedIdentity"]["transformationId"], "generated sentence transformation chain does not end at its generating transformation")
                parents = sentence["generatedIdentity"]["parentLineages"]
                ok(parents == sorted(set(parents)), "generated parent lineages are not unique and canonical")
                known_lineages = {item["provenance"]["lineageId"] for owner in definition["modules"] for item in owner["sentences"]}
                generated_identity = sentence["generatedIdentity"]
                role = generated_identity["role"]
                module_roles = {"insert-module-end", "insert-module-start"}
                if role in module_roles:
                    ok(not parents, "module-start/end generated role carries a parent lineage")
                    ok(transformation_inputs is not None and generated_identity["transformationId"] in transformation_inputs, "module-start/end generated role lacks its reviewed transformation input definition")
                    input_definition = transformation_inputs[generated_identity["transformationId"]]
                    input_modules = {item["name"]: item for item in input_definition["modules"]}
                    ok(value["module"] in input_modules and generated_identity["anchorIdentity"] == input_modules[value["module"]]["fingerprint"], "module-start/end generated anchor does not equal the reviewed input module fingerprint")
                else:
                    ok(bool(parents) and set(parents) <= known_lineages, "parented generated role has empty/dangling parent lineages")
                    ok(generated_identity["anchorIdentity"] in known_lineages, "parented generated anchor is not a destination lineage")
                    if role in {"insert-after-lineage", "insert-before-lineage"}:
                        ok(generated_identity["anchorIdentity"] in parents, "sentence insertion anchor is not one of its parents")
                lineage_id = digest("k-in-k/generated-lineage/v1", sentence["generatedIdentity"])
            else:
                ok(isinstance(sentence["sourceOccurrenceOrdinal"], int), "source sentence lacks a source occurrence ordinal")
                ok(sentence["generatedIdentity"] is None, "input sentence carries generated identity")
                lineage_payload = {
                    "baselineFamilyId": family_id, "module": module["name"], "source": value["source"],
                    "location": value["location"], "kind": value["kind"], "sourceOccurrenceOrdinal": sentence["sourceOccurrenceOrdinal"],
                }
                lineage_id = digest("k-in-k/input-lineage/v1", lineage_payload)
            ok(provenance["lineageId"] == lineage_id, "sentence lineage derivation")
            body_payload = {"body": value["body"], "requires": value["requires"], "ensures": value["ensures"]}
            body_id = digest("k-in-k/sentence-body/v1", body_payload)
            ok(provenance["bodyFingerprint"] == body_id, "sentence body fingerprint derivation")
            content_payload = {
                "lineageId": lineage_id, "module": value["module"], "label": value["label"], "kind": value["kind"],
                "source": value["source"], "location": value["location"], "generated": provenance["generated"],
                "bodyFingerprint": body_id, "attributes": value["attributes"],
                "transformationChain": provenance["transformationChain"],
            }
            content_id = digest("k-in-k/sentence-content/v1", content_payload)
            ok(provenance["contentFingerprint"] == content_id, "sentence content fingerprint derivation")
            content_fingerprints.append(content_id)
        module_payload = {"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": content_fingerprints}
        ok(module["fingerprint"] == digest("k-in-k/module/v1", module_payload), "module fingerprint derivation")
        module_payloads.append(module_payload)
    definition_payload = {"schemaVersion": definition["schemaVersion"], "representation": definition["representation"], "baselineFamilyId": family_id, "modules": module_payloads}
    ok(definition["definitionDigest"] == digest("k-in-k/definition/v1", definition_payload), "portable definition digest derivation")


def verify_bag13_local_well_formedness() -> None:
    memory = load(FIXTURES / "semantic-definition-memory.json")
    generated = load(FIXTURES / "semantic-definition-generated.json")
    common = load(SCHEMAS / "common.schema.json")

    def reject_term_schema(term: dict[str, Any], message: str) -> None:
        expect_semantic_rejection(lambda value: validate_schema(value, common["$defs"]["term"], SCHEMAS / "common.schema.json", common), term, message)

    source_value = memory["modules"][0]["sentences"][0]["value"]
    drift = deepcopy(source_value)
    drift["requires"] = {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "A"}}
    expect_semantic_rejection(lambda value: validate_sentence_local_well_formedness(value, {}), drift, "same-sentence variable sort drift was accepted")
    non_bool = deepcopy(source_value)
    non_bool["requires"] = {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "token", "text": "1"}}
    expect_semantic_rejection(lambda value: validate_sentence_local_well_formedness(value, {}), non_bool, "non-Bool requires was accepted")
    rewrite_drift = deepcopy(source_value["body"])
    rewrite_drift["node"]["right"]["sort"] = "OtherState"
    expect_semantic_rejection(validate_portable_term, rewrite_drift, "rewrite child sort mismatch was accepted")
    injection_drift = {"encoding": "portable-term-v1", "sort": "Address", "node": {"kind": "injection", "fromSort": "Int", "toSort": "Address", "term": {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "token", "text": "true"}}}}
    expect_semantic_rejection(validate_portable_term, injection_drift, "injection mismatch was accepted")

    symbol = "1" * 64
    base_application = {"encoding": "portable-term-v1", "sort": "Result", "node": {"kind": "application", "symbolId": symbol, "label": "display", "args": [{"encoding": "portable-term-v1", "sort": "Arg", "node": {"kind": "token", "text": "x"}}]}}
    reject_term_schema({"encoding": "portable-term-v1", "sort": "Result", "node": {"kind": "application", "label": "display", "args": []}}, "application without symbol ID was accepted")
    for field, mutation in (
        ("result", lambda term: term.update(sort="OtherResult")),
        ("arity", lambda term: term["node"]["args"].append({"encoding": "portable-term-v1", "sort": "Arg", "node": {"kind": "token", "text": "y"}})),
        ("argument", lambda term: term["node"]["args"][0].update(sort="OtherArg")),
        ("label", lambda term: term["node"].update(label="other-display")),
    ):
        registry: SignatureRegistry = {}
        validate_portable_term(deepcopy(base_application), registry, {})
        changed = deepcopy(base_application)
        mutation(changed)
        expect_semantic_rejection(lambda value: validate_portable_term(value, registry, {}), changed, f"symbol-ID {field} drift was accepted")
    overload_registry: SignatureRegistry = {}
    validate_portable_term(base_application, overload_registry, {})
    overload = deepcopy(base_application)
    overload["node"]["symbolId"] = "2" * 64
    overload["sort"] = "OtherResult"
    validate_portable_term(overload, overload_registry, {})
    ok(len(overload_registry) == 2, "overloaded display label was collapsed instead of retaining distinct symbol IDs")

    unsorted = deepcopy(memory)
    unsorted["modules"][0]["sentences"][0]["value"]["attributes"] = [{"name": "z", "value": None}, {"name": "a", "value": None}]
    expect_semantic_rejection(validate_definition_semantics, unsorted, "checker normalized unsorted attributes")
    duplicate = deepcopy(memory)
    duplicate["modules"][0]["sentences"][0]["value"]["attributes"] *= 2
    expect_semantic_rejection(validate_definition_semantics, duplicate, "duplicate attributes were accepted")
    hidden_attribute = deepcopy(source_value)
    hidden_attribute["attributes"] = [{"name": "typed", "value": {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "A"}}}]
    expect_semantic_rejection(lambda value: validate_sentence_local_well_formedness(value, {}), hidden_attribute, "variable contradiction hidden in an attribute was accepted")

    generated_rule = deepcopy(source_value)
    generated_rule["kind"] = "generated-rule"
    expect_semantic_rejection(lambda value: validate_schema(value, common["$defs"]["sentenceValue"], SCHEMAS / "common.schema.json", common), generated_rule, "generated-rule kind was accepted")
    bad_generated = deepcopy(generated)
    bad_generated["modules"][0]["sentences"][2]["sourceOccurrenceOrdinal"] = 0
    expect_schema_rejection(bad_generated, "semantic-definition.schema.json", "generated sentence with source occurrence ordinal was accepted")
    bad_source = deepcopy(generated)
    bad_source["modules"][0]["sentences"][0]["sourceOccurrenceOrdinal"] = None
    expect_schema_rejection(bad_source, "semantic-definition.schema.json", "source sentence without source occurrence ordinal was accepted")
    bad_parents = deepcopy(generated)
    source_lineages = [sentence["provenance"]["lineageId"] for sentence in bad_parents["modules"][0]["sentences"][:2]]
    bad_parents["modules"][0]["sentences"][2]["generatedIdentity"]["parentLineages"] = list(reversed(sorted(source_lineages)))
    expect_semantic_rejection(validate_definition_semantics, bad_parents, "noncanonical generated parents were accepted")
    stale_chain = deepcopy(generated)
    stale_chain["modules"][0]["sentences"][2]["provenance"]["transformationChain"][-1] = "f" * 64
    expect_semantic_rejection(validate_definition_semantics, stale_chain, "generated transformation chain drift was accepted")

    parentless_derived_definition = deepcopy(generated)
    parentless_derived_definition["modules"][0]["sentences"][2]["generatedIdentity"]["parentLineages"] = []
    expect_schema_rejection(parentless_derived_definition, "semantic-definition.schema.json", "semantic definition accepted a parentless derived-rule")
    identity_input = load(FIXTURES / "semantic-definition-memory.json")
    identity_output = load(FIXTURES / "semantic-definition-identity-output.json")
    module_generated = next(sentence for module in identity_output["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None and sentence["generatedIdentity"]["role"] == "insert-module-end")
    parented_module_definition = deepcopy(identity_output)
    parented_module_sentence = next(sentence for module in parented_module_definition["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == module_generated["provenance"]["lineageId"])
    parented_module_sentence["generatedIdentity"]["parentLineages"] = [identity_input["modules"][0]["sentences"][0]["provenance"]["lineageId"]]
    expect_schema_rejection(parented_module_definition, "semantic-definition.schema.json", "semantic definition accepted a parented module insertion")
    sentence_anchor_mismatch = deepcopy(identity_output)
    sentence_generated = next(sentence for module in sentence_anchor_mismatch["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None and sentence["generatedIdentity"]["role"] == "insert-before-lineage")
    alternate_lineage = next(sentence["provenance"]["lineageId"] for module in sentence_anchor_mismatch["modules"] for sentence in module["sentences"] if not sentence["provenance"]["generated"] and sentence["provenance"]["lineageId"] not in sentence_generated["generatedIdentity"]["parentLineages"])
    sentence_generated["generatedIdentity"]["anchorIdentity"] = alternate_lineage
    sentence_generated["provenance"]["lineageId"] = digest("k-in-k/generated-lineage/v1", sentence_generated["generatedIdentity"])
    sentence_anchor_mismatch = refreshed_definition(sentence_anchor_mismatch)
    transformation_inputs = {sentence_generated["generatedIdentity"]["transformationId"]: identity_input}
    expect_semantic_rejection(lambda value: validate_definition_semantics(value, transformation_inputs=transformation_inputs), sentence_anchor_mismatch, "sentence-relative generated role accepted a lineage anchor outside its parents")
    module_anchor_mismatch = deepcopy(identity_output)
    module_sentence = next(sentence for module in module_anchor_mismatch["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None and sentence["generatedIdentity"]["role"] == "insert-module-end")
    module_sentence["generatedIdentity"]["anchorIdentity"] = "f" * 64
    module_sentence["provenance"]["lineageId"] = digest("k-in-k/generated-lineage/v1", module_sentence["generatedIdentity"])
    module_anchor_mismatch = refreshed_definition(module_anchor_mismatch)
    expect_semantic_rejection(lambda value: validate_definition_semantics(value, transformation_inputs=transformation_inputs), module_anchor_mismatch, "module insertion role accepted a non-input-module anchor")

    ordinal_changed = deepcopy(generated)
    changed_sentence = ordinal_changed["modules"][0]["sentences"][2]
    before = (changed_sentence["provenance"]["lineageId"], changed_sentence["provenance"]["contentFingerprint"], ordinal_changed["modules"][0]["fingerprint"], ordinal_changed["definitionDigest"])
    changed_sentence["generatedIdentity"]["ordinal"] += 1
    changed_sentence["provenance"]["lineageId"] = digest("k-in-k/generated-lineage/v1", changed_sentence["generatedIdentity"])
    ordinal_changed = refreshed_definition(ordinal_changed)
    after_sentence = ordinal_changed["modules"][0]["sentences"][2]
    after = (after_sentence["provenance"]["lineageId"], after_sentence["provenance"]["contentFingerprint"], ordinal_changed["modules"][0]["fingerprint"], ordinal_changed["definitionDigest"])
    ok(all(left != right for left, right in zip(before, after)), "generated sentence sole ordinal did not change every dependent identity")
    validate_definition_semantics(ordinal_changed)
    stale_ordinal = deepcopy(generated)
    stale_ordinal["modules"][0]["sentences"][2]["generatedIdentity"]["ordinal"] += 1
    expect_semantic_rejection(validate_definition_semantics, stale_ordinal, "stale dependent IDs after generation ordinal change were accepted")

    path_registry: SignatureRegistry = {}
    path_variables: dict[str, str] = {}
    validate_portable_term({"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "P"}}, path_registry, path_variables)
    expect_semantic_rejection(lambda term: validate_portable_term(term, path_registry, path_variables), {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "P"}}, "same-path variable sort drift was accepted")
    validate_portable_term({"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "P"}}, {}, {})
    binding_registry: SignatureRegistry = {}
    binding_variables: dict[str, str] = {}
    validate_portable_term({"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "BOUND"}}, binding_registry, binding_variables)
    expect_semantic_rejection(lambda term: validate_portable_term(term, binding_registry, binding_variables), {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "BOUND"}}, "contradiction hidden in a path binding was accepted")
    contradictory_trace = load(FIXTURES / "event-trace.json")
    contradictory_trace["pathPredicate"] = {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "PATHVAR"}}
    contradictory_trace["events"][0]["payload"][0] = {"encoding": "portable-term-v1", "sort": "Address", "node": {"kind": "variable", "name": "PATHVAR"}}
    contradictory_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(contradictory_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    expect_semantic_rejection(validate_trace_semantics, contradictory_trace, "contradiction hidden in an event/predicate path graph was accepted")
    empty_trace = load(FIXTURES / "event-trace.json")
    empty_trace["events"] = []
    empty_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(empty_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    validate_trace_semantics(empty_trace)
    missing_trace_definition = deepcopy(empty_trace)
    missing_trace_definition.pop("definitionDigest")
    expect_schema_rejection(missing_trace_definition, "event-trace.schema.json", "empty-event trace without an explicit definition identity was accepted")
    unresolved_empty_trace = deepcopy(empty_trace)
    unresolved_empty_trace["definitionDigest"] = "f" * 64
    unresolved_empty_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(unresolved_empty_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    expect_semantic_rejection(validate_trace_semantics, unresolved_empty_trace, "empty-event trace resolved through an empty-lineage fallback")
    graph_trace = load(FIXTURES / "event-trace.json")
    graph_trace["events"][0]["payload"][0] = {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "SHARED-GRAPH-VARIABLE"}}
    graph_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(graph_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    graph_trace_digest = digest("k-in-k/event-trace/v1", graph_trace)
    graph_result = load(FIXTURES / "pattern-result.json")
    graph_result["pathResults"][0]["traceDigest"] = graph_trace_digest
    graph_result["pathResults"][0]["pathIdentityDigest"] = graph_trace["pathIdentityDigest"]
    graph_result["inputs"]["artifacts"] = [{"role": "event-trace", "digest": graph_trace_digest}]
    graph_result["witnesses"][0]["events"] = [deepcopy(graph_trace["events"][index]) for index in graph_result["witnesses"][0]["eventIndices"]]
    graph_result["witnesses"][0]["bindings"].append({"name": "SHARED-GRAPH-VARIABLE", "term": {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "SHARED-GRAPH-VARIABLE"}}})
    graph_result["witnesses"][0]["bindings"].sort(key=lambda binding: binding["name"])
    graph_result["primaryWitness"] = deepcopy(graph_result["witnesses"][0])
    graph_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(graph_result, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {graph_trace_digest: graph_trace}), graph_result, "trace event and witness binding did not share one path graph scope")
    hidden_operand = {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "sequence", "items": [{"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "variable", "name": "OPERAND"}}, {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "variable", "name": "OPERAND"}}]}}
    expect_semantic_rejection(validate_portable_term, hidden_operand, "contradiction hidden in a terminal/oracle operand was accepted")
    baseline_symbol_conflict = deepcopy(source_value["body"]["node"]["left"])
    baseline_symbol_conflict["node"]["label"] += "-conflicting-display"
    terminal_conflict = load(FIXTURES / "terminal-state.json")
    terminal_conflict["value"] = deepcopy(baseline_symbol_conflict)
    terminal_conflict["terminalStateDigest"] = digest("k-in-k/terminal-state/v1", value_without(terminal_conflict, "terminalStateDigest"))
    expect_semantic_rejection(validate_terminal_state_semantics, terminal_conflict, "terminal operand contradicted a baseline symbol signature but was accepted")
    oracle_conflict = load(FIXTURES / "oracle-value-baseline.json")
    oracle_conflict["value"] = deepcopy(baseline_symbol_conflict)
    oracle_conflict["oracleValueDigest"] = digest("k-in-k/oracle-value/v1", value_without(oracle_conflict, "oracleValueDigest"))
    expect_semantic_rejection(validate_oracle_value_semantics, oracle_conflict, "oracle operand contradicted a baseline symbol signature but was accepted")
    heterogeneous_sequence = {"encoding": "portable-term-v1", "sort": "K", "node": {"kind": "sequence", "items": [{"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "token", "text": "1"}}, {"encoding": "portable-term-v1", "sort": "Bool", "node": {"kind": "token", "text": "true"}}]}}
    validate_portable_term(heterogeneous_sequence)
    wrapper_independent = deepcopy(source_value["body"])
    ok(wrapper_independent["sort"] != wrapper_independent["node"]["left"]["sort"], "fixture does not retain rewrite wrapper sort independently")
    validate_portable_term(wrapper_independent)

    completion_documents = {str(path.relative_to(PACKAGE)): path.read_text(encoding="utf-8") for path in sorted(PACKAGE.rglob("*.md"))}
    claims = "\n".join(completion_documents.values())
    boundary = validate_claim_boundary_artifact()
    representation = boundary["representation"]
    ok(representation in completion_documents["contracts.md"] and representation in completion_documents["completion-audit.md"], "completion documents omit the exact portable representation name")
    ok("portable-semantic-definition-v1" not in claims, "completion documents retain a stale portable representation name")
    checklist = load(PACKAGE / "completion-checklist.json")
    matrix = load(PACKAGE / "closure-matrix.json")
    structured_claims = [load(path) for path in sorted(PACKAGE.rglob("*.json"))]
    claim_fragments = [sentence for document in completion_documents.values() for block in markdown_claim_blocks(document) for sentence in re.split(r"(?<=[.!?;])\s+", block)] + [text for document in structured_claims for text in json_text_values(document)]
    for claim in claim_fragments:
        validate_whole_k_claim_boundary(claim, boundary)
    for overclaim in (
        "This package is a complete parsed K adapter.",
        "The native K semantic IR mapping is lossless.",
        "All K constructs are fully represented by this interchange.",
        "The whole-K definition adapter has full fidelity.",
        "The parsed-K frontend is faithful to every K form.",
        "The native K adapter is lossless, not approximate.",
        "Rust must prove a bijective parsed-K adapter; unsupported forms reject.",
        "Parsed K round-trips exactly.",
        "The native K adapter roundtrips exactly.",
        "Whole-K definitions were round-tripped exactly.",
        "Parsed K is round-tripping exactly.",
        "The parsed-K adapter is lossless; an unrelated replay proof is pending.",
        "The parsed-K adapter is lossless and an unrelated replay proof is pending.",
        "The native K mapping is bijective, while resource sizing is not proven.",
        "The parsed-K adapter is lossless, proof is pending for unrelated replay behavior.",
        "The native K mapping is bijective, proof is required for unrelated cache behavior.",
        "Parsed K round-trips exactly; proof is pending for unrelated replay behavior.",
    ):
        expect_semantic_rejection(lambda claim: validate_whole_k_claim_boundary(claim, boundary), overclaim, f"equivalent whole-K overclaim was accepted: {overclaim}")
    validate_whole_k_claim_boundary("Rust must prove exact round-trip mapping for parsed K over the explicitly declared supported surface; unsupported forms reject.", boundary)
    validate_whole_k_claim_boundary("This package does not claim a complete whole-K adapter.", boundary)
    mu01 = next(entry for entry in checklist["entries"] if entry["id"] == "MU-01-definition-and-identity")
    portable_slice = next(entry for entry in matrix["requirements"] if entry["id"] == "portable-semantic-slice-interchange")
    required_traceability = {
        "investigations/backend-agnostic-goal-closure/schemas/semantic-definition.schema.json",
        "investigations/backend-agnostic-goal-closure/schemas/claim-boundary.schema.json",
        "investigations/backend-agnostic-goal-closure/claim-boundary.json",
        "investigations/backend-agnostic-goal-closure/artifact-role-specs.json",
        "investigations/backend-agnostic-goal-closure/fixtures/semantic-definition-memory.json",
        "investigations/backend-agnostic-goal-closure/fixtures/semantic-definition-counter.json",
        "investigations/backend-agnostic-goal-closure/fixtures/semantic-definition-generated.json",
        "investigations/backend-agnostic-goal-closure/verify.py",
    }
    ok(required_traceability <= set(portable_slice["artifacts"]), "portable semantic-slice closure row omits schema, definition-summary projection, fixture, or verifier traceability")
    for text_value, owner in ((mu01["rustProof"], "MU-01 Rust proof"), (portable_slice["rustOpen"], "portable-slice closure row")):
        normalized = text_value.lower()
        ok(all(fragment in normalized for fragment in ("supported", "coverage", "injectiv", "unsupported", "lossy", "reject")), f"{owner} does not bound native losslessness to declared supported-surface coverage/injectivity")
    diff_schema = load(SCHEMAS / "structural-diff.schema.json")
    ok(diff_schema["properties"]["nativeIrValidation"] == {"const": "rust-proof-pending"}, "structural diff schema no longer keeps native IR validation pending")
    campaign = load(FIXTURES / "mutation-campaign.json")
    ok(all(mutant["diff"]["nativeIrValidation"] == "rust-proof-pending" for mutant in campaign["mutants"]), "completion evidence overclaims native IR validation")


def observation_request_payload(observation: dict[str, Any]) -> dict[str, Any]:
    return value_without(observation, "manifestId", "transformationId", "outputDefinitionDigest")


def observation_transformation_payload(observation: dict[str, Any]) -> dict[str, Any]:
    return {
        "kind": "observation-installation",
        "operatorId": observation["observerDigest"],
        "operatorVersion": 1,
        "inputDefinitionDigest": observation["inputDefinitionDigest"],
        "manifestDigest": digest("k-in-k/observation-request/v1", observation_request_payload(observation)),
    }


def refresh_observation_identity(observation: dict[str, Any]) -> None:
    observation["eventVocabulary"].sort(key=lambda declaration: declaration["constructor"])
    observation["eventVocabularyDigest"] = digest("k-in-k/event-vocabulary/v1", observation["eventVocabulary"])
    observation["transformationId"] = digest("k-in-k/transformation/v1", observation_transformation_payload(observation))
    observation["manifestId"] = digest("k-in-k/observation-manifest/v1", value_without(observation, "manifestId"))


def ordered_definition_sentences(definition: dict[str, Any]) -> list[dict[str, Any]]:
    return [sentence for module in sorted(definition["modules"], key=lambda item: item["ordinal"]) for sentence in module["sentences"]]


def derive_observation_lineages(selector: dict[str, Any], definition: dict[str, Any]) -> list[str]:
    """Derive a closed selector result without trusting manifest match claims."""
    sentences = ordered_definition_sentences(definition)
    kind = selector["kind"]
    if kind == "lineage":
        known = {sentence["provenance"]["lineageId"] for sentence in sentences}
        return [selector["lineageId"]] if selector["lineageId"] in known else []
    if kind == "label":
        return [sentence["provenance"]["lineageId"] for sentence in sentences if sentence["provenance"]["label"] == selector["label"]]
    if kind == "attribute":
        expected_attribute = {"name": selector["name"], "value": selector["value"]}
        return [sentence["provenance"]["lineageId"] for sentence in sentences if expected_attribute in sentence["value"]["attributes"]]
    ok(kind == "structural-term", "observation selector kind is outside closed v1")
    sentence_kinds = selector["sentenceKinds"]
    ok(bool(sentence_kinds) and sentence_kinds == sorted(set(sentence_kinds)), "structural selector sentence kinds are empty, duplicate, or unsorted")
    matches: list[str] = []
    for sentence in sentences:
        if sentence["value"]["kind"] not in sentence_kinds:
            continue
        if selector["label"] is not None and sentence["provenance"]["label"] != selector["label"]:
            continue
        try:
            term = path_get(sentence["value"], selector["termPath"])
        except (AssertionError, KeyError, IndexError, TypeError):
            continue
        if not isinstance(term, dict) or term.get("encoding") != "portable-term-v1" or term.get("sort") != selector["termSort"]:
            continue
        head = selector["termHeadLabel"]
        if head is not None and not (term["node"]["kind"] == "application" and term["node"]["label"] == head):
            continue
        matches.append(sentence["provenance"]["lineageId"])
    return matches


def derive_event_semantic_site(observation: dict[str, Any], target_lineage: str, template: dict[str, Any] | None) -> dict[str, Any] | None:
    if template is None:
        return None
    site_payload = {
        "observerDigest": observation["observerDigest"],
        "observerVersion": 1,
        "definitionDigest": observation["inputDefinitionDigest"],
        "targetLineage": target_lineage,
        "role": template["role"],
        "termPath": template["termPath"],
    }
    return {"siteId": digest("k-in-k/observation-site/v1", site_payload), "role": template["role"], "termPath": template["termPath"]}


def validate_observation_paths_and_sorts(observation: dict[str, Any], definition: dict[str, Any]) -> None:
    sentences = sentence_index(definition)
    for selection in observation["selections"]:
        for lineage in selection["matchedLineages"]:
            ok(lineage in sentences, "observation binding references a missing sentence")
            sentence = sentences[lineage][1]
            for emission in selection["emissions"]:
                template = emission["semanticSite"]
                if template is not None:
                    try:
                        site_term = path_get(sentence["value"], template["termPath"])
                    except (AssertionError, KeyError, IndexError, TypeError):
                        raise AssertionError("observation semantic-site path does not resolve for every selected lineage")
                    ok(isinstance(site_term, dict) and site_term.get("encoding") == "portable-term-v1", "observation semantic site is not a portable term")
                for binding in emission["payloadBindings"]:
                    try:
                        source_term = path_get(sentence["value"], binding["sourcePath"])
                    except (AssertionError, KeyError, IndexError, TypeError):
                        raise AssertionError("observation payload source path does not resolve for every selected lineage")
                    ok(isinstance(source_term, dict) and source_term.get("encoding") == "portable-term-v1", "observation payload source is not a portable term")
                    ok(source_term.get("sort") == binding["sort"], "observation payload binding sort differs from selected source term")


def validate_observation_manifest_semantics(observation: dict[str, Any], definition: dict[str, Any]) -> None:
    ok(observation["inputDefinitionDigest"] == definition["definitionDigest"], "observation input definition mismatch")
    ok(observation["transformationId"] == digest("k-in-k/transformation/v1", observation_transformation_payload(observation)), "observation transformation ID derivation")
    ok(observation["manifestId"] == digest("k-in-k/observation-manifest/v1", value_without(observation, "manifestId")), "observation manifest ID derivation")
    selection_ids = [selection["selectionId"] for selection in observation["selections"]]
    ok(len(selection_ids) == len(set(selection_ids)), "duplicate observation selection ID")
    constructors = [declaration["constructor"] for declaration in observation["eventVocabulary"]]
    ok(len(constructors) == len(set(constructors)) and constructors == sorted(constructors), "observation vocabulary is duplicate or not canonical by constructor name")
    ok(observation["eventVocabularyDigest"] == digest("k-in-k/event-vocabulary/v1", observation["eventVocabulary"]), "observation event vocabulary digest drift")
    declarations = {declaration["constructor"]: declaration for declaration in observation["eventVocabulary"]}
    ordered_sentences = ordered_definition_sentences(definition)
    ordered_lineages = [sentence["provenance"]["lineageId"] for sentence in ordered_sentences]
    lineage_order = {lineage: index for index, lineage in enumerate(ordered_lineages)}
    selected: list[str] = []
    for selection in observation["selections"]:
        lineages = selection["matchedLineages"]
        derived_lineages = derive_observation_lineages(selection["selector"], definition)
        ok(len(derived_lineages) == selection["expectedCardinality"] and bool(derived_lineages), "cardinality-mismatch")
        ok(lineages == derived_lineages, "observation matched lineages are not the complete derived selector result in definition order")
        ok(len(lineages) == len(set(lineages)), "observation selection contains duplicate matched lineages")
        ok(all(lineage in lineage_order for lineage in lineages), "observation matched lineage is missing from the definition")
        selected.extend(lineages)
        emissions = selection["emissions"]
        emission_keys = [(emission["constructor"], emission["declarationOrdinal"]) for emission in emissions]
        ok(len(emission_keys) == len(set(emission_keys)) and len({emission["constructor"] for emission in emissions}) == len(emissions), "duplicate observation emission entry")
        ok([emission["declarationOrdinal"] for emission in emissions] == list(range(len(emissions))), "observation emission order is not contiguous")
        for emission in emissions:
            ok(emission["constructor"] in declarations, "observation emits an undeclared constructor")
            declaration = declarations[emission["constructor"]]
            bindings = emission["payloadBindings"]
            names = [binding["name"] for binding in bindings]
            paths = [canonical(binding["sourcePath"]) for binding in bindings]
            ok(len(names) == len(set(names)) and len(paths) == len(set(paths)), "observation payload bindings are not unique")
            ok([binding["sort"] for binding in bindings] == declaration["payloadSorts"], "observation binding sorts differ from event declaration")
            has_site = emission["semanticSite"] is not None
            ok(has_site == (declaration["originMode"] == "emitting-sentence-and-semantic-site"), "observation emission site disagrees with origin mode")
    ok(len(selected) == len(set(selected)), "observation selected one lineage more than once")
    if observation["selectionMode"] == "all-transitions":
        transition_lineages = [sentence["provenance"]["lineageId"] for module in definition["modules"] for sentence in module["sentences"] if sentence["value"]["kind"] == "rule"]
        ok(selected == transition_lineages and all(selection["selector"]["kind"] == "lineage" for selection in observation["selections"]), "all-transitions mode does not enumerate every transition in definition order")
    validate_observation_paths_and_sorts(observation, definition)


def validate_observation_installation_semantics(result: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> None:
    reject_baseline_mismatch(result["failures"], "observation installation failures")
    ok(result["resultId"] == digest("k-in-k/observation-installation-result/v1", value_without(result, "resultId")), "observation installation result ID derivation")
    dispositions = [consume_failure_disposition(failure, "observation-installation", taxonomy) for failure in result["failures"]]
    if result["status"] == "error":
        ok(dispositions and all(disposition == "error" for disposition in dispositions), "observation installation error differs from its taxonomy consequence")
    else:
        ok(not dispositions, "successful observation installation retained a taxonomy failure")


def validate_event_against_observation(event: dict[str, Any], observation: dict[str, Any], definition: dict[str, Any]) -> None:
    declarations = {item["constructor"]: item for item in observation["eventVocabulary"]}
    ok(event["constructor"] in declarations, f"event constructor {event['constructor']} is undeclared")
    declaration = declarations[event["constructor"]]
    ok([term["sort"] for term in event["payload"]] == declaration["payloadSorts"], f"event payload sorts disagree for {event['constructor']}")
    sentences = sentence_index(definition)
    emitting = event["origin"]["emittingSentence"]
    ok(emitting["lineageId"] in sentences and emitting == sentences[emitting["lineageId"]][1]["provenance"], "event emitting provenance differs from canonical definition provenance")
    matching_emissions = [emission for selection in observation["selections"] if emitting["lineageId"] in selection["matchedLineages"] for emission in selection["emissions"] if emission["constructor"] == event["constructor"]]
    ok(len(matching_emissions) == 1, "event is not authorized by exactly one observation emission")
    expected_site = derive_event_semantic_site(observation, emitting["lineageId"], matching_emissions[0]["semanticSite"])
    ok(event["origin"]["semanticSite"] == expected_site, "event semantic site differs from the lineage-derived observation site")
    semantic_site = event["origin"]["semanticSite"]
    if declaration["originMode"] == "emitting-sentence":
        ok(semantic_site is None, f"{event['constructor']} unexpectedly carries a semantic site")
    else:
        ok(semantic_site is not None, f"{event['constructor']} is missing its semantic site")


def validate_mutation_site_registry(site_registry: dict[str, Any], definition: dict[str, Any], operator: dict[str, Any]) -> None:
    selector = site_registry["selector"]
    join = site_registry["join"]
    ok(selector["selectorDigest"] == digest("k-in-k/mutation-selector/v1", selector["clauses"]), "mutation selector digest derivation")
    if join is not None:
        ok(join["joinDigest"] == digest("k-in-k/mutation-join/v1", value_without(join, "joinDigest")), "mutation join digest derivation")
    validate_policy_registry_shape(site_registry)
    ok(site_registry["definitionDigest"] == definition["definitionDigest"] and site_registry["operatorDigest"] == operator["operatorDigest"], "mutation site registry root identity mismatch")
    ok((selector["selectorDigest"], join["joinDigest"] if join is not None else None) == (operator["selectorDigest"], operator["joinDigest"]), "operator selector/join digests do not resolve to the site registry")
    roles = [clause["role"] for clause in selector["clauses"]]
    ok(len(roles) == len(set(roles)), "selector roles are duplicate")
    validate_patch_template_interface(operator, selector)
    if join is None:
        ok(len(roles) == 1 and operator["expectedTupleArity"] == 1, "join-free selector must produce singleton tuples")
    else:
        ok(join["orderedRoles"] == roles and len({clause["bindingName"] for clause in selector["clauses"]}) == 1 and join["bindingName"] == selector["clauses"][0]["bindingName"], "selector roles/bindings disagree with join declaration")
    expected_sites: list[dict[str, Any]] = []
    terms: dict[str, dict[str, Any]] = {}
    sentences = [sentence for module in definition["modules"] for sentence in module["sentences"]]
    sentence_order = {sentence["provenance"]["lineageId"]: index for index, sentence in enumerate(sentences)}
    for clause in selector["clauses"]:
        ok(clause["sentenceKinds"] == sorted(set(clause["sentenceKinds"])), "mutation selector sentence kinds are not canonical")
        ok(set(clause["sentenceKinds"]) <= set(operator["sentenceKinds"]), "mutation selector sentence kind exceeds operator declaration")
        for sentence in sentences:
            generated_allowed = operator["generatedSentencePolicy"] == "include" or (operator["generatedSentencePolicy"] == "only") == sentence["provenance"]["generated"]
            label_matches = clause["label"] is None or sentence["provenance"]["label"] == clause["label"]
            if generated_allowed and label_matches and sentence["value"]["kind"] in clause["sentenceKinds"]:
                try:
                    term = path_get(sentence["value"], clause["termPath"])
                except (AssertionError, KeyError, IndexError, TypeError):
                    continue
                if not (isinstance(term, dict) and term.get("encoding") == "portable-term-v1" and term.get("sort") == clause["termSort"]):
                    continue
                if clause["termHeadLabel"] is not None and not (term["node"]["kind"] == "application" and term["node"]["label"] == clause["termHeadLabel"]):
                    continue
                site = {"selectorRole": clause["role"], "sentenceLineage": sentence["provenance"]["lineageId"], "termPath": clause["termPath"], "bindings": [{"name": clause["bindingName"], "term": term}]}
                site["siteId"] = digest("k-in-k/site/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": definition["definitionDigest"], "targetLineage": site["sentenceLineage"], "selectorRole": site["selectorRole"], "termPath": site["termPath"], "bindings": site["bindings"]})
                expected_sites.append(site)
                terms[site["siteId"]] = term
    expected_sites.sort(key=lambda site: (sentence_order[site["sentenceLineage"]], site["selectorRole"], canonical(site["termPath"]), site["siteId"]))
    if site_registry["discovery"]["exhaustive"]:
        ok(site_registry["sites"] == expected_sites, "exhaustive mutation site list is not the exact canonical selector result")
    else:
        ok(site_registry["sites"] == expected_sites[:len(site_registry["sites"])], "non-exhaustive mutation site list is not a canonical selector prefix")
    site_ids = [site["siteId"] for site in expected_sites]
    ok(len(site_ids) == len(set(site_ids)), "mutation site registry contains duplicate sites")
    if join is None:
        expected_tuples = [[site["siteId"]] for site in expected_sites]
    else:
        by_role = {role: [site for site in expected_sites if site["selectorRole"] == role] for role in roles}
        expected_tuples = [[site["siteId"] for site in combination] for combination in product(*(by_role[role] for role in roles)) if len({canonical(terms[site["siteId"]]) for site in combination}) == 1 and all(terms[site["siteId"]]["sort"] == join["bindingSort"] for site in combination)]
    if site_registry["discovery"]["exhaustive"]:
        ok(site_registry["tuples"] == expected_tuples, "exhaustive mutation joined tuples are not derived canonically")
    else:
        ok(site_registry["tuples"] == expected_tuples[:len(site_registry["tuples"])], "non-exhaustive mutation joined tuples are not a canonical prefix")
    ok(operator["expectedTupleArity"] == (1 if join is None else len(join["orderedRoles"])), "operator tuple arity differs from selector/join registry")


def validate_observation_bindings(observation: dict[str, Any], definition: dict[str, Any]) -> None:
    validate_observation_paths_and_sorts(observation, definition)


def validate_trace_against_observation(trace: dict[str, Any], observation: dict[str, Any], definition: dict[str, Any]) -> None:
    events = trace["events"]
    cursor = 0
    while cursor < len(events):
        transition = events[cursor]["transitionOrdinal"]
        end = cursor
        while end < len(events) and events[end]["transitionOrdinal"] == transition:
            end += 1
        group = events[cursor:end]
        lineages = {event["origin"]["emittingSentence"]["lineageId"] for event in group}
        ok(len(lineages) == 1, "one observed transition contains multiple emitting sentences")
        lineage = next(iter(lineages))
        selections = [selection for selection in observation["selections"] if lineage in selection["matchedLineages"]]
        ok(len(selections) == 1, "observed transition does not resolve to one selection")
        expected = selections[0]["emissions"]
        ok([event["constructor"] for event in group] == [emission["constructor"] for emission in expected], "observed transition emission sequence/cardinality differs from manifest")
        ok([event["emissionOrdinal"] for event in group] == list(range(len(expected))), "observed transition emission ordinals differ from manifest")
        for event in group:
            validate_event_against_observation(event, observation, definition)
        cursor = end


def portable_observation_installation_outcome(observation: dict[str, Any], definition: dict[str, Any]) -> dict[str, Any]:
    """Model atomic publication at the portable validation boundary."""
    try:
        schema_path = SCHEMAS / "observation-manifest.schema.json"
        schema = load(schema_path)
        validate_schema(observation, schema, schema_path, schema)
        validate_observation_manifest_semantics(observation, definition)
    except AssertionError as error:
        return {"status": "error", "failure": str(error), "installedSelectionIds": [], "installedCount": 0, "outputDefinitionDigest": None}
    return {
        "status": "accepted",
        "installedSelectionIds": [selection["selectionId"] for selection in observation["selections"]],
        "installedCount": len(observation["selections"]),
        "outputDefinitionDigest": observation["outputDefinitionDigest"],
    }


def verify_structural_observation_cases(counter_definition: dict[str, Any]) -> None:
    fixture = load(FIXTURES / "structural-observation-cases.json")
    cases = {case["id"]: case for case in fixture["cases"]}
    ok(len(cases) == len(fixture["cases"]), "duplicate structural observation fixture case")
    schema_path = SCHEMAS / "observation-manifest.schema.json"
    schema = load(schema_path)
    for case in fixture["cases"]:
        observation = case["manifest"]
        validate_schema(observation, schema, schema_path, schema)
        validate_observation_manifest_semantics(observation, counter_definition)
        outcome = portable_observation_installation_outcome(observation, counter_definition)
        ok(outcome["status"] == "accepted" and outcome["installedCount"] == len(observation["selections"]), f"{case['id']}: structural observation fixture was not atomically accepted")

    label_free = cases["label-free-counter-rhs"]["manifest"]
    labeled = cases["labeled-branch-rhs"]["manifest"]
    multi_case = cases["multi-rule-body"]
    multi = multi_case["manifest"]
    counter_lineage, branch_lineage = [sentence["provenance"]["lineageId"] for sentence in ordered_definition_sentences(counter_definition)]
    ok(derive_observation_lineages(label_free["selections"][0]["selector"], counter_definition) == [counter_lineage], "label-free structural RHS selector was not derived by path/sort/head")
    ok(derive_observation_lineages(labeled["selections"][0]["selector"], counter_definition) == [branch_lineage], "labeled structural selector did not derive exactly one lineage")
    ok(multi["selections"][0]["matchedLineages"] == [counter_lineage, branch_lineage], "multi structural selector is not in definition order")
    ok(multi["selections"][0]["selector"]["termHeadLabel"] is None and len(multi["selections"][0]["matchedLineages"]) == 2, "null structural head did not accept all declared-sort terms")
    ok(label_free["selections"][0]["selector"]["label"] is None and counter_definition["modules"][0]["sentences"][0]["provenance"]["label"] is not None, "null structural label was treated as only unlabeled")
    templates = [emission["semanticSite"] for emission in multi["selections"][0]["emissions"]]
    ok(templates[0] is None and templates[1] is not None, "structural fixture does not cover null and site-carrying emissions")
    derived_sites = [derive_event_semantic_site(multi, lineage, templates[1]) for lineage in multi["selections"][0]["matchedLineages"]]
    derived_site_ids = [site["siteId"] for site in derived_sites if site is not None]
    ok(derived_site_ids == multi_case["expectedSiteIds"] and len(set(derived_site_ids)) == 2, "multi-match concrete semantic sites are not distinct lineage-derived identities")

    # All closed selector kinds share the same exact definition-order validator.
    memory_definition = load(FIXTURES / "semantic-definition-memory.json")
    base_observation = load(FIXTURES / "observation-manifest.json")
    label_observation = deepcopy(base_observation)
    label_observation["selections"] = [label_observation["selections"][0]]
    label_constructor = label_observation["selections"][0]["emissions"][0]["constructor"]
    label_observation["eventVocabulary"] = [item for item in label_observation["eventVocabulary"] if item["constructor"] == label_constructor]
    label_observation["selections"][0]["selector"] = {"kind": "label", "label": "write"}
    refresh_observation_identity(label_observation)
    validate_observation_manifest_semantics(label_observation, memory_definition)
    attribute_observation = deepcopy(base_observation)
    attribute_observation["selections"] = [attribute_observation["selections"][0]]
    attribute_constructor = attribute_observation["selections"][0]["emissions"][0]["constructor"]
    attribute_observation["eventVocabulary"] = [item for item in attribute_observation["eventVocabulary"] if item["constructor"] == attribute_constructor]
    attribute_observation["selections"][0]["selector"] = {"kind": "attribute", "name": "transition", "value": None}
    attribute_observation["selections"][0]["matchedLineages"] = [sentence["provenance"]["lineageId"] for sentence in ordered_definition_sentences(memory_definition)]
    attribute_observation["selections"][0]["expectedCardinality"] = 2
    refresh_observation_identity(attribute_observation)
    validate_observation_manifest_semantics(attribute_observation, memory_definition)

    def expect_atomic_rejection(value: dict[str, Any], message: str) -> None:
        refresh_observation_identity(value)
        outcome = portable_observation_installation_outcome(value, counter_definition)
        ok(outcome["status"] == "error" and outcome["installedSelectionIds"] == [] and outcome["installedCount"] == 0 and outcome["outputDefinitionDigest"] is None, message)

    def expect_atomic_schema_rejection(value: dict[str, Any], message: str) -> None:
        expect_schema_rejection(value, "observation-manifest.schema.json", message)
        outcome = portable_observation_installation_outcome(value, counter_definition)
        ok(outcome["status"] == "error" and outcome["installedSelectionIds"] == [] and outcome["installedCount"] == 0 and outcome["outputDefinitionDigest"] is None, f"{message} or published partial output")

    opaque = deepcopy(label_free)
    opaque["selections"][0]["selector"] = {"kind": "structural-pattern", "valueDigest": "f" * 64}
    expect_atomic_schema_rejection(opaque, "opaque structural-pattern selector was accepted")
    escape = deepcopy(label_free)
    escape["selections"][0]["selector"]["kPattern"] = "X => Y"
    expect_atomic_schema_rejection(escape, "structural-term K-pattern escape hatch was accepted")
    for case_id, sentence_kinds in (("empty", []), ("duplicate", ["rule", "rule"]), ("unsupported", ["rule", "syntax"]), ("unsorted", ["rule", "claim"])):
        bad = deepcopy(label_free)
        bad["selections"][0]["selector"]["sentenceKinds"] = sentence_kinds
        if case_id == "unsorted":
            expect_atomic_rejection(bad, "unsorted structural sentence kinds were accepted")
        else:
            expect_atomic_schema_rejection(bad, f"{case_id} structural sentence kinds were accepted")

    for drift, lineages in (
        ("missing", [counter_lineage]),
        ("extra", [counter_lineage, branch_lineage, "f" * 64]),
        ("duplicate", [counter_lineage, counter_lineage]),
        ("reordered", [branch_lineage, counter_lineage]),
    ):
        bad = deepcopy(multi)
        bad["selections"][0]["matchedLineages"] = lineages
        expect_atomic_rejection(bad, f"{drift} self-asserted structural lineage list was accepted or partially installed")
    bad = deepcopy(multi)
    bad["selections"][0]["expectedCardinality"] = 1
    expect_atomic_rejection(bad, "refreshed manifest with wrong structural cardinality was accepted or partially installed")

    malformed_path = deepcopy(label_free)
    malformed_path["selections"][0]["selector"]["termPath"] = [{"kind": "field", "name": "k-pattern"}]
    expect_atomic_schema_rejection(malformed_path, "malformed structural path syntax was accepted")
    for field, value, message in (
        ("termPath", [{"kind": "field", "name": "body"}, {"kind": "field", "name": "rhs"}, {"kind": "argument", "index": 99}], "out-of-range structural path was accepted"),
        ("termSort", "Control", "wrong structural term sort was accepted"),
        ("termHeadLabel", "selected", "wrong structural application head was accepted"),
    ):
        bad = deepcopy(label_free)
        bad["selections"][0]["selector"][field] = value
        expect_atomic_rejection(bad, message)

    concrete_reuse = deepcopy(multi)
    concrete_reuse["selections"][0]["emissions"][1]["semanticSite"]["siteId"] = derived_site_ids[0]
    expect_atomic_schema_rejection(concrete_reuse, "one concrete semantic-site ID was reusable as a multi-match template")
    first_sentence = ordered_definition_sentences(counter_definition)[0]
    site_emission = multi["selections"][0]["emissions"][1]
    event = {
        "index": 0,
        "transitionOrdinal": 0,
        "emissionOrdinal": 1,
        "constructor": site_emission["constructor"],
        "payload": [first_sentence["value"]["body"]],
        "origin": {"emittingSentence": first_sentence["provenance"], "semanticSite": derive_event_semantic_site(multi, counter_lineage, site_emission["semanticSite"])},
    }
    validate_event_against_observation(event, multi, counter_definition)
    changed_template = deepcopy(multi)
    changed_template["selections"][0]["emissions"][1]["semanticSite"]["role"] = "changed-rule-body"
    refresh_observation_identity(changed_template)
    expect_semantic_rejection(lambda value: validate_event_against_observation(event, value, counter_definition), changed_template, "semantic-site role changed without changing the derived event site ID")
    changed_template = deepcopy(multi)
    changed_template["selections"][0]["emissions"][1]["semanticSite"]["termPath"] = [{"kind": "field", "name": "body"}, {"kind": "field", "name": "lhs"}]
    refresh_observation_identity(changed_template)
    expect_semantic_rejection(lambda value: validate_event_against_observation(event, value, counter_definition), changed_template, "semantic-site path changed without changing the derived event site ID")

    one_lineage_only_path = [{"kind": "field", "name": "body"}, {"kind": "field", "name": "rhs"}, {"kind": "argument", "index": 0}, {"kind": "argument", "index": 0}]
    bad = deepcopy(multi)
    bad["selections"][0]["emissions"][1]["semanticSite"]["termPath"] = one_lineage_only_path
    expect_atomic_rejection(bad, "one selected lineage lacked a semantic-site path but installation was published")
    bad = deepcopy(multi)
    bad["selections"][0]["emissions"][0]["payloadBindings"][0] = {"name": "BODY", "sort": "Int", "sourcePath": one_lineage_only_path}
    bad["eventVocabulary"][0]["payloadSorts"] = ["Int"]
    expect_atomic_rejection(bad, "one selected lineage lacked a payload binding but installation was published")

    bad = deepcopy(multi)
    bad["selections"][0]["emissions"][0]["semanticSite"] = deepcopy(site_emission["semanticSite"])
    expect_atomic_rejection(bad, "emitting-sentence declaration accepted a semantic site")
    bad = deepcopy(multi)
    bad["selections"][0]["emissions"][1]["semanticSite"] = None
    expect_atomic_rejection(bad, "site-carrying declaration accepted a missing semantic site")


def official_fixture_schemas() -> dict[str, str]:
    return {
        "artifact-catalog.json": "artifact-catalog.schema.json",
        "observation-manifest.json": "observation-manifest.schema.json",
        "mutation-observation-manifest.json": "observation-manifest.schema.json",
        "observation-installation-result.json": "observation-installation-result.schema.json",
        "corpus-manifest.json": "corpus-manifest.schema.json",
        "corpus-result.json": "corpus-result.schema.json",
        "replay-manifest.json": "replay-manifest.schema.json",
        "write-only-replay-manifest.json": "replay-manifest.schema.json",
        "mutation-replay-manifest.json": "replay-manifest.schema.json",
        "mutation-pattern-replay-manifest.json": "replay-manifest.schema.json",
        "oracle-value-baseline.json": "oracle-value.schema.json",
        "oracle-value-mutant.json": "oracle-value.schema.json",
        "replay-closure.json": "replay-closure.schema.json",
        "pattern-result.json": "pattern-result.schema.json",
        "write-only-pattern-result.json": "pattern-result.schema.json",
        "mutation-pattern-result.json": "pattern-result.schema.json",
        "pattern-plan-write-eventually-load.json": "pattern-plan.schema.json",
        "pattern-plan-single-write.json": "pattern-plan.schema.json",
        "pattern-plan-write-next-load.json": "pattern-plan.schema.json",
        "pattern-plan-write-eventually-load-or-free.json": "pattern-plan.schema.json",
        "pattern-plan-overlapping-load-alternatives.json": "pattern-plan.schema.json",
        "pattern-plan-increment-eventually-branch.json": "pattern-plan.schema.json",
        "pattern-plan-write-then-load-side-condition.json": "pattern-plan.schema.json",
        "pattern-plan-write-then-load-constant-side-condition.json": "pattern-plan.schema.json",
        "pattern-plan-nonlexical-subset-side-condition.json": "pattern-plan.schema.json",
        "pattern-query-write-eventually-load.json": "pattern-query.schema.json",
        "pattern-query-single-write.json": "pattern-query.schema.json",
        "pattern-query-write-next-load.json": "pattern-query.schema.json",
        "pattern-query-write-eventually-load-or-free.json": "pattern-query.schema.json",
        "pattern-query-overlapping-load-alternatives.json": "pattern-query.schema.json",
        "pattern-query-increment-eventually-branch.json": "pattern-query.schema.json",
        "pattern-query-write-then-load-side-condition.json": "pattern-query.schema.json",
        "pattern-query-write-then-load-constant-side-condition.json": "pattern-query.schema.json",
        "pattern-query-nonlexical-subset-side-condition.json": "pattern-query.schema.json",
        "side-condition-conformance-table.json": "side-condition-conformance-table.schema.json",
        "event-trace.json": "event-trace.schema.json",
        "write-only-event-trace.json": "event-trace.schema.json",
        "mutation-event-trace.json": "event-trace.schema.json",
        "terminal-state.json": "terminal-state.schema.json",
        "terminal-state-mutant.json": "terminal-state.schema.json",
        "semantic-crash-mutant.json": "semantic-crash.schema.json",
        "semantic-crash.json": "semantic-crash.schema.json",
        "mutation-operator.json": "mutation-operator.schema.json",
        "mutation-site-registry.json": "mutation-site-registry.schema.json",
        "counter-mutation-operator.json": "mutation-operator.schema.json",
        "counter-mutation-site-registry.json": "mutation-site-registry.schema.json",
        "mutation-manifest.json": "mutation-manifest.schema.json",
        "mutation-execution-policy.json": "mutation-execution-policy.schema.json",
        "structural-diff.json": "structural-diff.schema.json",
        "semantic-definition-memory.json": "semantic-definition.schema.json",
        "semantic-definition-counter.json": "semantic-definition.schema.json",
        "semantic-definition-generated.json": "semantic-definition.schema.json",
        "semantic-definition-identity-output.json": "semantic-definition.schema.json",
    } | bag12_official_fixtures(PACKAGE) | bag14_official_fixtures(PACKAGE) | bag15_official_fixtures(PACKAGE) | bag16_official_fixtures(PACKAGE)


def official_package_schemas() -> dict[str, str]:
    return {
        "claim-boundary.json": "claim-boundary.schema.json",
    }


def verify_interchange_artifacts() -> None:
    fixtures = official_fixture_schemas()
    for fixture, schema in fixtures.items():
        validate_fixture(fixture, schema)
    verify_official_draft_2020_12(fixtures, official_package_schemas())

    artifact_catalog = load(FIXTURES / "artifact-catalog.json")
    execution_catalog = load(FIXTURES / "execution-artifact-catalog.json")
    validate_artifact_catalog(artifact_catalog)
    validate_artifact_catalog(execution_catalog)
    verify_artifact_boundary_adversaries(artifact_catalog)

    execution_policy = load(FIXTURES / "mutation-execution-policy.json")
    mutation_manifest = load(FIXTURES / "mutation-manifest.json")
    validate_mutation_query_roots(mutation_manifest, artifact_catalog)
    ok(execution_policy["policyId"] == digest("k-in-k/mutation-execution-policy/v1", value_without(execution_policy, "policyId")), "mutation execution policy ID derivation")
    drift_policy = deepcopy(execution_policy)
    drift_policy["isolationPolicy"]["observerState"] = "fresh-per-mutant"
    drift_policy["isolationPolicy"]["isolationPolicyDigest"] = digest("k-in-k/isolation-policy/v1", value_without(drift_policy["isolationPolicy"], "isolationPolicyDigest"))
    drift_policy["policyId"] = digest("k-in-k/mutation-execution-policy/v1", value_without(drift_policy, "policyId"))
    expect_semantic_rejection(lambda value: ok(value["isolationPolicy"]["observerState"] == "fresh-per-test-path", "mutation isolation observer state drift"), drift_policy, "mutation isolation drift was accepted after local identity refresh")
    isolation = execution_policy["isolationPolicy"]
    ok(isolation == {"schemaVersion": 1, "isolationPolicyDigest": digest("k-in-k/isolation-policy/v1", value_without(isolation, "isolationPolicyDigest")), "baselineState": "immutable", "mutantState": "fresh-per-mutant", "sharedWritableState": False, "observerState": "fresh-per-test-path"}, "mutation isolation boundary drift")

    observation = load(FIXTURES / "observation-manifest.json")
    memory_definition = load(FIXTURES / "semantic-definition-memory.json")
    validate_observation_manifest_semantics(observation, memory_definition)
    vocabulary = [item["constructor"] for item in observation["eventVocabulary"]]
    ok(len(vocabulary) == len(set(vocabulary)), "duplicate event vocabulary constructor")
    selection_ids: set[str] = set()
    selected_lineages: set[str] = set()
    for selection in observation["selections"]:
        ok(selection["selectionId"] not in selection_ids, "duplicate observation selection ID")
        selection_ids.add(selection["selectionId"])
        ok(len(selection["matchedLineages"]) == selection["expectedCardinality"], "observation cardinality mismatch")
        for lineage in selection["matchedLineages"]:
            ok(lineage not in selected_lineages, "observation selected one lineage twice")
            selected_lineages.add(lineage)
        emissions = selection["emissions"]
        ok([item["declarationOrdinal"] for item in emissions] == list(range(len(emissions))), "observation emission order is not contiguous")
        ok(all(item["constructor"] in vocabulary for item in emissions), "observation emits an undeclared constructor")
        declarations = {item["constructor"]: item for item in observation["eventVocabulary"]}
        for emission in emissions:
            ok([binding["sort"] for binding in emission["payloadBindings"]] == declarations[emission["constructor"]]["payloadSorts"], "emission payload bindings disagree with vocabulary")
        if any(item["constructor"] == "RuleApplied" for item in emissions):
            ok(emissions[0]["constructor"] == "RuleApplied", "RuleApplied must be emitted first")

    installation = load(FIXTURES / "observation-installation-result.json")
    validate_observation_installation_semantics(installation)
    ok(installation["manifestDigest"] == observation["manifestId"], "observation result references another manifest")
    ok(installation["outputDefinitionDigest"] == observation["outputDefinitionDigest"], "observation result output mismatch")
    ok(installation["installedSelectionIds"] == [item["selectionId"] for item in observation["selections"]], "observation result selection coverage mismatch")
    ok(installation["appliedSelectionCount"] == len(observation["selections"]), "observation result applied count mismatch")

    corpus_manifest = load(FIXTURES / "corpus-manifest.json")
    validate_corpus_manifest_semantics(corpus_manifest, execution_catalog)
    ok(corpus_manifest["artifactCatalogDigest"] == execution_catalog["catalogId"], "corpus manifest references another artifact catalog")
    corpus_requirements = [("definition", corpus_manifest["definitionDigest"]), ("compatibility-profile", corpus_manifest["compatibilityProfileDigest"]), ("observation-manifest", corpus_manifest["observationManifestDigest"]), ("execution-profile", corpus_manifest["executionProfileDigest"]), ("solver-profile", corpus_manifest["solverProfileDigest"])]
    corpus_requirements.extend((key["role"], key["digest"]) for root in corpus_manifest["patternQueries"] for key in root.values())
    for test in corpus_manifest["tests"]:
        corpus_requirements.extend([("program", test["programDigest"]), ("parser", test["parserDigest"]), ("options", test["optionsDigest"])])
    require_catalog_entries(execution_catalog, corpus_requirements, "corpus manifest")
    test_ids = [test["testId"] for test in corpus_manifest["tests"]]
    ok(len(test_ids) == len(set(test_ids)), "duplicate corpus test ID")
    ok(corpus_manifest["observationManifestDigest"] == observation["manifestId"], "corpus references another observation manifest")
    validate_corpus_result_semantics(corpus_manifest, load(FIXTURES / "corpus-result.json"))
    empty_corpus = deepcopy(corpus_manifest)
    empty_corpus["tests"] = []
    expect_schema_rejection(empty_corpus, "corpus-manifest.schema.json", "empty corpus manifest was accepted")
    invalid_early_stop = deepcopy(corpus_manifest)
    invalid_early_stop["aggregation"] = {"question": "per-test-exists", "earlyStopAfterMatch": True}
    expect_schema_rejection(invalid_early_stop, "corpus-manifest.schema.json", "per-test aggregation accepted corpus-level early stop")
    contradictory_corpus = load(FIXTURES / "corpus-result.json")
    contradictory_corpus["components"][0]["status"] = "no-match"
    contradictory_corpus["counts"] = {"match": 0, "noMatch": 1, "unknown": 1, "error": 0, "skipped": 0}
    contradictory_corpus["outcome"] = "unknown"
    contradictory_corpus["resultId"] = digest("k-in-k/corpus-result/v1", value_without(contradictory_corpus, "resultId"))
    expect_semantic_rejection(lambda value: validate_corpus_result_semantics(corpus_manifest, value), contradictory_corpus, "component no-match retained a matching path")

    replay = load(FIXTURES / "replay-manifest.json")
    validate_replay_semantics(replay)
    replay_fixtures = [replay, load(FIXTURES / "write-only-replay-manifest.json"), load(FIXTURES / "mutation-replay-manifest.json"), load(FIXTURES / "mutation-pattern-replay-manifest.json")]
    for replay_value in replay_fixtures:
        validate_replay_semantics(replay_value)
        validate_replay_catalog(replay_value, execution_catalog)
    closure = load(FIXTURES / "replay-closure.json")
    expected_closure = sorted((derive_replay_closure(item, execution_catalog) for item in replay_fixtures), key=lambda item: item["replayId"])
    ok(closure["records"] == expected_closure, "published replay closure records are not derived from replay inputs and catalog availability")
    ok(all(item["referentialClosure"] and not item["materialClosure"] and item["externalRequiredInputs"] and item["executionConformance"] == "not-proven" for item in closure["records"]), "current replay recipes do not honestly report external material requirements")
    mutation_replay = next(item for item in replay_fixtures if item["kind"] == "mutation-materialization")
    supplied_diff = next(item for item in mutation_replay["artifacts"] if item["role"] == "structural-diff")
    missing_supplied_catalog = deepcopy(execution_catalog)
    missing_supplied_catalog["entries"] = [entry for entry in missing_supplied_catalog["entries"] if (entry["role"], entry["digest"]) != (supplied_diff["role"], supplied_diff["digest"])]
    missing_record = derive_replay_closure(mutation_replay, missing_supplied_catalog)
    ok(not missing_record["referentialClosure"] and supplied_diff in missing_record["unresolvedConcreteKeys"], "supplied replay output absent from the catalog was accepted")
    mutation_manifest = load(FIXTURES / "mutation-manifest.json")
    ok(mutation_manifest["manifestId"] == digest("k-in-k/mutation-manifest/v1", value_without(mutation_manifest, "manifestId")), "mutation manifest ID derivation")
    ok(mutation_manifest["artifactCatalogDigest"] == artifact_catalog["catalogId"], "mutation manifest references another artifact catalog")

    operator = load(FIXTURES / "mutation-operator.json")
    validate_operator_declaration(operator)
    mutation_requirements = [("definition", mutation_manifest["definitionDigest"]), ("mutation-operator", mutation_manifest["operatorDigest"]), ("mutation-site-registry", mutation_manifest["siteRegistryDigest"]), ("mutation-module", operator["moduleDigest"]), ("mutation-selector", operator["selectorDigest"]), ("mutation-join", operator["joinDigest"]), ("precondition", operator["preconditionDigest"]), ("postcondition", operator["postconditionDigest"]), ("patch-template", operator["patchTemplateDigest"])]
    declaration_keys = [item for test in mutation_manifest["tests"] for item in test["oracleDeclarations"]]
    mutation_requirements.extend((item["role"], item["digest"]) for item in declaration_keys)
    for declaration_key in declaration_keys:
        declaration_entry = next(entry for entry in artifact_catalog["entries"] if (entry["role"], entry["digest"]) == (declaration_key["role"], declaration_key["digest"]))
        declaration = load(resolve_bundled(declaration_entry))
        for field in ("projectionSpec", "comparisonSpec", "kindConfig", "baselineGate"):
            mutation_requirements.extend((item["role"], item["digest"]) for item in walk_artifact_keys(declaration[field]))
    require_catalog_entries(artifact_catalog, mutation_requirements, "mutation manifest/operator")
    counter_operator = load(FIXTURES / "counter-mutation-operator.json")
    validate_operator_declaration(counter_operator)
    counter_site_registry = load(FIXTURES / "counter-mutation-site-registry.json")
    validate_mutation_site_registry(counter_site_registry, load(FIXTURES / "semantic-definition-counter.json"), counter_operator)
    ok(counter_operator["policy"] == "each" and counter_operator["joinDigest"] is None and all(len(site_tuple) == 1 for site_tuple in counter_site_registry["tuples"]), "counter-family registry does not prove join-free each-site interchange")

    structural_diff = load(FIXTURES / "structural-diff.json")
    ok(structural_diff["diffId"] == digest("k-in-k/structural-diff/v1", value_without(structural_diff, "diffId")), "structural diff ID derivation")
    ok(all(entry["targetLineage"] == entry["affectedProvenance"]["lineageId"] for entry in structural_diff["entries"]), "diff provenance does not match target lineage")

    counter_definition = load(FIXTURES / "semantic-definition-counter.json")
    generated_definition = load(FIXTURES / "semantic-definition-generated.json")
    validate_definition_semantics(memory_definition)
    validate_definition_semantics(counter_definition)
    validate_definition_semantics(generated_definition)
    verify_structural_observation_cases(counter_definition)
    expected_compatibility_digest = digest("k-in-k/compatibility-profile/v1", {"profile": memory_definition["family"]["compatibilityProfile"]})
    ok(observation["compatibilityProfileDigest"] == expected_compatibility_digest, "observation compatibility profile does not derive from definition family")
    bad_definition = deepcopy(memory_definition)
    bad_definition["modules"].append(deepcopy(bad_definition["modules"][0]))
    expect_semantic_rejection(validate_definition_graph, bad_definition, "duplicate definition module was accepted")
    bad_definition = deepcopy(memory_definition)
    bad_definition["family"]["entryModules"] = ["MISSING"]
    expect_semantic_rejection(validate_definition_graph, bad_definition, "missing family entry module was accepted")
    bad_definition = deepcopy(memory_definition)
    bad_definition["modules"][0]["imports"] = ["MISSING"]
    expect_semantic_rejection(validate_definition_graph, bad_definition, "dangling definition import was accepted")
    bad_definition = deepcopy(memory_definition)
    bad_definition["modules"][0]["sentences"].append(deepcopy(bad_definition["modules"][0]["sentences"][0]))
    expect_semantic_rejection(validate_definition_graph, bad_definition, "duplicate definition sentence identity was accepted")
    ok(memory_definition["family"]["familyName"] != counter_definition["family"]["familyName"], "fixture families are not distinct")
    ok(observation["inputDefinitionDigest"] == memory_definition["definitionDigest"], "observation manifest references another definition")
    definition_lineages = {sentence["provenance"]["lineageId"] for module in memory_definition["modules"] for sentence in module["sentences"]}
    ok(selected_lineages <= definition_lineages, "observation selection references missing definition lineage")
    validate_observation_bindings(observation, memory_definition)
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["emissions"][0]["payloadBindings"][0]["sort"] = "Int"
    expect_semantic_rejection(lambda value: validate_observation_bindings(value, memory_definition), bad_observation, "observation payload sort drift was accepted")
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["emissions"][0]["payloadBindings"][0]["sourcePath"][-1]["index"] = 99
    expect_semantic_rejection(lambda value: validate_observation_bindings(value, memory_definition), bad_observation, "unresolvable observation payload source path was accepted")
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["emissions"][0]["semanticSite"]["termPath"][-1]["index"] = 99
    expect_semantic_rejection(lambda value: validate_observation_bindings(value, memory_definition), bad_observation, "unresolvable observation semantic-site path was accepted")

    trace = load(FIXTURES / "event-trace.json")
    mutant_trace = load(FIXTURES / "mutation-event-trace.json")
    write_only_trace = load(FIXTURES / "write-only-event-trace.json")
    trace_registry = {digest("k-in-k/event-trace/v1", item): item for item in (trace, write_only_trace, mutant_trace)}
    validate_trace_semantics(trace)
    validate_trace_semantics(mutant_trace)
    validate_trace_semantics(write_only_trace)
    for event in trace["events"]:
        validate_event_against_observation(event, observation, memory_definition)
        matching_selections = [selection for selection in observation["selections"] if event["origin"]["emittingSentence"]["lineageId"] in selection["matchedLineages"]]
        ok(len(matching_selections) == 1 and event["constructor"] in [emission["constructor"] for emission in matching_selections[0]["emissions"]], "event origin/emission is not authorized by observation selection")
    validate_trace_against_observation(trace, observation, memory_definition)
    duplicate_emission_trace = deepcopy(trace)
    duplicate = deepcopy(duplicate_emission_trace["events"][0])
    duplicate["index"] = 1
    duplicate["emissionOrdinal"] = 1
    duplicate_emission_trace["events"].insert(1, duplicate)
    duplicate_emission_trace["events"][2]["index"] = 2
    expect_semantic_rejection(lambda value: validate_trace_against_observation(value, observation, memory_definition), duplicate_emission_trace, "duplicate event emission in one transition was accepted")
    pattern_result = load(FIXTURES / "pattern-result.json")
    validate_pattern_result_semantics(pattern_result, trace_registry)
    write_only_pattern = load(FIXTURES / "write-only-pattern-result.json")
    validate_pattern_result_semantics(write_only_pattern, trace_registry)
    unkeyed_result = deepcopy(pattern_result)
    unkeyed_result.pop("primaryWitness")
    for witness in unkeyed_result["witnesses"]:
        witness.pop("pathKey")
        witness.pop("replayKey")
    for path in unkeyed_result["pathResults"]:
        path["pathKey"] = None
    unkeyed_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(unkeyed_result, "resultId"))
    pattern_schema_path = SCHEMAS / "pattern-result.schema.json"
    pattern_schema = load(pattern_schema_path)
    validate_schema(unkeyed_result, pattern_schema, pattern_schema_path, pattern_schema)
    validate_pattern_result_semantics(unkeyed_result)
    half_keyed = deepcopy(unkeyed_result)
    half_keyed["witnesses"][0]["pathKey"] = "unstable"
    expect_schema_rejection(half_keyed, "pattern-result.schema.json", "half-keyed witness was accepted")
    unexpected_witness_field = deepcopy(pattern_result)
    unexpected_witness_field["witnesses"][0]["unexpected"] = True
    unexpected_witness_field["primaryWitness"]["unexpected"] = True
    expect_schema_rejection(unexpected_witness_field, "pattern-result.schema.json", "oneOf skipped sibling witness constraints")
    early_result = deepcopy(pattern_result)
    early_result["inputs"]["searchPolicy"] = "existential-first"
    early_result["completeCoverage"] = False
    early_result["pathResults"][0]["completeCoverage"] = False
    early_result["pathResults"][0]["stopReason"] = "match-found"
    early_result["pathResults"][0]["executionStopReason"] = "query-satisfied"
    early_result["pathResults"][0]["executionTerminal"] = None
    early_result["primaryWitness"]["stopReason"] = "match-found"
    early_result["primaryWitness"]["executionStopReason"] = "query-satisfied"
    early_result["witnesses"][0]["stopReason"] = "match-found"
    early_result["witnesses"][0]["executionStopReason"] = "query-satisfied"
    early_trace = deepcopy(trace)
    early_trace["complete"] = False
    early_trace["stopReason"] = "query-satisfied"
    early_trace["executionTerminal"] = None
    early_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(early_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    early_trace_digest = digest("k-in-k/event-trace/v1", early_trace)
    early_result["pathResults"][0]["pathIdentityDigest"] = early_trace["pathIdentityDigest"]
    early_result["pathResults"][0]["traceDigest"] = early_trace_digest
    early_result["inputs"]["artifacts"][0]["digest"] = early_trace_digest
    early_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(early_result, "resultId"))
    validate_schema(early_result, pattern_schema, pattern_schema_path, pattern_schema)
    event_schema_path = SCHEMAS / "event-trace.schema.json"
    event_schema = load(event_schema_path)
    validate_schema(early_trace, event_schema, event_schema_path, event_schema)
    validate_trace_semantics(early_trace)
    validate_pattern_result_semantics(early_result, {early_trace_digest: early_trace})
    contradictory_early = deepcopy(early_result)
    contradictory_early["completeCoverage"] = True
    contradictory_early["resultId"] = digest("k-in-k/pattern-result/v1", value_without(contradictory_early, "resultId"))
    expect_semantic_rejection(validate_pattern_result_semantics, contradictory_early, "match-found claimed complete coverage")
    ok(pattern_result["inputs"]["observationManifestDigest"] == observation["manifestId"], "pattern result references another observation manifest")
    ok(pattern_result["inputs"]["definitionDigest"] == observation["inputDefinitionDigest"] == replay["definitionDigest"] == corpus_manifest["definitionDigest"], "definition digests disagree across execution artifacts")
    ok(pattern_result["inputs"]["observerDigest"] == observation["observerDigest"], "observer digests disagree")
    ok(pattern_result["inputs"]["compatibilityProfileDigest"] == observation["compatibilityProfileDigest"] == corpus_manifest["compatibilityProfileDigest"], "compatibility profiles disagree")
    ok(pattern_result["inputs"]["transformationId"] == observation["transformationId"] and replay["transformationDigests"] == [observation["transformationId"]], "observation transformation chain disagrees")
    ok(pattern_query_root(pattern_result["inputs"]) == corpus_manifest["tests"][0]["patternQueries"][0], "pattern source/plan/query roots disagree with corpus test's primary ordered selection")
    ok(pattern_result["queryId"] == replay["queryId"] and pattern_result["inputs"]["executionMode"] == replay["executionMode"] == corpus_manifest["executionMode"], "query entry/execution mode disagree")
    ok(pattern_result["inputs"]["observerDigest"] == replay["observerDigest"] and pattern_result["inputs"]["observationManifestDigest"] == replay["observationManifestDigest"] and pattern_query_root(pattern_result["inputs"]) == pattern_query_root(replay), "replay observation/query identity disagrees")
    ok(pattern_result["inputs"]["programDigest"] == replay["programDigest"] == corpus_manifest["tests"][0]["programDigest"], "program digests disagree")
    ok(pattern_result["inputs"]["parserDigest"] == replay["parserDigest"] == corpus_manifest["tests"][0]["parserDigest"] and pattern_result["inputs"]["startSymbol"] == replay["startSymbol"] == corpus_manifest["tests"][0]["startSymbol"], "parser/start-symbol inputs disagree")
    validate_execution_profile_consistency(pattern_result, replay, corpus_manifest)
    ok(pattern_result["inputs"]["solverProfileDigest"] == replay["solverProfileDigest"] == corpus_manifest["solverProfileDigest"], "solver profiles disagree")
    ok(pattern_result["inputs"]["compatibilityProfileDigest"] == replay["compatibilityProfileDigest"], "replay compatibility profile disagrees")
    ok(pattern_result["inputs"]["optionsDigest"] == replay["optionsDigest"] == corpus_manifest["tests"][0]["optionsDigest"], "execution options disagree")
    ok(pattern_result["inputs"]["searchPolicy"] == replay["searchPolicy"], "search policies disagree")
    ok(pattern_result["inputs"]["replayInvocationDigest"] == replay["invocationDigest"], "pattern result references another replay invocation")
    ok(replay["expectedResultDigest"] == pattern_result["resultId"], "replay expected result disagrees with pattern result")
    ok(pattern_result["bounds"] == replay["bounds"] == corpus_manifest["bounds"], "pattern/corpus/replay bounds disagree")
    ok(trace["testId"] == pattern_result["testId"] == replay["testId"], "test IDs disagree across execution artifacts")
    ok(corpus_result := load(FIXTURES / "corpus-result.json"), "corpus result fixture missing")
    ok(corpus_result["components"][0]["patternResultDigest"] == pattern_result["resultId"], "corpus result references another pattern result")
    validate_corpus_result_semantics(corpus_manifest, corpus_result, {item["resultId"]: item for item in (pattern_result, write_only_pattern)})

    for case_id, failure, expected_outcome, expected_corpus_outcome in (
        ("test-scope-limit-before-path", {"stage": "execution", "classification": "depth-limit", "context": "pattern-test", "scope": "test", "retryability": "same-input-after-resource-change", "semanticEvidence": [], "details": {}}, "unknown", "unknown"),
        ("backend-error-before-path", {"stage": "execution", "classification": "backend-error", "context": "pattern-test", "scope": "test", "retryability": "never", "semanticEvidence": [], "details": {}}, "error", "unknown"),
    ):
        pre_path_pattern = deepcopy(pattern_result)
        pre_path_pattern["outcome"] = expected_outcome
        pre_path_pattern["completeCoverage"] = False
        pre_path_pattern["pathResults"] = []
        pre_path_pattern["witnesses"] = []
        pre_path_pattern.pop("primaryWitness", None)
        pre_path_pattern["failures"] = [failure]
        pre_path_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(pre_path_pattern, "resultId"))
        validate_schema(pre_path_pattern, pattern_schema, pattern_schema_path, pattern_schema)
        validate_pattern_result_semantics(pre_path_pattern)
        pre_path_corpus = deepcopy(corpus_result)
        component = pre_path_corpus["components"][0]
        component.update({"status": expected_outcome, "patternResultDigest": pre_path_pattern["resultId"], "matchingPathOrdinals": [], "matchingPathKeys": [], "pathResults": [], "failures": [failure], "skipReason": None})
        statuses = [item["status"] for item in pre_path_corpus["components"]]
        pre_path_corpus["outcome"] = expected_corpus_outcome
        pre_path_corpus["completeCoverage"] = False
        pre_path_corpus["counts"] = {"match": statuses.count("match"), "noMatch": statuses.count("no-match"), "unknown": statuses.count("unknown"), "error": statuses.count("error"), "skipped": statuses.count("skipped")}
        pre_path_corpus["resultId"] = digest("k-in-k/corpus-result/v1", value_without(pre_path_corpus, "resultId"))
        corpus_schema_path = SCHEMAS / "corpus-result.schema.json"
        corpus_schema = load(corpus_schema_path)
        validate_schema(pre_path_corpus, corpus_schema, corpus_schema_path, corpus_schema)
        validate_corpus_result_semantics(corpus_manifest, pre_path_corpus, {pre_path_pattern["resultId"]: pre_path_pattern, write_only_pattern["resultId"]: write_only_pattern})
        ok(component["status"] == expected_outcome and pre_path_corpus["outcome"] == expected_corpus_outcome, f"{case_id}: corpus did not preserve component status/aggregation")
    replay_artifacts = {artifact["role"]: artifact["digest"] for artifact in replay["artifacts"]}
    ok(replay_artifacts.get("program") == replay["programDigest"] and all(replay_artifacts.get(pattern_result["inputs"][field]["role"]) == pattern_result["inputs"][field]["digest"] for field in ("patternSource", "patternPlan", "patternQuery")), "replay artifacts disagree with invocation query inputs")
    for witness in pattern_result["witnesses"]:
        for event in witness["events"]:
            validate_event_against_observation(event, observation, memory_definition)

    bad_trace = deepcopy(trace)
    bad_trace["events"][1]["index"] = 0
    expect_semantic_rejection(validate_trace_semantics, bad_trace, "duplicate event index was accepted")
    bad_trace = deepcopy(trace)
    bad_trace["stopReason"] = "depth-limit"
    expect_semantic_rejection(validate_trace_semantics, bad_trace, "complete limited trace was accepted")
    bad_result = deepcopy(pattern_result)
    bad_result["primaryWitness"]["eventIndices"] = [0]
    expect_semantic_rejection(validate_pattern_result_semantics, bad_result, "noncanonical primary witness was accepted")
    bad_result = deepcopy(pattern_result)
    bad_result["witnesses"][0]["eventIndices"].reverse()
    bad_result["witnesses"][0]["events"].reverse()
    bad_result["primaryWitness"] = deepcopy(bad_result["witnesses"][0])
    bad_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_result, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, trace_registry), bad_result, "reversed witness indices were accepted")
    bad_result = deepcopy(pattern_result)
    bad_result["witnesses"].append(deepcopy(bad_result["witnesses"][0]))
    bad_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_result, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, trace_registry), bad_result, "duplicate pattern witness was accepted")
    bad_result = deepcopy(pattern_result)
    bad_result["outcome"] = "no-match"
    bad_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_result, "resultId"))
    expect_schema_rejection(bad_result, "pattern-result.schema.json", "no-match with witnesses was schema-valid")
    undeclared_event = deepcopy(trace["events"][0])
    undeclared_event["constructor"] = "undeclaredEvent"
    expect_semantic_rejection(lambda value: validate_event_against_observation(value, observation, memory_definition), undeclared_event, "undeclared event passed observation vocabulary")
    wrong_payload = deepcopy(trace["events"][0])
    wrong_payload["payload"][0]["sort"] = "Int"
    expect_semantic_rejection(lambda value: validate_event_against_observation(value, observation, memory_definition), wrong_payload, "event payload sort mismatch was accepted")
    bad_event = deepcopy(trace["events"][0])
    bad_event["origin"]["emittingSentence"]["module"] = "INVENTED"
    expect_semantic_rejection(lambda value: validate_event_against_observation(value, observation, memory_definition), bad_event, "event with invented provenance was accepted")
    bad_event = deepcopy(trace["events"][0])
    bad_event["origin"]["semanticSite"]["role"] = "invented-role"
    expect_semantic_rejection(lambda value: validate_event_against_observation(value, observation, memory_definition), bad_event, "event with invented semantic site was accepted")
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["selector"]["lineageId"] = "f" * 64
    bad_observation["transformationId"] = digest("k-in-k/transformation/v1", observation_transformation_payload(bad_observation))
    bad_observation["manifestId"] = digest("k-in-k/observation-manifest/v1", value_without(bad_observation, "manifestId"))
    expect_semantic_rejection(lambda value: validate_observation_manifest_semantics(value, memory_definition), bad_observation, "lineage selector identity drift was accepted")
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["selector"] = {"kind": "label", "label": "load"}
    bad_observation["transformationId"] = digest("k-in-k/transformation/v1", observation_transformation_payload(bad_observation))
    bad_observation["manifestId"] = digest("k-in-k/observation-manifest/v1", value_without(bad_observation, "manifestId"))
    expect_semantic_rejection(lambda value: validate_observation_manifest_semantics(value, memory_definition), bad_observation, "label selector accepted self-asserted matches")
    unsupported_structural_selector = deepcopy(observation)
    unsupported_structural_selector["selections"][0]["selector"] = {"kind": "structural-pattern", "valueDigest": "f" * 64}
    expect_schema_rejection(unsupported_structural_selector, "observation-manifest.schema.json", "opaque structural observation selector was accepted in closed v1")
    bad_observation = deepcopy(observation)
    bad_observation["selections"][0]["emissions"][0]["payloadBindings"][1]["name"] = "A"
    expect_semantic_rejection(lambda value: validate_observation_manifest_semantics(value, memory_definition), bad_observation, "duplicate observation binding name was accepted")
    bad_observer = deepcopy(pattern_result)
    bad_observer["inputs"]["observerDigest"] = "f" * 64
    expect_semantic_rejection(lambda value: ok(value["inputs"]["observerDigest"] == observation["observerDigest"], "observer mismatch"), bad_observer, "cross-artifact observer mismatch was accepted")
    bad_replay = deepcopy(replay)
    bad_replay["expectedResultDigest"] = "f" * 64
    expect_semantic_rejection(lambda value: ok(value["expectedResultDigest"] == pattern_result["resultId"], "expected result mismatch"), bad_replay, "cross-artifact replay result mismatch was accepted")
    bad_replay = deepcopy(replay)
    bad_replay["artifacts"].insert(0, {**deepcopy(bad_replay["artifacts"][0]), "digest": "f" * 64})
    refresh_replay_ids(bad_replay)
    expect_semantic_rejection(validate_replay_semantics, bad_replay, "duplicate replay program artifact was accepted")
    bad_replay = deepcopy(replay)
    bad_replay["steps"][2]["inputArtifacts"][0]["digest"] = "f" * 64
    refresh_replay_ids(bad_replay)
    expect_semantic_rejection(validate_replay_semantics, bad_replay, "replay step with dangling input was accepted")
    bad_replay = deepcopy(replay)
    bad_replay["steps"][2]["optionsDigest"] = "f" * 64
    refresh_replay_ids(bad_replay)
    expect_semantic_rejection(validate_replay_semantics, bad_replay, "replay step options drift was accepted")
    bad_replay = deepcopy(replay)
    bad_replay["steps"][2]["inputArtifacts"].reverse()
    refresh_replay_ids(bad_replay)
    expect_semantic_rejection(validate_replay_semantics, bad_replay, "role-swapped replay inputs were accepted")
    incomplete_catalog = deepcopy(artifact_catalog)
    incomplete_catalog["entries"] = [entry for entry in incomplete_catalog["entries"] if not (entry["role"] == "parser" and entry["digest"] == replay["parserDigest"])]
    incomplete_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(incomplete_catalog, "catalogId"))
    validate_artifact_catalog(incomplete_catalog)
    catalog_drift_replay = deepcopy(replay)
    catalog_drift_replay["artifactCatalogDigest"] = incomplete_catalog["catalogId"]
    refresh_replay_ids(catalog_drift_replay)
    expect_semantic_rejection(lambda value: validate_replay_catalog(value, incomplete_catalog), catalog_drift_replay, "replay with a missing typed parser root was accepted")
    for owner in ("pattern", "replay", "corpus"):
        drift_pattern, drift_replay, drift_corpus = deepcopy(pattern_result), deepcopy(replay), deepcopy(corpus_manifest)
        if owner == "pattern":
            drift_pattern["inputs"]["executionProfileDigest"] = "f" * 64
            drift_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(drift_pattern, "resultId"))
        elif owner == "replay":
            drift_replay["executionProfileDigest"] = "f" * 64
            refresh_replay_ids(drift_replay)
        else:
            drift_corpus["executionProfileDigest"] = "f" * 64
            drift_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(drift_corpus, "manifestId"))
        expect_semantic_rejection(lambda _: validate_execution_profile_consistency(drift_pattern, drift_replay, drift_corpus), None, f"{owner} execution-profile drift was accepted after local identity refresh")
    missing_execution_profile_catalog = deepcopy(artifact_catalog)
    missing_execution_profile_catalog["entries"] = [entry for entry in missing_execution_profile_catalog["entries"] if not (entry["role"] == "execution-profile" and entry["digest"] == replay["executionProfileDigest"])]
    missing_execution_profile_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(missing_execution_profile_catalog, "catalogId"))
    validate_artifact_catalog(missing_execution_profile_catalog)
    missing_profile_replay = deepcopy(replay)
    missing_profile_replay["artifactCatalogDigest"] = missing_execution_profile_catalog["catalogId"]
    refresh_replay_ids(missing_profile_replay)
    expect_semantic_rejection(lambda value: validate_replay_catalog(value, missing_execution_profile_catalog), missing_profile_replay, "replay with a missing execution-profile catalog root was accepted")


def verify_corpus_vectors() -> None:
    data = load(VECTORS / "corpus-vectors.json")
    seen: set[str] = set()
    for case in data["cases"]:
        ok(case["id"] not in seen, f"duplicate corpus vector {case['id']}")
        seen.add(case["id"])
        statuses = [component["status"] for component in case["components"]]
        component_outcomes = [status for status in statuses if status != "skipped"]
        derived = aggregate(component_outcomes, case["globalFailure"])
        ok(derived == case["expected"]["outcome"], f"{case['id']}: corpus aggregation")
        complete = not case["globalFailure"] and not any(status in ("unknown", "error", "skipped") for status in statuses)
        ok(complete == case["expected"]["completeCoverage"], f"{case['id']}: corpus completeness")
        test_ids = [component["testId"] for component in case["components"]]
        ok(test_ids == case["expected"]["collectedTestIds"] and len(test_ids) == len(set(test_ids)), f"{case['id']}: corpus order/identity")
        matching = [component["testId"] for component in case["components"] if component["status"] == "match"]
        ok(matching == case["expected"]["matchingTestIds"], f"{case['id']}: matching-test index")
        if case["earlyStopAfterMatch"] and matching:
            match_index = statuses.index("match")
            ok(all(status == "skipped" for status in statuses[match_index + 1:]), f"{case['id']}: early stop did not retain skips")
        elif not case["globalFailure"]:
            ok("skipped" not in statuses, f"{case['id']}: default collection skipped work")
    schema_path = SCHEMAS / "corpus-result.schema.json"
    schema = load(schema_path)
    base_manifest = load(FIXTURES / "corpus-manifest.json")
    for case in data["schemaCases"]:
        manifest = deepcopy(base_manifest)
        manifest["aggregation"] = {"question": case["question"], "earlyStopAfterMatch": case["earlyStopAfterMatch"]}
        test_template = manifest["tests"][0]
        manifest["tests"] = [{**deepcopy(test_template), "testId": component["testId"], "programDigest": digest("k-in-k/corpus-vector-program/v1", component["testId"])} for component in case["components"]]
        manifest["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(manifest, "manifestId"))
        statuses = [component["status"] for component in case["components"]]
        counts = {"match": statuses.count("match"), "noMatch": statuses.count("no-match"), "unknown": statuses.count("unknown"), "error": statuses.count("error"), "skipped": statuses.count("skipped")}
        components = deepcopy(case["components"])
        for component in components:
            for ordinal, path in enumerate(component["pathResults"]):
                path["pathOrdinal"] = ordinal
                path["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", {"caseId": case["id"], "testId": component["testId"], "pathOrdinal": ordinal})
                path["executionStopReason"] = "query-satisfied" if path["stopReason"] == "match-found" else path["stopReason"]
            component["matchingPathOrdinals"] = [path["pathOrdinal"] for path in component["pathResults"] if path["status"] == "match"]
        result = {"schemaVersion": 1, "resultId": "0" * 64, "manifestDigest": manifest["manifestId"], "outcome": aggregate([status for status in statuses if status != "skipped"], bool(case["failures"])), "completeCoverage": not any(status in ("unknown", "error", "skipped") for status in statuses), "components": components, "counts": counts, "failures": deepcopy(case["failures"])}
        result["resultId"] = digest("k-in-k/corpus-result/v1", value_without(result, "resultId"))
        validate_schema(result, schema, schema_path, schema)
        validate_corpus_result_semantics(manifest, result)
        ok(result["outcome"] == case["expected"]["outcome"] and result["completeCoverage"] == case["expected"]["completeCoverage"], f"{case['id']}: schema-shaped corpus outcome")

        if case["id"] == "schema-shaped-shared-setup-error":
            bad = deepcopy(result)
            bad["components"][0] = deepcopy(load(FIXTURES / "corpus-result.json")["components"][0])
            bad["components"][0]["testId"] = manifest["tests"][0]["testId"]
            bad["counts"] = {"match": 1, "noMatch": 0, "unknown": 0, "error": 0, "skipped": 1}
            bad["resultId"] = digest("k-in-k/corpus-result/v1", value_without(bad, "resultId"))
            expect_semantic_rejection(lambda value: validate_corpus_result_semantics(manifest, value), bad, "shared setup failure retained executed results")

    manifest = load(FIXTURES / "corpus-manifest.json")
    base = load(FIXTURES / "corpus-result.json")
    bad = deepcopy(base)
    bad["components"][1]["pathResults"][0]["failures"][0]["scope"] = "campaign"
    bad["resultId"] = digest("k-in-k/corpus-result/v1", value_without(bad, "resultId"))
    expect_semantic_rejection(lambda value: validate_corpus_result_semantics(manifest, value), bad, "path failure with campaign scope was accepted")
    bad = deepcopy(base)
    bad["components"][1]["pathResults"][0]["failures"][0]["classification"] = "time-limit"
    bad["resultId"] = digest("k-in-k/corpus-result/v1", value_without(bad, "resultId"))
    expect_semantic_rejection(lambda value: validate_corpus_result_semantics(manifest, value), bad, "path stop and failure classification drift was accepted")
    for complete in (True, False):
        bad = deepcopy(base)
        path = bad["components"][0]["pathResults"][0]
        path["completeCoverage"] = complete
        path["stopReason"] = "depth-limit"
        path["failures"] = []
        bad["resultId"] = digest("k-in-k/corpus-result/v1", value_without(bad, "resultId"))
        expect_semantic_rejection(lambda value: validate_corpus_result_semantics(manifest, value), bad, f"matching path with unsupported depth stop (complete={complete}) was accepted")


def validate_event_vocabulary_record(record: dict[str, Any]) -> None:
    constructors = record["constructors"]
    names = [item["constructor"] for item in constructors]
    ok(names == sorted(names) and len(names) == len(set(names)), "event vocabulary is not a canonical constructor mapping")
    ok(record["eventVocabularyDigest"] == digest("k-in-k/event-vocabulary/v1", constructors), "event vocabulary semantic digest drift")


def validate_pattern_plan(plan: dict[str, Any], vocabularies: dict[str, dict[str, Any]], catalog_keys: set[tuple[str, str]] | None = None) -> None:
    ok(plan["patternPlanDigest"] == digest("k-in-k/pattern-plan/v1", value_without(plan, "patternPlanDigest")), "pattern plan digest drift")
    by_digest = {record["eventVocabularyDigest"]: record for record in vocabularies.values()}
    ok(plan["eventVocabularyDigest"] in by_digest, "pattern plan resolves against no exact event vocabulary")
    declarations = {item["constructor"]: item for item in by_digest[plan["eventVocabularyDigest"]]["constructors"]}
    variables = plan["variables"]
    variable_sorts = {item["name"]: item["sort"] for item in variables}
    ok(len(variable_sorts) == len(variables), "pattern plan has duplicate variable declarations")
    ok(all(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", item["name"]) for item in variables), "pattern plan variable name is outside witness-binding grammar")
    for arm in plan["arms"]:
        ok(len(arm["relations"]) == len(arm["atoms"]) - 1, "pattern arm relation/atom arity drift")
        bound: set[str] = set()
        for atom in arm["atoms"]:
            ok(atom["constructor"] in declarations, "pattern atom uses an unknown constructor")
            declaration = declarations[atom["constructor"]]
            positions = [clause["position"] for clause in atom["payload"]]
            ok(positions == sorted(set(positions)), "pattern atom payload positions are duplicate or not strictly increasing")
            for clause in atom["payload"]:
                position, variable = clause["position"], clause["variable"]
                ok(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", variable) is not None, "pattern payload variable is outside witness-binding grammar")
                ok(variable in variable_sorts, "pattern atom uses an undeclared variable")
                ok(position < len(declaration["payloadSorts"]), "pattern payload position exceeds constructor arity")
                ok(variable_sorts[variable] == declaration["payloadSorts"][position], "pattern payload/variable/vocabulary sort drift")
                if clause["mode"] == "bind":
                    ok(variable not in bound, "pattern variable is multiply introduced")
                    bound.add(variable)
                else:
                    ok(variable in bound, "pattern variable is used before binding")
        ok(bound == set(variable_sorts), "pattern arm does not bind the complete declared variable interface exactly once")
    side = plan["sideCondition"]
    if side is not None:
        canonical_inputs = [item["name"] for item in variables if item["name"] in side["inputVariables"]]
        ok(side["inputVariables"] == canonical_inputs, "side-condition inputs are not a canonical declared-variable subset")
        if catalog_keys is not None:
            ok((side["artifact"]["role"], side["artifact"]["digest"]) in catalog_keys, "pattern side condition does not resolve through the artifact catalog")


def validate_pattern_query(query: dict[str, Any], plan_registry: dict[str, dict[str, Any]], catalog_keys: set[tuple[str, str]] | None = None) -> None:
    ok(query["queryId"] == digest("k-in-k/pattern-query/v1", value_without(query, "queryId")), "pattern query digest drift")
    ok(query["patternPlan"]["digest"] in plan_registry, "pattern query references an unknown plan")
    if catalog_keys is not None:
        ok((query["patternSource"]["role"], query["patternSource"]["digest"]) in catalog_keys, "pattern query references an unknown source")
        ok((query["patternPlan"]["role"], query["patternPlan"]["digest"]) in catalog_keys, "pattern query references an uncataloged plan")
        ok(("pattern-query", query["queryId"]) in catalog_keys, "pattern query artifact does not resolve through the catalog")


def validate_side_condition_table(table: dict[str, Any]) -> None:
    ok(table["tableDigest"] == digest("k-in-k/side-condition-conformance-table/v1", value_without(table, "tableDigest")), "side-condition table digest drift")
    keys = [(row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]) for row in table["rows"]]
    ok(keys == sorted(keys) and len(keys) == len(set(keys)), "side-condition table keys are duplicate or noncanonical")


def verify_supplied_witness(case: dict[str, Any], derived_witnesses: list[dict[str, Any]]) -> None:
    expected = case["expected"]
    supplied = expected["witness"]
    primary = derived_witnesses[0]
    for field in ("pathKey", "eventIndices", "bindings"):
        ok(primary[field] == supplied.get(field, {}), f"{case['id']}: supplied primary witness {field} differs from denotation")
    if "armOrdinal" in supplied:
        ok(primary["armOrdinal"] == supplied["armOrdinal"], f"{case['id']}: supplied arm ordinal differs from denotation")
    if "pathPredicate" in supplied:
        path = next(path for path in case["paths"] if path.get("pathKey") == supplied["pathKey"])
        ok(supplied["pathPredicate"] == path.get("pathPredicate"), f"{case['id']}: supplied path predicate was not preserved")
    if "allWitnessIndices" in expected:
        ok(expected["allWitnessIndices"] == [witness["eventIndices"] for witness in derived_witnesses], f"{case['id']}: complete witness index set differs from denotation")
    if "allWitnessPaths" in expected:
        ok(expected["allWitnessPaths"] == [witness["pathKey"] for witness in derived_witnesses], f"{case['id']}: complete witness path set differs from denotation")


def term_ref_relation(path: dict[str, Any], left: str, right: str, data: dict[str, Any]) -> str:
    ok(left in data["terms"] and right in data["terms"], "symbolic relation references an unknown term")
    if canonical(data["terms"][left]) == canonical(data["terms"][right]):
        return "equal"
    parent: dict[str, str] = {}

    def find(item: str) -> str:
        parent.setdefault(item, item)
        if parent[item] != item:
            parent[item] = find(parent[item])
        return parent[item]

    for first, second in path.get("equivalences", []):
        ok(first in data["terms"] and second in data["terms"], "equivalence references an unknown term")
        first_root, second_root = find(first), find(second)
        parent[second_root] = first_root
    if find(left) == find(right):
        return "equal"
    unequal = [{find(first), find(second)} for first, second in path.get("inequalities", [])]
    ok(all(first in data["terms"] and second in data["terms"] for pair in path.get("inequalities", []) for first, second in [pair]), "inequality references an unknown term")
    ok(all(len(pair) == 2 for pair in unequal), "malformed inequality relation")
    if {find(left), find(right)} in unequal:
        return "unequal"
    left_symbolic = data["terms"][left]["node"]["kind"] == "variable"
    right_symbolic = data["terms"][right]["node"]["kind"] == "variable"
    return "indeterminate" if left_symbolic or right_symbolic else "unequal"


def validate_path_relations(path: dict[str, Any], data: dict[str, Any]) -> None:
    refs = [ref for relation in ("equivalences", "inequalities") for pair in path.get(relation, []) for ref in pair]
    ok(all(ref in data["terms"] for ref in refs), "path relation references an unknown term")
    for left, right in path.get("inequalities", []):
        ok(term_ref_relation({"equivalences": path.get("equivalences", [])}, left, right, data) != "equal", "contradictory symbolic equality and inequality")


def match_vector_event(atom: dict[str, Any], event: dict[str, Any], bindings: dict[str, str], path: dict[str, Any], data: dict[str, Any]) -> tuple[str, dict[str, str] | None]:
    if event["constructor"] != atom["constructor"]:
        return "no-match", None
    result = dict(bindings)
    for clause in atom["payload"]:
        index, variable = clause["position"], clause["variable"]
        if index >= len(event["payload"]):
            return "no-match", None
        term_ref = event["payload"][index]
        if clause["mode"] == "use":
            if variable not in result:
                return "no-match", None
            relation = term_ref_relation(path, result[variable], term_ref, data)
            if relation == "unequal":
                return "no-match", None
            if relation == "indeterminate":
                return "indeterminate", None
        elif variable in result:
            return "no-match", None
        else:
            result[variable] = term_ref
    return "match", result


def denotational_vector_result(case: dict[str, Any], data: dict[str, Any]) -> tuple[list[dict[str, Any]], bool]:
    query = data["queries"][case["query"]]
    plan = next(plan for plan in data["plans"].values() if plan["patternPlanDigest"] == query["patternPlan"]["digest"])
    witnesses: list[dict[str, Any]] = []
    indeterminate = False
    table = {(row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]): row["result"] for row in data["sideConditionTable"]["rows"]}
    stable_path_keys = case.get("stablePathKeys", True)
    for path_ordinal, path in enumerate(case["paths"]):
        events = [data["events"][reference] for reference in path["eventRefs"]]
        path_key = path.get("pathKey")
        path_order = path_key if stable_path_keys else digest("k-in-k/unkeyed-vector-path/v1", value_without(path, "pathKey", "replayKey"))

        def extend(arm: dict[str, Any], arm_ordinal: int, atom_ordinal: int, indices: list[int], bindings: dict[str, str]) -> None:
            nonlocal indeterminate
            if atom_ordinal == len(arm["atoms"]):
                ordered_bindings = {variable["name"]: bindings[variable["name"]] for variable in plan["variables"]}
                if plan["sideCondition"] is not None:
                    binding_value = [{"name": name, "term": data["terms"][bindings[name]]} for name in plan["sideCondition"]["inputVariables"]]
                    predicate_ref = path.get("pathPredicate", "true")
                    ok(predicate_ref in data["terms"], "side-condition path predicate reference is unknown")
                    key = (plan["sideCondition"]["artifact"]["digest"], digest("k-in-k/bindings/v1", binding_value), digest("k-in-k/path-predicate/v1", data["terms"][predicate_ref]))
                    result = table.get(key, "unknown")
                    if result == "false":
                        return
                    if result == "unknown":
                        indeterminate = True
                        return
                witnesses.append({"pathKey": path_key, "pathOrder": path_order, "eventIndices": indices, "bindings": ordered_bindings, "armOrdinal": arm_ordinal})
                return
            if not indices:
                candidates = range(len(events))
            elif arm["relations"][atom_ordinal - 1] == "next-event":
                candidates = [indices[-1] + 1]
            else:
                candidates = range(indices[-1] + 1, len(events))
            for index in candidates:
                if index >= len(events):
                    continue
                status, next_bindings = match_vector_event(arm["atoms"][atom_ordinal], events[index], bindings, path, data)
                indeterminate |= status == "indeterminate"
                if status == "match" and next_bindings is not None:
                    extend(arm, arm_ordinal, atom_ordinal + 1, [*indices, index], next_bindings)

        for arm_ordinal, arm in enumerate(plan["arms"]):
            extend(arm, arm_ordinal, 0, [], {})
    ordered = sorted(witnesses, key=lambda witness: (witness["pathOrder"], tuple(witness["eventIndices"]), canonical(witness["bindings"]), witness["armOrdinal"]))
    return ordered, indeterminate


def aggregate(components: list[str], global_error: bool) -> str:
    if global_error:
        return "error"
    if "match" in components:
        return "match"
    if any(item in ("unknown", "error") for item in components):
        return "unknown"
    return "no-match"


def verify_execution() -> None:
    data = load(VECTORS / "execution-pattern-vectors.json")
    catalog = load(FIXTURES / "artifact-catalog.json")
    catalog_keys = {(entry["role"], entry["digest"]) for entry in catalog["entries"]}
    for vocabulary in data["eventVocabularies"].values():
        validate_event_vocabulary_record(vocabulary)
    plan_registry = {plan["patternPlanDigest"]: plan for plan in data["plans"].values()}
    ok(len(plan_registry) == len(data["plans"]), "duplicate normalized plan identity")
    for plan in data["plans"].values():
        validate_official_instance(plan, "pattern-plan.schema.json")
        validate_pattern_plan(plan, data["eventVocabularies"], catalog_keys)
    query_ids: set[str] = set()
    for name, query in data["queries"].items():
        validate_official_instance(query, "pattern-query.schema.json")
        validate_pattern_query(query, plan_registry, catalog_keys)
        ok(query["exportedName"] == name and query["queryId"] not in query_ids, "query registry name/identity drift")
        query_ids.add(query["queryId"])
        resolve_pattern_query_root({"patternSource": query["patternSource"], "patternPlan": query["patternPlan"], "patternQuery": {"role": "pattern-query", "digest": query["queryId"]}}, catalog, data["eventVocabularies"])
    validate_side_condition_table(data["sideConditionTable"])
    ok(data["compilerConformance"] == {"status": "not-proven", "futureRequirement": "rust-k-pattern-compiler-receipt"}, "portable fixtures promoted compiler conformance")
    ok(all(item["status"] == "historical-only" and item["retiredSemantics"] == "legacy-exact-trace" for item in data["historicalRetiredWholeTraceEvidence"]), "retired whole-trace evidence escaped its historical boundary")
    ok(not ({item["id"] for item in data["historicalRetiredWholeTraceEvidence"]} & {case["id"] for case in data["cases"]}), "retired whole-trace evidence entered plan denotation cases")
    case_ids: set[str] = set()
    for case in data["cases"]:
        ok(case["id"] not in case_ids, f"duplicate execution case {case['id']}")
        case_ids.add(case["id"])
        stable_path_keys = case.get("stablePathKeys", True)
        path_keys: set[str] = set()
        for path in case["paths"]:
            validate_path_relations(path, data)
            ok("replayKey" not in path, f"{case['id']}: path-level replay key was accepted as witness ordering authority")
            if stable_path_keys:
                ok(isinstance(path.get("pathKey"), str) and path["pathKey"] not in path_keys, f"{case['id']}: missing or duplicate stable path key")
                path_keys.add(path["pathKey"])
            else:
                ok("pathKey" not in path and "replayKey" not in path, f"{case['id']}: unstable mode exposed a path/replay key")
            ok(all(ref in data["events"] for ref in path["eventRefs"]), f"{case['id']}: unknown event ref")
            if path["complete"]:
                ok(path["stopReason"] in ("terminal", "stuck"), f"{case['id']}: complete path has limit stop")
            else:
                ok(path["stopReason"] not in ("terminal", "stuck"), f"{case['id']}: incomplete path has complete stop")
        outcome = case["expected"]["outcome"]
        derived_witnesses, indeterminate = denotational_vector_result(case, data) if not case.get("inputFailure") else ([], False)
        if case.get("inputFailure"):
            derived_outcome = "error"
        elif derived_witnesses:
            derived_outcome = "match"
        elif indeterminate or any(not path["complete"] for path in case["paths"]):
            derived_outcome = "unknown"
        else:
            derived_outcome = "no-match"
        ok(derived_outcome == outcome, f"{case['id']}: denotational matcher derived {derived_outcome}, expected {outcome}")
        derived_coverage = False if case.get("inputFailure") else all(path["complete"] for path in case["paths"])
        ok(case["expected"]["completeCoverage"] == derived_coverage, f"{case['id']}: completeCoverage is inconsistent")
        if outcome == "match":
            if stable_path_keys:
                ok("witness" in case["expected"], f"{case['id']}: keyed match without primary witness")
                verify_supplied_witness(case, derived_witnesses)
                primary = derived_witnesses[0]
                supplied = case["expected"]["witness"]
                ok(primary["pathKey"] == supplied["pathKey"] and primary["eventIndices"] == supplied["eventIndices"] and primary["bindings"] == supplied.get("bindings", {}), f"{case['id']}: supplied witness differs from denotational primary")
                if "armOrdinal" in supplied:
                    ok(primary["armOrdinal"] == supplied["armOrdinal"], f"{case['id']}: alternative tie-break mismatch")
            else:
                ok(case["expected"].get("primaryWitness") is None and "witness" not in case["expected"], f"{case['id']}: unstable mode selected a primary")
                if "allWitnessIndices" in case["expected"]:
                    ok(case["expected"]["allWitnessIndices"] == [witness["eventIndices"] for witness in derived_witnesses], f"{case['id']}: unstable mode did not retain all witnesses")
                if case["expected"].get("permutationInvariant"):
                    def normalize_unkeyed_paths(paths: list[dict[str, Any]]) -> list[dict[str, Any]]:
                        normalized = [{"pathIdentityDigest": digest("k-in-k/unkeyed-vector-path/v1", value_without(path, "pathKey", "replayKey")), **deepcopy(value_without(path, "pathKey", "replayKey"))} for path in paths]
                        identities = [path["pathIdentityDigest"] for path in normalized]
                        ok(len(identities) == len(set(identities)), f"{case['id']}: duplicate unkeyed paths were not coalesced/rejected")
                        normalized.sort(key=lambda path: path["pathIdentityDigest"])
                        for ordinal, path in enumerate(normalized):
                            path["pathOrdinal"] = ordinal
                        return normalized
                    permuted = deepcopy(case)
                    permuted["paths"].reverse()
                    permuted_witnesses, permuted_indeterminate = denotational_vector_result(permuted, data)
                    ok(normalize_unkeyed_paths(case["paths"]) == normalize_unkeyed_paths(permuted["paths"]), f"{case['id']}: full unkeyed path list depends on scheduler order")
                    ok(derived_witnesses == permuted_witnesses and indeterminate == permuted_indeterminate, f"{case['id']}: full unkeyed witness list depends on scheduler order")
                    ok(len(derived_witnesses) == case["expected"]["allWitnessCount"], f"{case['id']}: unkeyed equivalence vector lost witnesses")
        elif outcome == "no-match":
            ok(all(path["complete"] for path in case["paths"]), f"{case['id']}: no-match without exhaustive paths")
            ok("witness" not in case["expected"], f"{case['id']}: no-match has witness")
        elif outcome == "unknown":
            ok(any(not path["complete"] for path in case["paths"]), f"{case['id']}: unknown without incompleteness")
            ok("witness" not in case["expected"], f"{case['id']}: unknown has witness")
            incomplete_reasons = [path["stopReason"] for path in case["paths"] if not path["complete"]]
            ok(case["expected"].get("failure") in incomplete_reasons, f"{case['id']}: unknown failure differs from incomplete path stops")
        else:
            ok("inputFailure" in case, f"{case['id']}: error lacks structured failure")
            ok(case["expected"].get("failure") == case["inputFailure"]["classification"], f"{case['id']}: error failure differs from its input failure")
        ok("sideConditionResult" not in case, f"{case['id']}: case-local side-condition assertion survived")
        if case.get("searchPolicy", "exhaustive") == "existential-first":
            ok(outcome == "match" and not case["expected"]["completeCoverage"] and case["expected"].get("searchStopped"), f"{case['id']}: existential stop metadata")
            ok(any(path["stopReason"] == "match-found" for path in case["paths"]), f"{case['id']}: existential stop lacks match-found path")
            ok(case["expected"].get("replaySearchPolicy") == "existential-first", f"{case['id']}: replay omitted search policy")
    for item in data["aggregationCases"]:
        ok(aggregate(item["components"], item["globalError"]) == item["expected"], "aggregation truth table mismatch")
    contradictory = deepcopy(next(case for case in data["cases"] if case["id"] == "distinct-symbolic-terms-proven-unequal"))
    contradictory["paths"][0]["equivalences"] = [["symbolicX", "symbolicY"]]
    expect_semantic_rejection(lambda value: validate_path_relations(value["paths"][0], data), contradictory, "contradictory symbolic relations were accepted")


def verify_bag11_adversaries() -> None:
    data = load(VECTORS / "execution-pattern-vectors.json")
    vocabularies = data["eventVocabularies"]
    base_plan = deepcopy(data["plans"]["write-eventually-load"])
    side_plan = deepcopy(data["plans"]["write-then-load-side-condition"])
    constant_side_plan = deepcopy(data["plans"]["write-then-load-constant-side-condition"])
    subset_plan = deepcopy(data["plans"]["nonlexical-subset-side-condition"])
    query = deepcopy(data["queries"]["write-eventually-load"])
    # BAG-11 corpus/replay identities are immutable and resolve through the
    # execution-catalog snapshot.  BAG-12 mutation declarations use the live
    # mutation catalog below; do not collapse those two authorities.
    catalog = load(FIXTURES / "execution-artifact-catalog.json")
    catalog_keys = {(entry["role"], entry["digest"]) for entry in catalog["entries"]}
    plan_schema_path = SCHEMAS / "pattern-plan.schema.json"
    plan_schema = load(plan_schema_path)

    def rehash_plan(plan: dict[str, Any]) -> None:
        plan["patternPlanDigest"] = digest("k-in-k/pattern-plan/v1", value_without(plan, "patternPlanDigest"))

    def rehash_query(value: dict[str, Any]) -> None:
        value["queryId"] = digest("k-in-k/pattern-query/v1", value_without(value, "queryId"))

    for label, mutate in (
        ("unknown plan field", lambda value: value.update({"extension": {}})),
        ("recursive plan", lambda value: value.update({"recursive": {"self": True}})),
        ("negative plan", lambda value: value.update({"negation": True})),
        ("universal plan", lambda value: value.update({"universal": True})),
        ("unknown atom kind", lambda value: value["arms"][0]["atoms"][0].update({"kind": "event"})),
    ):
        bad = deepcopy(base_plan)
        mutate(bad)
        expect_schema_rejection(bad, "pattern-plan.schema.json", f"{label} was accepted")
    for label, path, replacement in (
        ("empty pattern", ["arms"], []),
        ("zero-length component", ["arms", 0, "atoms"], []),
        ("unknown relation operator", ["arms", 0, "relations", 0], "until"),
        ("unknown bind/use mode", ["arms", 0, "atoms", 0, "payload", 0, "mode"], "capture"),
    ):
        bad = deepcopy(base_plan)
        cursor: Any = bad
        for component in path[:-1]:
            cursor = cursor[component]
        cursor[path[-1]] = replacement
        expect_schema_rejection(bad, "pattern-plan.schema.json", f"{label} was accepted")
    for label, mutate in (
        ("lowercase declared variable", lambda value: value["variables"][0].update({"name": "a"})),
        ("punctuated payload variable", lambda value: value["arms"][0]["atoms"][0]["payload"][0].update({"variable": "A-B"})),
    ):
        bad = deepcopy(base_plan)
        mutate(bad)
        expect_schema_rejection(bad, "pattern-plan.schema.json", f"{label} escaped witness-binding grammar")

    semantic_mutations: list[tuple[str, Any]] = [
        ("unknown constructor", lambda value: value["arms"][0]["atoms"][0].update({"constructor": "missingEvent"})),
        ("payload out of range", lambda value: value["arms"][0]["atoms"][0]["payload"][0].update({"position": 9})),
        ("duplicate payload index", lambda value: value["arms"][0]["atoms"][0]["payload"].append({"position": 0, "mode": "use", "variable": "A"})),
        ("cross-sort variable", lambda value: value["variables"][0].update({"sort": "Int"})),
        ("unbound use", lambda value: value["arms"][0]["atoms"][0]["payload"][0].update({"mode": "use"})),
        ("rebound variable", lambda value: value["arms"][0]["atoms"][1]["payload"][0].update({"mode": "bind"})),
        ("unused variable", lambda value: value["variables"].append({"name": "B", "sort": "Address"})),
        ("relation arity drift", lambda value: value["arms"][0]["relations"].append("eventually-after")),
        ("another vocabulary", lambda value: value.update({"eventVocabularyDigest": vocabularies["counter"]["eventVocabularyDigest"]})),
    ]
    for label, mutate in semantic_mutations:
        bad = deepcopy(base_plan)
        mutate(bad)
        rehash_plan(bad)
        expect_semantic_rejection(lambda value: validate_pattern_plan(value, vocabularies), bad, f"{label} was accepted after local digest refresh")

    arity_vocabularies = deepcopy(vocabularies)
    memory = arity_vocabularies["memory"]
    next(item for item in memory["constructors"] if item["constructor"] == "memoryWrite")["payloadSorts"] = []
    memory["eventVocabularyDigest"] = digest("k-in-k/event-vocabulary/v1", memory["constructors"])
    arity_plan = deepcopy(base_plan)
    arity_plan["eventVocabularyDigest"] = memory["eventVocabularyDigest"]
    rehash_plan(arity_plan)
    expect_semantic_rejection(lambda value: validate_pattern_plan(value, arity_vocabularies), arity_plan, "constructor arity drift was accepted")

    bad = deepcopy(side_plan)
    bad["sideCondition"]["resultSort"] = "Int"
    expect_schema_rejection(bad, "pattern-plan.schema.json", "side-condition result-sort drift was accepted")
    bad = deepcopy(side_plan)
    bad["sideCondition"]["artifact"]["digest"] = "f" * 64
    rehash_plan(bad)
    ok(bad["patternPlanDigest"] != side_plan["patternPlanDigest"], "condition artifact drift did not change plan identity")
    expect_semantic_rejection(lambda value: validate_pattern_plan(value, vocabularies, catalog_keys), bad, "rehashed plan with unknown side-condition artifact was accepted")
    validate_official_instance(constant_side_plan, "pattern-plan.schema.json")
    validate_pattern_plan(constant_side_plan, vocabularies, catalog_keys)
    ok(constant_side_plan["sideCondition"]["inputVariables"] == [], "constant side condition lost its empty declared interface")
    validate_official_instance(subset_plan, "pattern-plan.schema.json")
    validate_pattern_plan(subset_plan, vocabularies, catalog_keys)
    ok([item["name"] for item in subset_plan["variables"]] == ["VALUE", "ADDRESS"] and subset_plan["sideCondition"]["inputVariables"] == ["VALUE"], "nonlexical declaration order or side-condition subset was normalized")
    bad = deepcopy(subset_plan)
    bad["sideCondition"]["inputVariables"] = ["ADDRESS", "VALUE"]
    rehash_plan(bad)
    expect_semantic_rejection(lambda value: validate_pattern_plan(value, vocabularies, catalog_keys), bad, "side-condition subset order differing from declaration order was accepted")

    table = data["sideConditionTable"]
    rows = {(row["condition"]["digest"], row["bindingsDigest"], row["pathPredicateDigest"]): row["result"] for row in table["rows"]}
    true_row = next(row for row in table["rows"] if row["result"] == "true")
    exact_key = (true_row["condition"]["digest"], true_row["bindingsDigest"], true_row["pathPredicateDigest"])
    ok(rows.get(exact_key, "unknown") == "true", "exact finite side-condition row did not resolve true")
    ok(rows.get((exact_key[0], "f" * 64, exact_key[2]), "unknown") == "unknown", "row for another binding was treated as evidence")
    ok(rows.get((exact_key[0], exact_key[1], "f" * 64), "unknown") == "unknown", "row for another path predicate was treated as evidence")
    condition_digest = side_plan["sideCondition"]["artifact"]["digest"]
    predicate_digest = digest("k-in-k/path-predicate/v1", data["terms"]["true"])
    empty_digest = digest("k-in-k/bindings/v1", [])
    subset_digest = digest("k-in-k/bindings/v1", [{"name": "VALUE", "term": data["terms"]["v7"]}])
    full_subset_witness_digest = digest("k-in-k/bindings/v1", [{"name": "VALUE", "term": data["terms"]["v7"]}, {"name": "ADDRESS", "term": data["terms"]["a"]}])
    ok(rows[(condition_digest, empty_digest, predicate_digest)] == "true", "constant side condition did not hash the empty declared interface")
    ok(rows[(condition_digest, subset_digest, predicate_digest)] == "true", "subset side condition did not hash exactly its declared variable subset")
    ok(full_subset_witness_digest != subset_digest and rows.get((condition_digest, full_subset_witness_digest, predicate_digest), "unknown") == "unknown", "undeclared witness bindings leaked into the side-condition table key")
    subset_case = next(case for case in data["cases"] if case["id"] == "subset-side-condition-preserves-nonlexical-declaration-order")
    subset_witnesses, subset_indeterminate = denotational_vector_result(subset_case, data)
    ok(not subset_indeterminate and list(subset_witnesses[0]["bindings"]) == ["VALUE", "ADDRESS"], "end-to-end witness did not retain nonlexical plan declaration order")
    reordered_subset_data = deepcopy(data)
    reordered_subset = reordered_subset_data["plans"]["nonlexical-subset-side-condition"]
    reordered_subset["variables"].reverse()
    rehash_plan(reordered_subset)
    reordered_subset_query = reordered_subset_data["queries"]["nonlexical-subset-side-condition"]
    reordered_subset_query["patternPlan"]["digest"] = reordered_subset["patternPlanDigest"]
    rehash_query(reordered_subset_query)
    validate_pattern_plan(reordered_subset, vocabularies)
    reordered_witnesses, _ = denotational_vector_result(subset_case, reordered_subset_data)
    ok(list(reordered_witnesses[0]["bindings"]) == ["ADDRESS", "VALUE"] and reordered_subset["patternPlanDigest"] != subset_plan["patternPlanDigest"], "variable declaration reordering did not change plan identity and witness order")

    missing_entry = deepcopy(query)
    missing_entry.pop("entryModule")
    expect_schema_rejection(missing_entry, "pattern-query.schema.json", "missing query entry module was accepted")
    missing_name = deepcopy(query)
    missing_name["exportedName"] = ""
    expect_schema_rejection(missing_name, "pattern-query.schema.json", "missing exported query name was accepted")
    drift_query = deepcopy(query)
    drift_query["queryId"] = "f" * 64
    expect_semantic_rejection(lambda value: validate_pattern_query(value, {base_plan["patternPlanDigest"]: base_plan}), drift_query, "query digest drift was accepted")
    for field, role in (("patternSource", "pattern-source"), ("patternPlan", "pattern-plan")):
        drift = deepcopy(query)
        drift[field] = {"role": role, "digest": "f" * 64}
        expect_semantic_rejection(lambda value: validate_pattern_query(value, {base_plan["patternPlanDigest"]: base_plan}), drift, f"query {field} drift was accepted without a new query ID")
    unknown_source = deepcopy(query)
    unknown_source["patternSource"]["digest"] = "f" * 64
    rehash_query(unknown_source)
    expect_semantic_rejection(lambda value: validate_pattern_query(value, {base_plan["patternPlanDigest"]: base_plan}, catalog_keys), unknown_source, "rehashed query with an unknown source artifact was accepted")
    single_query = data["queries"]["single-write"]
    spliced_root = {"patternSource": deepcopy(query["patternSource"]), "patternPlan": deepcopy(single_query["patternPlan"]), "patternQuery": {"role": "pattern-query", "digest": query["queryId"]}}
    expect_semantic_rejection(lambda value: resolve_pattern_query_root(value, catalog, vocabularies), spliced_root, "consumer accepted a source/plan/query triple spliced across resolved query artifacts")

    alternative = deepcopy(data["plans"]["write-eventually-load-or-free"])
    reordered = deepcopy(alternative)
    reordered["arms"].reverse()
    rehash_plan(reordered)
    ok(reordered["patternPlanDigest"] != alternative["patternPlanDigest"], "alternative reordering did not change plan identity")
    alternative_query = deepcopy(data["queries"]["write-eventually-load-or-free"])
    ok(alternative_query["patternPlan"]["digest"] != reordered["patternPlanDigest"], "reordered alternative silently retained the old query root")

    plan_drift = deepcopy(base_plan)
    plan_drift["arms"][0]["relations"][0] = "next-event"
    rehash_plan(plan_drift)
    validate_pattern_plan(plan_drift, vocabularies)
    plan_drift_query = deepcopy(query)
    plan_drift_query["patternPlan"]["digest"] = plan_drift["patternPlanDigest"]
    rehash_query(plan_drift_query)
    ok(plan_drift["patternPlanDigest"] != base_plan["patternPlanDigest"] and plan_drift_query["queryId"] != query["queryId"], "plan-only change did not change plan/query identity")
    name_only_query = deepcopy(query)
    name_only_query["exportedName"] = "writeEventuallyLoadSecondName"
    rehash_query(name_only_query)
    ok(name_only_query["patternSource"] == query["patternSource"] and name_only_query["patternPlan"] == query["patternPlan"] and name_only_query["queryId"] != query["queryId"], "two names in one source/plan collapsed to one query ID")

    corpus = load(FIXTURES / "corpus-manifest.json")
    replay = load(FIXTURES / "replay-manifest.json")

    def root_for(value: dict[str, Any]) -> dict[str, Any]:
        return {"patternSource": deepcopy(value["patternSource"]), "patternPlan": deepcopy(value["patternPlan"]), "patternQuery": {"role": "pattern-query", "digest": value["queryId"]}}

    def corpus_with(value: dict[str, Any]) -> dict[str, Any]:
        changed = deepcopy(corpus)
        changed["tests"][0]["patternQueries"][0] = root_for(value)
        changed["patternQueries"] = [deepcopy(root) for test in changed["tests"] for root in test["patternQueries"]]
        changed["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(changed, "manifestId"))
        return changed

    def replay_with(value: dict[str, Any]) -> dict[str, Any]:
        changed = deepcopy(replay)
        root = root_for(value)
        changed.update(root)
        changed["queryId"] = value["queryId"]
        changed["artifacts"] = [artifact for artifact in changed["artifacts"] if artifact["role"] not in {"pattern-source", "pattern-plan", "pattern-query"}] + list(deepcopy(root).values())
        changed["steps"][3]["inputArtifacts"] = [changed["steps"][2]["expectedArtifacts"][0], *list(deepcopy(root).values())]
        refresh_replay_ids(changed)
        return changed

    for changed_query in (name_only_query, plan_drift_query):
        ok(corpus_with(changed_query)["manifestId"] != corpus["manifestId"], "query change did not reach corpus identity")
        changed_replay = replay_with(changed_query)
        ok(changed_replay["invocationDigest"] != replay["invocationDigest"] and changed_replay["replayId"] != replay["replayId"], "query change did not reach replay identities")

    validate_corpus_manifest_semantics(corpus, catalog)
    ok(len(corpus["tests"][0]["patternQueries"]) == 3 and corpus["tests"][0]["patternQueries"][0] == corpus["tests"][0]["patternQueries"][2], "corpus positive does not preserve repeated per-test oracle query selections")
    bad_corpus = deepcopy(corpus)
    bad_corpus["patternQueries"] = list(reversed(bad_corpus["patternQueries"]))
    bad_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(bad_corpus, "manifestId"))
    expect_semantic_rejection(lambda value: validate_corpus_manifest_semantics(value, catalog), bad_corpus, "corpus top roots were reordered away from per-test selections")
    bad_corpus = deepcopy(corpus)
    bad_corpus["patternQueries"] = list({root["patternQuery"]["digest"]: root for root in bad_corpus["patternQueries"]}.values())
    bad_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(bad_corpus, "manifestId"))
    expect_semantic_rejection(lambda value: validate_corpus_manifest_semantics(value, catalog), bad_corpus, "corpus top roots deduplicated repeated per-oracle selections")
    bad_corpus = deepcopy(corpus)
    bad_corpus["tests"][0]["patternQueries"][0], bad_corpus["tests"][0]["patternQueries"][1] = bad_corpus["tests"][0]["patternQueries"][1], bad_corpus["tests"][0]["patternQueries"][0]
    bad_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(bad_corpus, "manifestId"))
    expect_semantic_rejection(lambda value: validate_corpus_manifest_semantics(value, catalog), bad_corpus, "corpus per-test selections changed order without changing top roots")
    bad_corpus = deepcopy(corpus)
    bad_corpus["tests"][0]["patternQueries"][0]["patternPlan"] = deepcopy(single_query["patternPlan"])
    bad_corpus["patternQueries"] = [deepcopy(root) for test in bad_corpus["tests"] for root in test["patternQueries"]]
    bad_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(bad_corpus, "manifestId"))
    expect_semantic_rejection(lambda value: validate_corpus_manifest_semantics(value, catalog), bad_corpus, "rehashed corpus accepted a spliced consumer query triple")

    for fixture, schema_name, field in (
        (corpus, "corpus-manifest.schema.json", "patternQueries"),
        (replay, "replay-manifest.schema.json", "patternSource"),
    ):
        bad = deepcopy(fixture)
        bad.pop(field)
        expect_schema_rejection(bad, schema_name, f"{schema_name} omitted required per-query identity")
    bad = deepcopy(corpus)
    bad["tests"][0].pop("patternQueries")
    expect_schema_rejection(bad, "corpus-manifest.schema.json", "corpus test omitted its ordered per-oracle query selections")
    for field in ("patternPlan", "patternQuery"):
        bad = deepcopy(replay)
        bad.pop(field)
        expect_schema_rejection(bad, "replay-manifest.schema.json", f"pattern replay omitted {field}")

    mutation = load(FIXTURES / "mutation-manifest.json")
    mutation_catalog = load(FIXTURES / "artifact-catalog.json")
    validate_mutation_query_roots(mutation, mutation_catalog)
    missing_test_roots = deepcopy(mutation)
    missing_test_roots["tests"][0].pop("patternQueries")
    expect_schema_rejection(missing_test_roots, "mutation-manifest.schema.json", "mutation test invocation omitted ordered query selections")
    missing_declaration = deepcopy(mutation)
    missing_declaration["tests"][0]["oracleDeclarations"].pop()
    expect_semantic_rejection(lambda value: validate_mutation_query_roots(value, mutation_catalog), missing_declaration, "mutation test omitted a typed oracle declaration slot")
    drifted_query_root = root_for(single_query)
    drifted_query_root["patternSource"] = {"role": "pattern-source", "digest": "f" * 64}
    for field in ("patternSource", "patternPlan", "patternQuery"):
        spliced_mutation = deepcopy(mutation)
        spliced_mutation["tests"][0]["patternQueries"][0][field] = deepcopy(drifted_query_root[field])
        expect_semantic_rejection(lambda value: validate_mutation_query_roots(value, mutation_catalog), spliced_mutation, f"typed mutation manifest accepted declaration/{field} drift")
    result = load(FIXTURES / "pattern-result.json")
    trace = load(FIXTURES / "event-trace.json")
    trace_digest = digest("k-in-k/event-trace/v1", trace)
    subset_query = data["queries"]["nonlexical-subset-side-condition"]
    subset_result = deepcopy(result)
    subset_result["queryId"] = subset_query["queryId"]
    subset_result["inputs"].update(root_for(subset_query))
    subset_table = load(FIXTURES / "side-condition-conformance-table.json")
    subset_derived, subset_indeterminate = derive_trace_plan_witnesses(subset_result, subset_plan, subset_table, trace, subset_result["pathResults"][0])
    ok(not subset_indeterminate and len(subset_derived) == 1 and [binding["name"] for binding in subset_derived[0]["bindings"]] == ["VALUE", "ADDRESS"], "persisted-shape nonlexical denotation did not preserve declaration order")
    subset_result["witnesses"] = subset_derived
    subset_result["primaryWitness"] = deepcopy(subset_derived[0])
    subset_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(subset_result, "resultId"))
    validate_official_instance(subset_result, "pattern-result.schema.json")
    validate_pattern_result_semantics(subset_result, {trace_digest: trace})
    reordered_subset_result = deepcopy(subset_result)
    reordered_subset_result["witnesses"][0]["bindings"].reverse()
    reordered_subset_result["primaryWitness"] = deepcopy(reordered_subset_result["witnesses"][0])
    reordered_subset_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(reordered_subset_result, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), reordered_subset_result, "persisted-shape witness binding reorder was accepted")
    for field in ("patternSource", "patternPlan", "patternQuery"):
        missing_result_root = deepcopy(result)
        missing_result_root["inputs"].pop(field)
        expect_schema_rejection(missing_result_root, "pattern-result.schema.json", f"pattern result omitted {field}")
    spliced_result = deepcopy(result)
    spliced_result["inputs"]["patternPlan"] = deepcopy(single_query["patternPlan"])
    spliced_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(spliced_result, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), spliced_result, "rehashed pattern result accepted a spliced source/plan/query triple")
    spliced_replay = deepcopy(replay)
    spliced_replay["patternPlan"] = deepcopy(single_query["patternPlan"])
    spliced_replay["artifacts"] = [deepcopy(spliced_replay["patternPlan"]) if artifact["role"] == "pattern-plan" else artifact for artifact in spliced_replay["artifacts"]]
    spliced_replay["steps"][3]["inputArtifacts"][2] = deepcopy(spliced_replay["patternPlan"])
    refresh_replay_ids(spliced_replay)
    expect_semantic_rejection(validate_replay_semantics, spliced_replay, "rehashed replay invocation/manifest accepted a spliced source/plan/query triple")
    omitted = deepcopy(result)
    omitted["witnesses"] = []
    omitted.pop("primaryWitness")
    omitted["resultId"] = digest("k-in-k/pattern-result/v1", value_without(omitted, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), omitted, "persisted witness omission was accepted")
    extra = deepcopy(result)
    extra_witness = deepcopy(extra["witnesses"][0])
    extra_witness["armOrdinal"] = 1
    extra["witnesses"].append(extra_witness)
    extra["resultId"] = digest("k-in-k/pattern-result/v1", value_without(extra, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), extra, "extra self-asserted arm witness was accepted")
    wrong_binding = deepcopy(result)
    wrong_binding["witnesses"][0]["bindings"][0]["term"]["node"]["text"] = "2"
    wrong_binding["primaryWitness"] = deepcopy(wrong_binding["witnesses"][0])
    wrong_binding["resultId"] = digest("k-in-k/pattern-result/v1", value_without(wrong_binding, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), wrong_binding, "self-asserted witness binding was accepted")
    missing_arm = deepcopy(result)
    missing_arm["witnesses"][0].pop("armOrdinal")
    missing_arm["primaryWitness"].pop("armOrdinal")
    expect_schema_rejection(missing_arm, "pattern-result.schema.json", "witness omitted arm ordinal zero")
    wrong_status = deepcopy(result)
    wrong_status["pathResults"][0]["status"] = "no-match"
    wrong_status["outcome"] = "no-match"
    wrong_status["witnesses"] = []
    wrong_status.pop("primaryWitness")
    wrong_status["resultId"] = digest("k-in-k/pattern-result/v1", value_without(wrong_status, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {trace_digest: trace}), wrong_status, "self-asserted path status was accepted")

    two_occurrence_trace = deepcopy(trace)
    later_load = deepcopy(two_occurrence_trace["events"][-1])
    later_load.update({"index": 2, "transitionOrdinal": later_load["transitionOrdinal"] + 1, "emissionOrdinal": 0})
    two_occurrence_trace["events"].append(later_load)
    identity_payload = value_without(two_occurrence_trace, "pathOrdinal", "pathKey", "pathIdentityDigest")
    two_occurrence_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", identity_payload)
    two_occurrence_trace_digest = digest("k-in-k/event-trace/v1", two_occurrence_trace)
    two_occurrence_result = deepcopy(result)
    two_occurrence_path = two_occurrence_result["pathResults"][0]
    two_occurrence_path["traceDigest"] = two_occurrence_trace_digest
    two_occurrence_path["pathIdentityDigest"] = two_occurrence_trace["pathIdentityDigest"]
    for artifact in two_occurrence_result["inputs"]["artifacts"]:
        if artifact["role"] == "event-trace" and artifact["digest"] == trace_digest:
            artifact["digest"] = two_occurrence_trace_digest
    plan, _query, _observation, side_table = resolved_fixture_query(two_occurrence_result["inputs"], two_occurrence_result["queryId"])
    derived_occurrences, indeterminate = derive_trace_plan_witnesses(two_occurrence_result, plan, side_table, two_occurrence_trace, two_occurrence_path)
    ok(not indeterminate and {tuple(witness["eventIndices"]) for witness in derived_occurrences} == {(0, 1), (0, 2)}, "persisted two-occurrence adversary did not derive both matches")
    from refresh_fixture_ids import bag11_fixture_witnesses, refresh_replay
    produced_occurrences = bag11_fixture_witnesses(plan, two_occurrence_trace, two_occurrence_path)
    ok(produced_occurrences == sorted(derived_occurrences, key=witness_order_key), "refresh producer differs from the complete verifier denotation or its semantic order")
    two_occurrence_result["witnesses"] = produced_occurrences
    two_occurrence_result["primaryWitness"] = deepcopy(produced_occurrences[0])

    two_occurrence_replay = deepcopy(replay)
    two_occurrence_replay["steps"][2]["expectedArtifacts"] = [{"role": "event-trace", "digest": two_occurrence_trace_digest}]
    two_occurrence_replay["steps"][3]["inputArtifacts"][0] = {"role": "event-trace", "digest": two_occurrence_trace_digest}
    refresh_replay(two_occurrence_replay)
    two_occurrence_result["inputs"]["replayInvocationDigest"] = two_occurrence_replay["invocationDigest"]
    two_occurrence_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(two_occurrence_result, "resultId"))
    two_occurrence_replay["expectedResultDigest"] = two_occurrence_result["resultId"]
    two_occurrence_replay["steps"][3]["expectedArtifacts"] = [{"role": "pattern-result", "digest": two_occurrence_result["resultId"]}]
    refresh_replay(two_occurrence_replay)
    validate_official_instance(two_occurrence_result, "pattern-result.schema.json")
    validate_pattern_result_semantics(two_occurrence_result, {two_occurrence_trace_digest: two_occurrence_trace})
    validate_official_instance(two_occurrence_replay, "replay-manifest.schema.json")
    validate_replay_semantics(two_occurrence_replay)
    ok(two_occurrence_result["primaryWitness"]["eventIndices"] == [0, 1], "persisted two-occurrence primary is not the earliest occurrence")
    ok(two_occurrence_replay["expectedResultDigest"] == two_occurrence_result["resultId"] and two_occurrence_result["inputs"]["replayInvocationDigest"] == two_occurrence_replay["invocationDigest"], "refresh producer result did not propagate through replay identities")
    replay_hash_order = sorted(produced_occurrences, key=lambda witness: witness["replayKey"])
    ok(replay_hash_order[0]["eventIndices"] == [0, 2], "two-occurrence adversary no longer distinguishes replay identity from semantic order")
    replay_ordered_result = deepcopy(two_occurrence_result)
    replay_ordered_result["witnesses"] = replay_hash_order
    replay_ordered_result["primaryWitness"] = deepcopy(replay_hash_order[0])
    replay_ordered_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(replay_ordered_result, "resultId"))
    expect_semantic_rejection(
        lambda value: validate_pattern_result_semantics(value, {two_occurrence_trace_digest: two_occurrence_trace}),
        replay_ordered_result,
        "replay-ID hash order promoted a later persisted occurrence to primary",
    )

    pattern_operand = next(
        value
        for path in sorted(FIXTURES.glob("oracle-operand-*.json"))
        for value in [load(path)]
        if value["subject"]["side"] == "baseline"
        and value["normalizedValue"].get("patternResult") == {"role": "pattern-result", "digest": result["resultId"]}
        and value["normalizedValue"]["bindingTuples"] == []
    )
    refreshed_operand = deepcopy(pattern_operand)
    refreshed_result_key = {"role": "pattern-result", "digest": two_occurrence_result["resultId"]}
    refreshed_operand["completionEvidence"]["patternResult"] = refreshed_result_key
    refreshed_operand["normalizedValue"]["patternResult"] = refreshed_result_key
    refreshed_operand["operandId"] = digest("k-in-k/oracle-operand/v1", value_without(refreshed_operand, "operandId"))
    validate_official_instance(refreshed_operand, "oracle-semantics.schema.json#/$defs/operand")

    def external_structured_entry(role: str, identity: str, value: dict[str, Any]) -> dict[str, Any]:
        return {
            "role": role,
            "digest": identity,
            "contentModel": "canonical-json",
            "mediaType": "application/json",
            "contentSha256": hashlib.sha256(canonical(value).encode("utf-8")).hexdigest(),
            "availability": "external-required",
            "logicalPath": f"artifact://bag11-two-occurrence/{role}/{identity}",
            "resolverId": "rust-artifact-store-v1",
        }

    refreshed_catalog = deepcopy(catalog)
    refreshed_catalog["entries"].extend([
        external_structured_entry("event-trace", two_occurrence_trace_digest, two_occurrence_trace),
        external_structured_entry("pattern-result", two_occurrence_result["resultId"], two_occurrence_result),
        external_structured_entry("replay-manifest", two_occurrence_replay["replayId"], two_occurrence_replay),
        external_structured_entry("oracle-operand", refreshed_operand["operandId"], refreshed_operand),
    ])
    refreshed_catalog["entries"].sort(key=lambda entry: (entry["role"], entry["digest"]))
    refreshed_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(refreshed_catalog, "catalogId"))
    validate_official_instance(refreshed_catalog, "artifact-catalog.schema.json")
    validate_artifact_catalog(refreshed_catalog)
    require_catalog_entries(refreshed_catalog, [
        ("event-trace", two_occurrence_trace_digest),
        ("pattern-result", two_occurrence_result["resultId"]),
        ("replay-manifest", two_occurrence_replay["replayId"]),
        ("oracle-operand", refreshed_operand["operandId"]),
    ], "persisted two-occurrence refreshed output closure")
    ok(
        all(refreshed != original for refreshed, original in (
            (two_occurrence_trace_digest, trace_digest),
            (two_occurrence_result["resultId"], result["resultId"]),
            (two_occurrence_replay["invocationDigest"], replay["invocationDigest"]),
            (two_occurrence_replay["replayId"], replay["replayId"]),
            (refreshed_operand["operandId"], pattern_operand["operandId"]),
            (refreshed_catalog["catalogId"], catalog["catalogId"]),
        )),
        "two-occurrence fixture change did not refresh every enclosing portable identity",
    )

    selected_root = root_for(single_query)
    require_catalog_entries(catalog, [(value["role"], value["digest"]) for value in selected_root.values()], "identity propagation query")
    propagated_catalog = deepcopy(catalog)
    propagated_catalog["entries"] = [entry for entry in propagated_catalog["entries"] if (entry["role"], entry["digest"]) != ("pattern-query", query["queryId"])]
    propagated_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(propagated_catalog, "catalogId"))
    validate_artifact_catalog(propagated_catalog)
    resolve_pattern_query_root(selected_root, propagated_catalog, vocabularies)
    propagated_result = deepcopy(result)
    propagated_result["queryId"] = single_query["queryId"]
    propagated_result["inputs"].update(deepcopy(selected_root))
    propagated_result["resultId"] = digest("k-in-k/pattern-result/v1", value_without(propagated_result, "resultId"))
    propagated_corpus = deepcopy(corpus)
    for test in propagated_corpus["tests"]:
        test["patternQueries"] = [deepcopy(selected_root) if root["patternQuery"]["digest"] == query["queryId"] else root for root in test["patternQueries"]]
    propagated_corpus["patternQueries"] = [deepcopy(root) for test in propagated_corpus["tests"] for root in test["patternQueries"]]
    propagated_corpus["artifactCatalogDigest"] = propagated_catalog["catalogId"]
    propagated_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(propagated_corpus, "manifestId"))
    validate_corpus_manifest_semantics(propagated_corpus, propagated_catalog)
    propagated_replay = replay_with(single_query)
    propagated_replay["artifactCatalogDigest"] = propagated_catalog["catalogId"]
    refresh_replay_ids(propagated_replay)
    validate_replay_catalog(propagated_replay, propagated_catalog)
    changed_roots = (propagated_result["resultId"], propagated_catalog["catalogId"], propagated_corpus["manifestId"], propagated_replay["invocationDigest"], propagated_replay["replayId"])
    original_roots = (result["resultId"], catalog["catalogId"], corpus["manifestId"], replay["invocationDigest"], replay["replayId"])
    ok(all(changed != original for changed, original in zip(changed_roots, original_roots)), "query selection/artifact change did not propagate through result/catalog/corpus/replay identities")
    overlapping_case = next(case for case in data["cases"] if case["id"] == "overlapping-alternatives-use-declaration-order")
    ordered, _ = denotational_vector_result(overlapping_case, data)
    ok([witness["armOrdinal"] for witness in ordered] == [0, 1], "complete overlapping denotation omits arm zero or declaration order")
    expect_semantic_rejection(lambda value: ok(value == ordered, "reordered complete witnesses"), list(reversed(ordered)), "reordered witnesses were accepted")

    compiler_profile = next(entry for entry in load(FIXTURES / "artifact-catalog.json")["entries"] if entry["role"] == "pattern-compiler-profile")
    future_receipt = {"patternSource": query["patternSource"], "patternPlan": query["patternPlan"], "entryModule": query["entryModule"], "exportedName": query["exportedName"], "compilerProfile": {"role": "pattern-compiler-profile", "digest": compiler_profile["digest"]}, "compilerVersion": "future", "diagnosticsDigest": "0" * 64}
    def validate_future_receipt_binding(receipt: dict[str, Any], expected_query: dict[str, Any]) -> None:
        ok(receipt["patternSource"] == expected_query["patternSource"] and receipt["patternPlan"] == expected_query["patternPlan"] and receipt["entryModule"] == expected_query["entryModule"] and receipt["exportedName"] == expected_query["exportedName"], "future compiler receipt binds another source, plan, or named entry")
    validate_future_receipt_binding(future_receipt, query)
    wrong_receipt = deepcopy(future_receipt)
    wrong_receipt["patternPlan"] = {"role": "pattern-plan", "digest": plan_drift["patternPlanDigest"]}
    expect_semantic_rejection(lambda value: validate_future_receipt_binding(value, query), wrong_receipt, "compiler receipt for another plan was accepted")


def verify_observation() -> None:
    data = load(VECTORS / "observation-vectors.json")
    structural_fixture = load(FIXTURES / "structural-observation-cases.json")
    structural_cases = {case["id"]: case["manifest"] for case in structural_fixture["cases"]}
    counter_definition = load(FIXTURES / "semantic-definition-counter.json")
    for case in data["selectionCases"]:
        expected = case["expected"]
        if "manifestDigest" in case:
            same = case["manifestDigest"] == case["installedManifestDigest"]
            derived = {"status": "already-present" if same else "error", "installedCount": 0}
            if not same:
                derived["failure"] = "non-conservative-observation"
        elif "structuralFixtureCase" in case:
            observation = structural_cases[case["structuralFixtureCase"]]
            schema_path = SCHEMAS / "observation-manifest.schema.json"
            schema = load(schema_path)
            validate_schema(observation, schema, schema_path, schema)
            validate_observation_manifest_semantics(observation, counter_definition)
            installed = sum(len(selection["matchedLineages"]) for selection in observation["selections"])
            derived = {"status": "accepted", "installedCount": installed}
        elif "selector" in case:
            accepted = len(case["suppliedMatches"]) == case["selector"]["expectedCardinality"]
            derived = {"status": "accepted" if accepted else "error", "installedCount": len(case["suppliedMatches"]) if accepted else 0}
            if not accepted:
                derived["failure"] = "cardinality-mismatch"
        elif any(len(matches) != 1 for matches in case.get("suppliedMatches", [])):
            derived = {"status": "error", "failure": "cardinality-mismatch", "installedCount": 0}
        elif "support" in case and not all(case["support"].values()):
            derived = {"status": "error", "failure": "unsupported-observation-shape", "installedCount": 0}
        elif "suppliedMatches" in case:
            flattened = [match for matches in case["suppliedMatches"] for match in matches]
            if len(flattened) != len(set(flattened)):
                derived = {"status": "error", "failure": "duplicate-site", "installedCount": 0}
            else:
                derived = {"status": "accepted", "installedCount": len(flattened)}
        else:
            raise AssertionError(f"{case['id']}: observation selection vector has no derivation inputs")
        ok(expected == derived, f"{case['id']}: selection result is not derived from its inputs")
    by_id = {case["id"]: case for case in data["emissionCases"]}
    case = by_id["one-transition-multiple-events"]
    ok([item["kind"] for item in case["manifest"]] == case["expected"]["eventOrder"], "manifest event order mismatch")
    ok(case["expected"]["transitionOrdinals"] == [case["transitionOrdinal"]] * len(case["manifest"]), "one transition did not retain one transition ordinal")
    ok(case["expected"]["emissionOrdinals"] == list(range(len(case["manifest"]))), "emission ordinals not contiguous")
    for case in data["emissionCases"]:
        if case["expected"].get("status") == "error":
            if "manifest" in case:
                keys = [(entry["observerId"], entry["eventOrdinal"]) for entry in case["manifest"]]
                failure = "duplicate-site" if len(keys) != len(set(keys)) else None
            else:
                variables = case.get("payloadVariables", [])
                if any(not variable["boundAtTransition"] for variable in variables):
                    failure = "invalid-variable"
                elif any(variable["sort"] != variable.get("declaredEventSort", variable["sort"]) for variable in variables):
                    failure = "ill-sorted"
                else:
                    failure = None
            ok(case["expected"] == {"status": "error", "failure": failure, "emittedCount": 0} and failure is not None, f"{case['id']}: emission error is not derived from its inputs")
        if "transitions" in case:
            flattened = [(transition["ordinal"], emission, ordinal) for transition in case["transitions"] for ordinal, emission in enumerate(transition["events"])]
            ok(case["expected"]["eventIndices"] == list(range(len(flattened))), f"{case['id']}: observed-event indices")
            if "transitionOrdinals" in case["expected"]:
                ok(case["expected"]["transitionOrdinals"] == [item[0] for item in flattened], f"{case['id']}: transition ordinals")
            if "emissionOrdinals" in case["expected"]:
                ok(case["expected"]["emissionOrdinals"] == [item[2] for item in flattened], f"{case['id']}: emission ordinals")
            constructors = [item[1] for item in flattened]
            if "domainNextEvent" in case["expected"]:
                write_index, load_index = constructors.index("memoryWrite"), constructors.index("memoryLoad")
                ok(case["expected"]["domainNextEvent"] == (load_index == write_index + 1), f"{case['id']}: domain adjacency")
                ok(case["expected"]["domainEventuallyAfter"] == (load_index > write_index), f"{case['id']}: domain eventual order")
            if "nextTransition" in case["expected"]:
                observed_transitions = [item[0] for item in flattened]
                ok(case["expected"]["nextEvent"] == (len(flattened) == 2), f"{case['id']}: event adjacency")
                ok(case["expected"]["nextTransition"] == (observed_transitions[1] == observed_transitions[0] + 1), f"{case['id']}: transition adjacency")
            if "eventuallyAfter" in case["expected"]:
                ok(case["expected"]["nextEvent"] == (len(flattened) == 2), f"{case['id']}: domain next-event adjacency")
                ok(case["expected"]["eventuallyAfter"] == (len(flattened) >= 2), f"{case['id']}: domain eventually-after ordering")
        if "branches" in case:
            for branch in case["branches"]:
                events = [(transition["ordinal"], event) for transition in branch["transitions"] for event in transition["events"]]
                expected = case["expected"][branch["pathKey"]]
                ok(expected["eventIndices"] == list(range(len(events))), f"{case['id']}: branch event clock")
                ok(expected["transitionOrdinals"] == [event[0] for event in events], f"{case['id']}: branch transition retention")
    for case in data["conservativityCases"]:
        expected = case["expected"]
        if "baselineTreeDigest" in case:
            ok((case["baselineTreeDigest"] == case["instrumentedErasedTreeDigest"]) == (expected["status"] == "pass"), f"{case['id']}: disabled erasure")
        elif "instrumentedAfterErasure" in case:
            ok((case["baseline"] == case["instrumentedAfterErasure"]) == (expected["status"] == "pass"), f"{case['id']}: branch erasure")
        elif "stopReason" in case.get("instrumented", {}):
            ok(expected["status"] == "unknown" and not expected["conservativityProven"], f"{case['id']}: inconclusive erasure")
        else:
            ok(expected["status"] == "error" and case["baselineStateDigest"] != case["instrumentedErasedStateDigest"], f"{case['id']}: changed erasure result")
    execution_cases = {case["id"]: case for case in load(VECTORS / "execution-pattern-vectors.json")["cases"]}
    for case in data["traceStreamEquivalenceCases"]:
        ok(case["executionVector"] in execution_cases, f"unknown trace/stream vector {case['executionVector']}")
        required = ["outcome", "primaryWitness"] if execution_cases[case["executionVector"]]["expected"]["outcome"] == "match" else ["outcome"]
        ok(case["requiredEqualFields"] == required, f"trace/stream equivalence does not compare the complete normalized witness for {case['executionVector']}")


def paths_overlap(left: str, right: str) -> bool:
    if left == right:
        return True
    left_prefix = left.rstrip("/") + "/"
    right_prefix = right.rstrip("/") + "/"
    return right.startswith(left_prefix) or left.startswith(right_prefix)


def typed_path_prefix(left: list[dict[str, Any]], right: list[dict[str, Any]]) -> bool:
    return len(left) <= len(right) and left == right[:len(left)]


def sentence_index(definition: dict[str, Any]) -> dict[str, tuple[dict[str, Any], dict[str, Any]]]:
    result: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}
    for module in definition["modules"]:
        for sentence in module["sentences"]:
            lineage = sentence["provenance"]["lineageId"]
            ok(lineage not in result, "duplicate sentence lineage in definition")
            result[lineage] = (module, sentence)
    return result


def path_get(sentence_value: dict[str, Any], path: list[dict[str, Any]]) -> Any:
    current: Any = sentence_value
    for step in path:
        kind = step["kind"]
        if kind == "field":
            name = step["name"]
            if current is sentence_value and name in ("body", "requires", "ensures", "attributes"):
                current = current[name]
            elif isinstance(current, dict) and current.get("encoding") == "portable-term-v1" and name in ("lhs", "rhs") and current["node"]["kind"] == "rewrite":
                current = current["node"]["left" if name == "lhs" else "right"]
            else:
                raise AssertionError("malformed-path")
        elif kind == "argument" and isinstance(current, dict) and current.get("encoding") == "portable-term-v1" and current["node"]["kind"] == "application":
            try:
                current = current["node"]["args"][step["index"]]
            except IndexError as error:
                raise AssertionError("malformed-path") from error
        elif kind == "sequence-item" and isinstance(current, dict) and current.get("encoding") == "portable-term-v1" and current["node"]["kind"] == "sequence":
            try:
                current = current["node"]["items"][step["index"]]
            except IndexError as error:
                raise AssertionError("malformed-path") from error
        elif kind == "injection-term" and isinstance(current, dict) and current.get("encoding") == "portable-term-v1" and current["node"]["kind"] == "injection":
            current = current["node"]["term"]
        elif kind == "attribute" and isinstance(current, list):
            matches = [attribute for attribute in current if attribute["name"] == step["name"]]
            if len(matches) != 1:
                raise AssertionError("malformed-path")
            current = matches[0]
        else:
            raise AssertionError("malformed-path")
    return current


def path_replace(sentence_value: dict[str, Any], path: list[dict[str, Any]], replacement: Any) -> None:
    ok(bool(path), "cannot replace empty term path")
    parent = path_get(sentence_value, path[:-1]) if len(path) > 1 else sentence_value
    step = path[-1]
    if step["kind"] == "field":
        name = step["name"]
        if parent is sentence_value and name in ("body", "requires", "ensures"):
            parent[name] = replacement
        elif isinstance(parent, dict) and parent.get("encoding") == "portable-term-v1" and name in ("lhs", "rhs") and parent["node"]["kind"] == "rewrite":
            parent["node"]["left" if name == "lhs" else "right"] = replacement
        else:
            raise AssertionError("malformed-path")
    elif step["kind"] == "argument" and parent["node"]["kind"] == "application":
        parent["node"]["args"][step["index"]] = replacement
    elif step["kind"] == "sequence-item" and parent["node"]["kind"] == "sequence":
        parent["node"]["items"][step["index"]] = replacement
    elif step["kind"] == "injection-term" and parent["node"]["kind"] == "injection":
        parent["node"]["term"] = replacement
    else:
        raise AssertionError("malformed-path")


def refreshed_definition(definition: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(definition)
    module_payloads: list[dict[str, Any]] = []
    for module in result["modules"]:
        contents: list[str] = []
        for sentence in module["sentences"]:
            value, provenance = sentence["value"], sentence["provenance"]
            provenance.update({"module": value["module"], "label": value["label"], "kind": value["kind"], "source": value["source"], "location": value["location"]})
            body_id = digest("k-in-k/sentence-body/v1", {"body": value["body"], "requires": value["requires"], "ensures": value["ensures"]})
            provenance["bodyFingerprint"] = body_id
            content_payload = {
                "lineageId": provenance["lineageId"], "module": value["module"], "label": value["label"], "kind": value["kind"],
                "source": value["source"], "location": value["location"], "generated": provenance["generated"],
                "bodyFingerprint": body_id, "attributes": value["attributes"], "transformationChain": provenance["transformationChain"],
            }
            provenance["contentFingerprint"] = digest("k-in-k/sentence-content/v1", content_payload)
            contents.append(provenance["contentFingerprint"])
        module_payload = {"name": module["name"], "ordinal": module["ordinal"], "imports": module["imports"], "sentenceContentFingerprints": contents}
        module["fingerprint"] = digest("k-in-k/module/v1", module_payload)
        module_payloads.append(module_payload)
    definition_payload = {"schemaVersion": result["schemaVersion"], "representation": result["representation"], "baselineFamilyId": result["baselineFamilyId"], "modules": module_payloads}
    result["definitionDigest"] = digest("k-in-k/definition/v1", definition_payload)
    return result


def apply_portable_patch(definition: dict[str, Any], patch: dict[str, Any]) -> tuple[dict[str, Any] | None, dict[str, Any] | None, str | None]:
    original = deepcopy(definition)
    targets = sentence_index(original)
    modules = {module["name"]: module for module in original["modules"]}
    edits = patch["edits"]
    try:
        baseline_signatures = definition_signature_registry(original)
        validate_definition_semantics(original)
        for edit in edits:
            operation = edit["operation"]
            if operation == "insert-sentence" and edit["position"]["kind"] in ("module-start", "module-end"):
                module = modules.get(edit["position"]["module"])
                if module is None or edit["expectedModuleFingerprint"] != module["fingerprint"]:
                    raise AssertionError("stale-precondition")
                if edit["value"]["sentence"]["module"] != module["name"]:
                    raise AssertionError("invalid-position")
            else:
                if edit["targetLineage"] not in targets:
                    raise AssertionError("stale-precondition")
                _, sentence = targets[edit["targetLineage"]]
                if edit["expectedContent"] != sentence["provenance"]["contentFingerprint"]:
                    raise AssertionError("stale-precondition")
                if operation == "insert-sentence" and edit["position"].get("anchorLineage") != edit["targetLineage"]:
                    raise AssertionError("invalid-position")
                if operation == "insert-sentence" and edit["value"]["sentence"]["module"] != targets[edit["targetLineage"]][0]["name"]:
                    raise AssertionError("invalid-position")
                if operation in ("replace-term", "replace-condition"):
                    old = path_get(sentence["value"], edit["targetPath"])
                    replacement = edit["value"].get("term")
                    if edit["value"]["kind"] == "original-reference":
                        replacement = path_get(targets[edit["value"]["fromOriginalLineage"]][1]["value"], edit["value"]["fromOriginalPath"])
                    if operation == "replace-term" and old["sort"] != replacement["sort"]:
                        raise AssertionError("locally-ill-formed")
                    if operation == "replace-condition" and replacement["sort"] != "Bool":
                        raise AssertionError("locally-ill-formed")
                    validate_portable_term(replacement, baseline_signatures, {})
                    if old == replacement:
                        raise AssertionError("no-change")
                elif operation in ("add-attribute", "remove-attribute", "replace-attribute"):
                    path = edit["targetPath"]
                    if path != [{"kind": "field", "name": "attributes"}, {"kind": "attribute", "name": path[-1].get("name", "")}]:
                        raise AssertionError("malformed-path")
                    name = path[-1]["name"]
                    if operation in ("add-attribute", "replace-attribute") and edit["value"].get("name") != name:
                        raise AssertionError("locally-ill-formed")
                    matches = [attribute for attribute in sentence["value"]["attributes"] if attribute["name"] == name]
                    if operation == "add-attribute":
                        if matches:
                            raise AssertionError("stale-precondition")
                    else:
                        if len(matches) != 1 or edit["expectedAttributeFingerprint"] != digest("k-in-k/attribute/v1", matches[0]):
                            raise AssertionError("stale-precondition")
                        replacement_attribute = {"name": edit["value"].get("name"), "value": edit["value"].get("value")}
                        if operation == "replace-attribute" and any(attribute["name"] == replacement_attribute["name"] and attribute is not matches[0] for attribute in sentence["value"]["attributes"]):
                            raise AssertionError("locally-ill-formed")
                        if operation == "replace-attribute" and matches[0] == replacement_attribute:
                            raise AssertionError("no-change")
                    if operation in ("add-attribute", "replace-attribute") and edit["value"].get("value") is not None:
                        validate_portable_term(edit["value"]["value"], baseline_signatures, {})
                elif operation == "replace-sentence" and sentence["value"] == edit["value"]["sentence"]:
                    raise AssertionError("no-change")
                elif operation == "replace-sentence":
                    replacement_sentence = edit["value"]["sentence"]
                    for immutable_key in ("module", "source", "kind", "location"):
                        if replacement_sentence[immutable_key] != sentence["value"][immutable_key] or replacement_sentence[immutable_key] != sentence["provenance"][immutable_key]:
                            raise AssertionError("locally-ill-formed")
                    validate_sentence_local_well_formedness(replacement_sentence, baseline_signatures)
            if operation == "insert-sentence":
                validate_sentence_local_well_formedness(edit["value"]["sentence"], baseline_signatures)
        for index, left in enumerate(edits):
            for right in edits[index + 1:]:
                if left["operation"] == right["operation"] == "insert-sentence":
                    left_position, right_position = left["position"], right["position"]
                    left_anchor = left_position.get("anchorLineage") or left_position.get("module")
                    right_anchor = right_position.get("anchorLineage") or right_position.get("module")
                    if (left_position["kind"], left_anchor, left_position["ordinal"]) == (right_position["kind"], right_anchor, right_position["ordinal"]):
                        raise AssertionError("duplicate-target")
                if left["targetLineage"] is not None and left["targetLineage"] == right["targetLineage"] and left["operation"] != "insert-sentence" and right["operation"] != "insert-sentence":
                    if left["targetPath"] == right["targetPath"]:
                        raise AssertionError("duplicate-target")
                    if typed_path_prefix(left["targetPath"], right["targetPath"]) or typed_path_prefix(right["targetPath"], left["targetPath"]):
                        raise AssertionError("overlapping-edit")
                for anchor_edit, destructive_edit in ((left, right), (right, left)):
                    if anchor_edit["operation"] == "insert-sentence" and anchor_edit["position"]["kind"] in ("before-lineage", "after-lineage") and destructive_edit["operation"] in ("replace-sentence", "delete-sentence") and anchor_edit["position"]["anchorLineage"] == destructive_edit["targetLineage"]:
                        raise AssertionError("overlapping-edit")
    except (AssertionError, KeyError, IndexError, TypeError) as error:
        reason = str(error) if str(error) in {"stale-precondition", "invalid-position", "no-change", "malformed-path", "duplicate-target", "overlapping-edit", "locally-ill-formed"} else "locally-ill-formed"
        return None, None, reason

    output = deepcopy(original)
    output_targets = sentence_index(output)
    deleted: set[str] = set()
    insertions: dict[tuple[str, str, str], list[tuple[int, dict[str, Any]]]] = {}
    transformation_id = digest("k-in-k/transformation/v1", {"kind": "mutation", "operatorId": patch["operatorId"], "operatorVersion": patch["operatorVersion"], "inputDefinitionDigest": original["definitionDigest"], "manifestDigest": patch["patchId"]})
    for edit in edits:
        operation = edit["operation"]
        if operation == "insert-sentence":
            position = edit["position"]
            if position["kind"] in ("before-lineage", "after-lineage"):
                module_name = output_targets[position["anchorLineage"]][0]["name"]
                parent_lineages = [position["anchorLineage"]]
                anchor = position["anchorLineage"]
            else:
                module_name = position["module"]
                parent_lineages = []
                anchor = module_name
            anchor_identity = position.get("anchorLineage") or modules[module_name]["fingerprint"]
            generated_payload = {"transformationId": transformation_id, "parentLineages": parent_lineages, "anchorIdentity": anchor_identity, "role": f"insert-{position['kind']}", "ordinal": position["ordinal"]}
            lineage = digest("k-in-k/generated-lineage/v1", generated_payload)
            value = deepcopy(edit["value"]["sentence"])
            inserted = {"sourceOccurrenceOrdinal": None, "generatedIdentity": generated_payload, "provenance": {"lineageId": lineage, "contentFingerprint": "0" * 64, "bodyFingerprint": "0" * 64, "module": value["module"], "label": value["label"], "kind": value["kind"], "source": value["source"], "location": value["location"], "generated": True, "transformationChain": [transformation_id]}, "value": value}
            insertions.setdefault((module_name, position["kind"], anchor), []).append((position["ordinal"], inserted))
            continue
        _, sentence = output_targets[edit["targetLineage"]]
        if operation in ("replace-term", "replace-condition"):
            replacement = edit["value"].get("term")
            if edit["value"]["kind"] == "original-reference":
                replacement = path_get(targets[edit["value"]["fromOriginalLineage"]][1]["value"], edit["value"]["fromOriginalPath"])
            path_replace(sentence["value"], edit["targetPath"], deepcopy(replacement))
        elif operation == "replace-sentence":
            sentence["value"] = deepcopy(edit["value"]["sentence"])
        elif operation == "delete-sentence":
            deleted.add(edit["targetLineage"])
        else:
            attributes = sentence["value"]["attributes"]
            name = edit["targetPath"][-1]["name"]
            replacement_attribute = {"name": edit["value"].get("name"), "value": edit["value"].get("value")}
            if operation == "add-attribute":
                attributes.append(replacement_attribute)
            elif operation == "remove-attribute":
                attributes[:] = [attribute for attribute in attributes if attribute["name"] != name]
            else:
                attributes[:] = [replacement_attribute if attribute["name"] == name else attribute for attribute in attributes]
            attributes.sort(key=lambda attribute: attribute["name"])
    for module in output["modules"]:
        rebuilt: list[dict[str, Any]] = []
        rebuilt.extend(item for _, item in sorted(insertions.get((module["name"], "module-start", module["name"]), [])))
        for sentence in module["sentences"]:
            lineage = sentence["provenance"]["lineageId"]
            rebuilt.extend(item for _, item in sorted(insertions.get((module["name"], "before-lineage", lineage), [])))
            if lineage not in deleted:
                rebuilt.append(sentence)
            rebuilt.extend(item for _, item in sorted(insertions.get((module["name"], "after-lineage", lineage), [])))
        rebuilt.extend(item for _, item in sorted(insertions.get((module["name"], "module-end", module["name"]), [])))
        module["sentences"] = rebuilt
    output = refreshed_definition(output)
    try:
        validate_definition_semantics(output, baseline_signatures, {transformation_id: original})
    except (AssertionError, KeyError, IndexError, TypeError):
        return None, None, "locally-ill-formed"
    output_targets = sentence_index(output)
    diff_entries: list[dict[str, Any]] = []
    for edit in edits:
        operation = edit["operation"]
        if operation == "insert-sentence":
            position = edit["position"]
            module_name = position.get("module") or targets[position["anchorLineage"]][0]["name"]
            parent_lineages = [position["anchorLineage"]] if "anchorLineage" in position else []
            anchor_identity = position.get("anchorLineage") or modules[module_name]["fingerprint"]
            lineage = digest("k-in-k/generated-lineage/v1", {"transformationId": transformation_id, "parentLineages": parent_lineages, "anchorIdentity": anchor_identity, "role": f"insert-{position['kind']}", "ordinal": position["ordinal"]})
            affected = output_targets[lineage][1]["provenance"]
            before, after = None, affected["contentFingerprint"]
            target_lineage = lineage
        else:
            original_sentence = targets[edit["targetLineage"]][1]
            affected = original_sentence["provenance"]
            target_lineage = edit["targetLineage"]
            if operation == "delete-sentence":
                before, after = affected["contentFingerprint"], None
            elif operation in ("add-attribute", "remove-attribute", "replace-attribute"):
                name = edit["targetPath"][-1]["name"]
                old_attributes = [attribute for attribute in original_sentence["value"]["attributes"] if attribute["name"] == name]
                new_sentence = output_targets[target_lineage][1]
                new_attributes = [attribute for attribute in new_sentence["value"]["attributes"] if attribute["name"] == name]
                before = digest("k-in-k/diff-value/v1", old_attributes[0]) if old_attributes else None
                after = digest("k-in-k/diff-value/v1", new_attributes[0]) if new_attributes else None
            else:
                before = digest("k-in-k/diff-value/v1", path_get(original_sentence["value"], edit["targetPath"]) if edit["targetPath"] else original_sentence["value"])
                new_sentence = output_targets[target_lineage][1]
                after = digest("k-in-k/diff-value/v1", path_get(new_sentence["value"], edit["targetPath"]) if edit["targetPath"] else new_sentence["value"])
        diff_entries.append({"editId": edit["editId"], "operation": operation, "targetLineage": target_lineage, "targetPath": edit["targetPath"], "beforeFingerprint": before, "afterFingerprint": after, "affectedProvenance": affected})
    diff_value = {"schemaVersion": 1, "baselineDefinitionDigest": original["definitionDigest"], "mutantDefinitionDigest": output["definitionDigest"], "portableApplication": "applied-and-locally-well-formed", "nativeIrValidation": "rust-proof-pending", "entries": diff_entries}
    diff_value["diffId"] = digest("k-in-k/structural-diff/v1", diff_value)
    return output, diff_value, None


def materialize_vector_patch(data: dict[str, Any], case: dict[str, Any]) -> dict[str, Any]:
    edits: list[dict[str, Any]] = []
    for template in case["edits"]:
        edit = deepcopy(template)
        value_ref = edit.pop("valueRef")
        edit["value"] = deepcopy(data["valuePool"][value_ref])
        edit["editId"] = digest("k-in-k/edit/v1", edit)
        edits.append(edit)
    edits.sort(key=lambda edit: (edit["targetLineage"] or "", canonical(edit["targetPath"]), edit["operation"], edit["editId"]))
    patch = {"schemaVersion": 1, "operatorId": case["operatorId"], "operatorVersion": case["operatorVersion"], "edits": edits}
    patch["patchId"] = digest("k-in-k/patch/v1", {"schemaVersion": 1, "edits": edits})
    return patch


def validate_structural_diff_provenance(diff_value: dict[str, Any], baseline: dict[str, Any], mutant: dict[str, Any]) -> None:
    ok(diff_value["baselineDefinitionDigest"] == baseline["definitionDigest"] and diff_value["mutantDefinitionDigest"] == mutant["definitionDigest"], "structural diff definition roots do not resolve exactly")
    baseline_sentences = sentence_index(baseline)
    mutant_sentences = sentence_index(mutant)
    for entry in diff_value["entries"]:
        lineage = entry["targetLineage"]
        if entry["operation"] == "insert-sentence":
            ok(lineage not in baseline_sentences and lineage in mutant_sentences, "insertion diff lineage is not output-only")
            expected = mutant_sentences[lineage][1]["provenance"]
            ok(entry["beforeFingerprint"] is None and entry["afterFingerprint"] == expected["contentFingerprint"], "insertion diff fingerprints differ from output provenance")
        else:
            ok(lineage in baseline_sentences, "edit diff lineage is absent from the baseline")
            expected = baseline_sentences[lineage][1]["provenance"]
            if entry["operation"] == "delete-sentence":
                ok(lineage not in mutant_sentences and entry["beforeFingerprint"] == expected["contentFingerprint"] and entry["afterFingerprint"] is None, "deletion diff fingerprints/lineage differ from baseline and output")
            else:
                ok(lineage in mutant_sentences, "nondeletion diff lineage disappeared from the output")
        ok(entry["affectedProvenance"] == expected, "structural diff affected provenance is not the exact canonical sentence provenance")


def verify_patch_applications() -> None:
    data = load(VECTORS / "patch-application-vectors.json")
    ok(data["portableApplicationBoundary"] == {"portableApplication": "applied-and-locally-well-formed", "nativeIrValidation": "rust-proof-pending"}, "patch vectors blur portable application and native IR validation")
    schema_path = SCHEMAS / "patch.schema.json"
    patch_schema = load(schema_path)
    diff_schema_path = SCHEMAS / "structural-diff.schema.json"
    diff_schema = load(diff_schema_path)
    seen: set[str] = set()
    families: set[str] = set()
    covered_operations: set[str] = set()
    covered_positions: set[str] = set()
    for case in data["cases"]:
        ok(case["id"] not in seen, f"duplicate patch application vector {case['id']}")
        seen.add(case["id"])
        definition = load(FIXTURES / case["definitionFixture"])
        families.add(definition["family"]["familyName"])
        patch = materialize_vector_patch(data, case)
        covered_operations.update(edit["operation"] for edit in patch["edits"])
        covered_positions.update(edit["position"]["kind"] for edit in patch["edits"] if "position" in edit)
        validate_schema(patch, patch_schema, schema_path, patch_schema)
        output, diff_value, failure = apply_portable_patch(definition, patch)
        expected = case["expected"]
        if expected["valid"]:
            ok(failure is None and output is not None and diff_value is not None, f"{case['id']}: portable patch failed with {failure}")
            ok(expected["appliedEditCount"] == len(patch["edits"]), f"{case['id']}: applied edit count")
            output_transformation_inputs = {sentence["generatedIdentity"]["transformationId"]: definition for module in output["modules"] for sentence in module["sentences"] if sentence["generatedIdentity"] is not None}
            validate_definition_semantics(output, transformation_inputs=output_transformation_inputs)
            validate_schema(diff_value, diff_schema, diff_schema_path, diff_schema)
            validate_structural_diff_provenance(diff_value, definition, output)
            ok({key: diff_value[key] for key in ("portableApplication", "nativeIrValidation")} == data["portableApplicationBoundary"], f"{case['id']}: patch result overclaims native validation")
            ok(output["definitionDigest"] == expected["outputDefinitionDigest"], f"{case['id']}: output definition digest")
            ok(diff_value["diffId"] == expected["diffId"], f"{case['id']}: structural diff digest")
            repeated_output, repeated_diff, repeated_failure = apply_portable_patch(definition, patch)
            ok(repeated_failure is None and repeated_output == output and repeated_diff == diff_value, f"{case['id']}: repeated application was nondeterministic")
            provenance_drift = deepcopy(diff_value)
            provenance_drift["entries"][0]["affectedProvenance"]["label"] = "wrong-provenance-label"
            provenance_drift["diffId"] = digest("k-in-k/structural-diff/v1", value_without(provenance_drift, "diffId"))
            expect_semantic_rejection(lambda value: validate_structural_diff_provenance(value, definition, output), provenance_drift, f"{case['id']}: structural diff human provenance drift was accepted")
        else:
            ok(output is None and diff_value is None and failure == expected["failure"], f"{case['id']}: expected {expected['failure']}, got {failure}")
            ok(expected["appliedEditCount"] == 0, f"{case['id']}: failed patch exposed applications")
    ok(len(families) >= 2, "patch vectors do not cover two fixture families")
    ok(covered_operations == {"replace-term", "replace-sentence", "delete-sentence", "insert-sentence", "replace-condition", "add-attribute", "remove-attribute", "replace-attribute"}, "patch vectors do not cover every operation")
    ok(covered_positions == {"before-lineage", "after-lineage", "module-start", "module-end"}, "patch vectors do not cover every insertion position")
    injected_definition = load(FIXTURES / "semantic-definition-memory.json")
    injected_sentence = injected_definition["modules"][0]["sentences"][0]["value"]
    injected_sentence["body"]["node"]["left"]["node"]["args"][0] = {
        "encoding": "portable-term-v1", "sort": "Address",
        "node": {"kind": "injection", "fromSort": "Int", "toSort": "Address", "term": {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "token", "text": "1"}}},
    }
    injection_path = [{"kind": "field", "name": "body"}, {"kind": "field", "name": "lhs"}, {"kind": "argument", "index": 0}, {"kind": "injection-term"}]
    ok(path_get(injected_sentence, injection_path)["sort"] == "Int", "injection descendant path did not resolve")
    replacement = {"encoding": "portable-term-v1", "sort": "Int", "node": {"kind": "token", "text": "2"}}
    path_replace(injected_sentence, injection_path, replacement)
    ok(path_get(injected_sentence, injection_path) == replacement, "injection descendant replacement failed")
    cross = data["crossModuleInsertionIdentity"]
    left_definition = load(FIXTURES / cross["definitionFixtures"][0])
    right_definition = load(FIXTURES / cross["definitionFixtures"][1])
    combined = deepcopy(left_definition)
    right_module = deepcopy(right_definition["modules"][0])
    right_module["ordinal"] = len(combined["modules"])
    combined["modules"].append(right_module)
    combined["family"] = {"familyName": "cross-module-portable-slice", "entryModules": [module["name"] for module in combined["modules"]], "compatibilityProfile": left_definition["family"]["compatibilityProfile"]}
    combined["baselineFamilyId"] = digest("k-in-k/baseline-family/v1", baseline_family_payload(combined["family"]))
    for module in combined["modules"]:
        for sentence in module["sentences"]:
            value = sentence["value"]
            sentence["provenance"]["lineageId"] = digest("k-in-k/input-lineage/v1", {"baselineFamilyId": combined["baselineFamilyId"], "module": module["name"], "source": value["source"], "location": value["location"], "kind": value["kind"], "sourceOccurrenceOrdinal": sentence["sourceOccurrenceOrdinal"]})
    combined = refreshed_definition(combined)
    validate_definition_semantics(combined)
    cross_edits: list[dict[str, Any]] = []
    for module in combined["modules"]:
        value = deepcopy(data["valuePool"]["inserted-memory-sentence"])
        value["sentence"]["module"] = module["name"]
        value["sentence"]["source"] = f"generated://{module['name'].lower()}/audit"
        edit = {"operation": "insert-sentence", "targetLineage": None, "expectedContent": None, "expectedModuleFingerprint": module["fingerprint"], "targetPath": [], "position": {"kind": cross["position"], "module": module["name"], "ordinal": cross["ordinal"]}, "value": value}
        edit["editId"] = digest("k-in-k/edit/v1", edit)
        cross_edits.append(edit)
    cross_edits.sort(key=lambda edit: (edit["targetLineage"] or "", canonical(edit["targetPath"]), edit["operation"], edit["editId"]))
    cross_patch = {"schemaVersion": 1, "operatorId": "cross-module-insertion", "operatorVersion": 1, "edits": cross_edits}
    cross_patch["patchId"] = digest("k-in-k/patch/v1", {"schemaVersion": 1, "edits": cross_edits})
    cross_output, _, cross_failure = apply_portable_patch(combined, cross_patch)
    ok(cross["expected"]["valid"] and cross_failure is None and cross_output is not None, "cross-module insertion vector failed")
    inserted = [sentence for module in cross_output["modules"] for sentence in module["sentences"] if sentence["provenance"]["generated"]]
    inserted_lineages = [sentence["provenance"]["lineageId"] for sentence in inserted]
    ok(cross["expected"]["distinctGeneratedLineages"] and len(inserted_lineages) == 2 and len(set(inserted_lineages)) == 2, "cross-module insertions collided")
    ok({sentence["generatedIdentity"]["anchorIdentity"] for sentence in inserted} == {module["fingerprint"] for module in combined["modules"]}, "module insertion identity omitted its destination anchor")
    wrong_module_patch = deepcopy(cross_patch)
    wrong_module_patch["edits"][0]["value"]["sentence"]["module"] = "WRONG"
    wrong_output, wrong_diff, wrong_failure = apply_portable_patch(combined, wrong_module_patch)
    ok(wrong_output is None and wrong_diff is None and wrong_failure == "invalid-position", "cross-module insertion accepted a mismatched sentence module")
    base_case = next(case for case in data["cases"] if case["id"] == "before-and-module-end-insertion")
    valid_patch = materialize_vector_patch(data, base_case)
    bad = deepcopy(valid_patch)
    bad["edits"] = [edit for edit in bad["edits"] if edit["position"]["kind"] == "before-lineage"]
    bad["edits"][0]["position"].pop("anchorLineage")
    expect_schema_rejection(bad, "patch.schema.json", "before-lineage insertion without anchor was accepted")
    bad = deepcopy(valid_patch)
    bad["edits"] = [edit for edit in bad["edits"] if edit["position"]["kind"] == "module-end"]
    bad["edits"][0].pop("expectedModuleFingerprint")
    expect_schema_rejection(bad, "patch.schema.json", "module insertion without module fingerprint was accepted")
    add_case = next(case for case in data["cases"] if case["id"] == "add-attribute")
    bad = materialize_vector_patch(data, add_case)
    bad["edits"][0]["expectedAttributeFingerprint"] = "f" * 64
    expect_schema_rejection(bad, "patch.schema.json", "attribute add with old fingerprint was accepted")
    remove_case = next(case for case in data["cases"] if case["id"] == "remove-attribute")
    bad = materialize_vector_patch(data, remove_case)
    bad["edits"][0]["value"] = deepcopy(data["valuePool"]["attribute-transition"])
    expect_schema_rejection(bad, "patch.schema.json", "attribute removal with replacement value was accepted")
    condition_case = next(case for case in data["cases"] if case["id"] == "replace-condition-second-family")
    bad = materialize_vector_patch(data, condition_case)
    bad["edits"][0]["targetPath"] = [{"kind": "field", "name": "body"}]
    expect_schema_rejection(bad, "patch.schema.json", "condition replacement outside requires/ensures was accepted")
    unsupported = materialize_vector_patch(data, condition_case)
    unsupported["edits"][0]["operation"] = "rewrite-host-node"
    expect_schema_rejection(unsupported, "patch.schema.json", "unsupported patch operation was accepted")

    atomic_case = next(case for case in data["cases"] if case["id"] == "atomic-distinct-sentence-replacements")
    outer_drift = materialize_vector_patch(data, atomic_case)
    outer_drift["edits"] = outer_drift["edits"][:1]
    outer_drift["edits"][0]["value"] = deepcopy(data["valuePool"]["zero-int"])
    output, diff_value, failure = apply_portable_patch(load(FIXTURES / atomic_case["definitionFixture"]), outer_drift)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "replace-term outer-sort drift was published")

    original_drift = materialize_vector_patch(data, atomic_case)
    original_drift["edits"] = original_drift["edits"][:1]
    original_drift["edits"][0]["value"] = {"kind": "original-reference", "fromOriginalLineage": original_drift["edits"][0]["targetLineage"], "fromOriginalPath": [{"kind": "field", "name": "body"}, {"kind": "field", "name": "rhs"}, {"kind": "argument", "index": 1}]}
    output, diff_value, failure = apply_portable_patch(load(FIXTURES / atomic_case["definitionFixture"]), original_drift)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "original-reference outer-sort drift was published")

    non_bool_patch = materialize_vector_patch(data, condition_case)
    non_bool_patch["edits"][0]["value"] = deepcopy(data["valuePool"]["zero-int"])
    output, diff_value, failure = apply_portable_patch(load(FIXTURES / condition_case["definitionFixture"]), non_bool_patch)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "non-Bool condition replacement was published")

    mismatched_attribute = materialize_vector_patch(data, add_case)
    mismatched_attribute["edits"][0]["value"]["name"] = "renamed-without-operation"
    output, diff_value, failure = apply_portable_patch(load(FIXTURES / add_case["definitionFixture"]), mismatched_attribute)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "attribute target/value-name mismatch was published")

    signature_drift = materialize_vector_patch(data, atomic_case)
    signature_drift["edits"] = signature_drift["edits"][:1]
    baseline = load(FIXTURES / atomic_case["definitionFixture"])
    known_head = baseline["modules"][0]["sentences"][0]["value"]["body"]["node"]["left"]["node"]
    signature_drift["edits"][0]["value"] = {"kind": "term", "term": {"encoding": "portable-term-v1", "sort": "Address", "node": {"kind": "application", "symbolId": known_head["symbolId"], "label": known_head["label"], "args": deepcopy(baseline["modules"][0]["sentences"][0]["value"]["body"]["node"]["left"]["node"]["args"])}}}
    output, diff_value, failure = apply_portable_patch(baseline, signature_drift)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "baseline-known signature drift after replacement was published")

    sentence_case = next(case for case in data["cases"] if case["id"] == "replace-sentence-second-family")
    sentence_baseline = load(FIXTURES / sentence_case["definitionFixture"])
    for field, replacement in (
        ("module", "WRONG-MODULE"),
        ("source", "repo://wrong/source.k"),
        ("kind", "claim"),
        ("location", {"startLine": 90, "startColumn": 1, "endLine": 90, "endColumn": 2}),
    ):
        contradictory = materialize_vector_patch(data, sentence_case)
        contradictory["edits"][0]["value"]["sentence"][field] = replacement
        output, diff_value, failure = apply_portable_patch(sentence_baseline, contradictory)
        ok(output is None and diff_value is None and failure == "locally-ill-formed", f"replacement-sentence {field} contradiction was published")
    for field in ("lineageId", "module", "source", "kind", "location"):
        contradictory_baseline = deepcopy(sentence_baseline)
        provenance = contradictory_baseline["modules"][0]["sentences"][0]["provenance"]
        provenance[field] = "f" * 64 if field == "lineageId" else "WRONG" if field in {"module", "source", "kind"} else {"startLine": 99, "startColumn": 1, "endLine": 99, "endColumn": 2}
        output, diff_value, failure = apply_portable_patch(contradictory_baseline, materialize_vector_patch(data, sentence_case))
        ok(output is None and diff_value is None and failure == "locally-ill-formed", f"contradictory baseline {field} provenance entered patch publication")

    last_occurrence = materialize_vector_patch(data, sentence_case)
    target_lineage = last_occurrence["edits"][0]["targetLineage"]
    target_sentence = next(sentence for module in sentence_baseline["modules"] for sentence in module["sentences"] if sentence["provenance"]["lineageId"] == target_lineage)
    replacement_sentence = deepcopy(target_sentence["value"])
    application_nodes: list[dict[str, Any]] = []
    def collect_applications(term: dict[str, Any]) -> None:
        node = term["node"]
        if node["kind"] == "application":
            application_nodes.append(node)
            for argument in node["args"]:
                collect_applications(argument)
        elif node["kind"] == "rewrite":
            collect_applications(node["left"]); collect_applications(node["right"])
        elif node["kind"] == "sequence":
            for item in node["items"]: collect_applications(item)
        elif node["kind"] == "injection":
            collect_applications(node["term"])
    collect_applications(replacement_sentence["body"])
    unique_node = next(node for node in application_nodes if sum(1 for candidate in application_nodes if candidate["symbolId"] == node["symbolId"]) == 1)
    unique_node["label"] += "-conflict"
    last_occurrence["edits"][0]["value"] = {"kind": "sentence", "sentence": replacement_sentence}
    output, diff_value, failure = apply_portable_patch(sentence_baseline, last_occurrence)
    ok(output is None and diff_value is None and failure == "locally-ill-formed", "replacing the last original symbol occurrence bypassed immutable baseline signature seeding")

    fresh_symbol = materialize_vector_patch(data, atomic_case)
    fresh_symbol["edits"] = fresh_symbol["edits"][:1]
    fresh_symbol["edits"][0]["value"] = {"kind": "term", "term": {"encoding": "portable-term-v1", "sort": "Address", "node": {"kind": "application", "symbolId": "f" * 64, "label": "portable-only-fresh", "args": []}}}
    output, diff_value, failure = apply_portable_patch(baseline, fresh_symbol)
    ok(failure is None and output is not None and diff_value is not None and diff_value["nativeIrValidation"] == "rust-proof-pending", "singleton fresh symbol was reported native-valid instead of portable-only success")


def verify_mutation() -> None:
    data = load(VECTORS / "mutation-vectors.json")
    for item in data["idDerivation"]:
        ok(digest(item["domain"], item["payload"]) == item["expected"], f"{item['kind']} ID derivation")
    same_lineage_sites = [item for item in data["idDerivation"] if item["kind"].startswith("site")]
    ok(len(same_lineage_sites) >= 2 and len({item["expected"] for item in same_lineage_sites}) == len(same_lineage_sites), "same-lineage mutation sites at different term paths collided")
    sites = data["sites"]
    site_key = lambda name: (sites[name]["moduleOrdinal"], sites[name]["location"], sites[name]["lineage"])
    for case in data["selectionCases"]:
        expected = case["expected"]
        supplied = case["suppliedSiteTuples"]
        if case["policy"] == "exact":
            wrong_arity = any(len(item) != case["expectedTupleArity"] for item in supplied)
            if wrong_arity:
                ok(expected.get("failure") == "invalid-join" and expected["candidateSiteTuples"] == [], f"{case['id']}: exact tuple arity")
            elif len(supplied) != case["expectedTupleCount"]:
                ok(expected.get("failure") == "cardinality-mismatch" and expected["candidateSiteTuples"] == [], f"{case['id']}: exact tuple count")
            elif "candidateSiteTuples" in expected:
                ok(expected["candidateSiteTuples"] == supplied, f"{case['id']}: exact success")
        if case["id"] == "each-canonical-order":
            ok(expected["candidateSiteTuples"] == [[name] for name in sorted((item[0] for item in supplied), key=site_key)], "each ordering")
        if case["id"] == "tuple-each-symmetric-dedup":
            normalized = {tuple(sorted(item, key=site_key)) for item in supplied}
            ok([list(item) for item in sorted(normalized, key=lambda item: tuple(site_key(name) for name in item))] == expected["candidateSiteTuples"], "symmetric tuple dedup")
        if case["id"] == "all-matches-one-atomic-instance":
            ok(expected["candidateSiteTuples"] == [[*sorted((item[0] for item in supplied), key=site_key)]], "all-matches ordering")
            ok(expected["mutantCount"] == 1, "all-matches must be one mutant")
        if not expected["complete"]:
            ok(expected["failure"] == "incomplete-generation" and not expected["defaultScored"], "incomplete generation scoring")
            canonical_sites = [[name] for name in sorted((item[0] for item in supplied), key=site_key)]
            ok(expected["candidateSiteTuples"] == canonical_sites[:case["candidateCap"]], "candidate-cap membership")
        if case["id"] == "duplicate-site-rejected":
            ok(expected["failure"] == "duplicate-site" and expected["candidateSiteTuples"] == [], "duplicate site handling")
        if case["id"] == "binding-order-normalized":
            normalized = [sorted(binding_set, key=lambda item: item["name"]) for binding_set in case["bindings"]]
            ok(normalized[0] == normalized[1] and expected["sameBindingDigest"], "binding normalization")
    taxonomy = {(item["stage"], item["classification"]) for item in load(PACKAGE / "failure-taxonomy.json")["entries"]}
    for case in data["validationCases"]:
        ok((case["stage"], case["expected"]["failure"]) in taxonomy, f"{case['id']}: unregistered failure")
        if "outputConstructed" in case["expected"]:
            ok(not case["expected"]["outputConstructed"], f"{case['id']}: validation failure constructed output")
    valid_operations = {"replace-term", "replace-sentence", "delete-sentence", "insert-sentence", "replace-condition", "add-attribute", "remove-attribute", "replace-attribute"}
    contents = {"write": "d" * 64, "load": "e" * 64, "free": "9" * 64}
    ok("patchCases" not in data, "obsolete shorthand patch cases re-entered the portable vectors")
    for case in data.get("patchCases", []):
        edits = case["edits"]
        expected = case["expected"]
        detected: str | None = None
        if case.get("declaredReplacementEqualsOriginal"):
            detected = "no-change"
        elif any(edit["operation"] not in valid_operations for edit in edits):
            detected = "unsupported-operation"
        elif any(edit["path"] and not edit["path"].startswith("/") for edit in edits):
            detected = "malformed-path"
        elif any(edit["expectedContent"] != contents[edit["target"]] for edit in edits):
            detected = "stale-precondition"
        else:
            for index, left in enumerate(edits):
                for right in edits[index + 1:]:
                    if left["target"] == right["target"] and paths_overlap(left["path"], right["path"]):
                        detected = "duplicate-target" if left["path"] == right["path"] else "overlapping-edit"
        if expected["valid"]:
            ok(detected is None, f"{case['id']}: unexpected patch rejection {detected}")
            ok(expected["outputConstructed"] and expected["appliedEditCount"] == len(edits), f"{case['id']}: successful commit count")
        else:
            ok(detected == expected["failure"], f"{case['id']}: expected {expected['failure']}, detected {detected}")
            ok(not expected["outputConstructed"] and expected["appliedEditCount"] == 0, f"{case['id']}: failure exposed partial output")
    excluded_statuses = {"invalid", "timeout", "unknown", "error", "duplicate", "no-change"}
    for case in data["campaignCases"]:
        expected = case["expected"]
        if case["baseline"] != "valid":
            ok(not expected["scored"], f"{case['id']}: invalid baseline scored")
            continue
        if case["id"] == "default-score-exclusions":
            statuses = case["mutants"]
            killed, survived = statuses.count("killed"), statuses.count("survived")
            ok(expected["denominator"] == killed + survived, "score denominator")
            ok(set(expected["excluded"]) == excluded_statuses, "score exclusion set")
            ok(expected["ratio"] == {"numerator": 1, "denominator": 2}, "score ratio")
        if case["id"] == "timeout-is-not-survived":
            ok(expected["survived"] == 0 and expected["denominator"] == 0 and expected["ratio"] is None, "timeout scoring")
        if case["id"] == "coupled-patch-is-one-mutant":
            ok(expected["mutantCount"] == 1 and case["mutants"][0]["editCount"] == 2, "coupled mutant cardinality")
        if "crashScope" in case:
            required = "error" if case["crashScope"] == "infrastructure" else "killed"
            ok(expected["status"] == required, f"{case['id']}: crash classification")


def mutation_package_registry() -> dict[str, dict[str, dict[str, Any]]]:
    catalogs = [load(FIXTURES / "artifact-catalog.json")]
    manifests = [load(FIXTURES / "mutation-manifest.json")]
    operators = [load(FIXTURES / "mutation-operator.json")]
    site_registries = [load(FIXTURES / "mutation-site-registry.json")]
    replays = [load(FIXTURES / name) for name in ("replay-manifest.json", "write-only-replay-manifest.json", "mutation-pattern-replay-manifest.json", "mutation-replay-manifest.json")]
    diffs = [load(FIXTURES / "structural-diff.json")]
    patterns = [load(FIXTURES / name) for name in ("pattern-result.json", "write-only-pattern-result.json", "mutation-pattern-result.json")]
    traces = [load(FIXTURES / name) for name in ("event-trace.json", "write-only-event-trace.json", "mutation-event-trace.json")]
    trace_registry = {digest("k-in-k/event-trace/v1", item): item for item in traces}
    observations = [load(FIXTURES / name) for name in ("observation-manifest.json", "mutation-observation-manifest.json")]
    observation_registry = {item["manifestId"]: item for item in observations}
    baseline_definition = load(FIXTURES / "semantic-definition-memory.json")
    campaign = load(FIXTURES / "mutation-campaign.json")
    mutant_definition, _, mutation_failure = apply_portable_patch(baseline_definition, campaign["generation"]["candidates"][0]["patch"])
    ok(mutation_failure is None and mutant_definition is not None, "portable mutant definition could not be materialized for artifact validation")
    definitions = {baseline_definition["definitionDigest"]: baseline_definition, mutant_definition["definitionDigest"]: mutant_definition}
    validate_mutation_site_registry(site_registries[0], baseline_definition, operators[0])
    for observation in observations:
        ok(observation["inputDefinitionDigest"] in definitions, "observation manifest definition is unavailable")
        validate_observation_manifest_semantics(observation, definitions[observation["inputDefinitionDigest"]])
        validate_observation_bindings(observation, definitions[observation["inputDefinitionDigest"]])
    invocation_replays = {item["invocationDigest"]: item for item in replays if item["kind"] == "pattern-query"}
    for pattern in patterns:
        validate_pattern_result_semantics(pattern, trace_registry)
        inputs = pattern["inputs"]
        ok(inputs["definitionDigest"] in definitions and inputs["observationManifestDigest"] in observation_registry, "pattern definition/observation graph is dangling")
        observation = observation_registry[inputs["observationManifestDigest"]]
        ok(observation["inputDefinitionDigest"] == inputs["definitionDigest"] and observation["observerDigest"] == inputs["observerDigest"] and observation["compatibilityProfileDigest"] == inputs["compatibilityProfileDigest"] and observation["transformationId"] == inputs["transformationId"], "pattern inputs differ from resolved observation")
        ok(inputs["replayInvocationDigest"] in invocation_replays, "pattern replay invocation is dangling")
        pattern_replay = invocation_replays[inputs["replayInvocationDigest"]]
        ok(pattern_replay["testId"] == pattern["testId"] and pattern_replay["expectedResultDigest"] == pattern["resultId"] and pattern_replay["definitionDigest"] == inputs["definitionDigest"] and pattern_replay["programDigest"] == inputs["programDigest"] and pattern_replay["parserDigest"] == inputs["parserDigest"] and pattern_replay["startSymbol"] == inputs["startSymbol"] and pattern_replay["queryId"] == pattern["queryId"] and pattern_replay["executionMode"] == inputs["executionMode"] and pattern_replay["observerDigest"] == inputs["observerDigest"] and pattern_replay["observationManifestDigest"] == inputs["observationManifestDigest"] and pattern_query_root(pattern_replay) == pattern_query_root(inputs) and pattern_replay["transformationDigests"] == [inputs["transformationId"]] and pattern_replay["compatibilityProfileDigest"] == inputs["compatibilityProfileDigest"] and pattern_replay["executionProfileDigest"] == inputs["executionProfileDigest"] and pattern_replay["solverProfileDigest"] == inputs["solverProfileDigest"] and pattern_replay["optionsDigest"] == inputs["optionsDigest"] and pattern_replay["searchPolicy"] == inputs["searchPolicy"] and pattern_replay["bounds"] == pattern["bounds"], "pattern result differs from resolved replay invocation")
        for path in pattern["pathResults"]:
            trace = trace_registry[path["traceDigest"]]
            for event in trace["events"]:
                validate_event_against_observation(event, observation, definitions[inputs["definitionDigest"]])
    corpora = [load(FIXTURES / "corpus-manifest.json")]
    terminals, crashes = terminal_artifact_registry()
    oracle_values = oracle_value_registry()
    return {
        "catalogs": {item["catalogId"]: item for item in catalogs},
        "manifests": {item["manifestId"]: item for item in manifests},
        "operators": {item["operatorDigest"]: item for item in operators},
        "siteRegistries": {item["registryId"]: item for item in site_registries},
        "replays": {item["replayId"]: item for item in replays},
        "diffs": {item["diffId"]: item for item in diffs},
        "patterns": {item["resultId"]: item for item in patterns},
        "traces": trace_registry,
        "observations": observation_registry,
        "definitions": definitions,
        "corpora": {item["manifestId"]: item for item in corpora},
        "terminals": terminals,
        "crashes": crashes,
        "oracleValues": oracle_values,
    }


def policy_case_support(operator: dict[str, Any], site_registry: dict[str, Any], definition_digest: str) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    def policy_opaque(role: str, label: str) -> str:
        content_hash = hashlib.sha256(f"BAG-08 synthetic policy {label}\n".encode("ascii")).hexdigest()
        return opaque_artifact_digest(role, "application/octet-stream", content_hash)
    requirements = [
        ("definition", definition_digest), ("mutation-operator", operator["operatorDigest"]),
        ("mutation-site-registry", site_registry["registryId"]),
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
    case_id = operator["operatorId"].removeprefix("policy-")
    opaque_fields = {operator["moduleDigest"]: ("mutation-module", f"{case_id}:module"), operator["preconditionDigest"]: ("precondition", f"{case_id}:precondition"), operator["postconditionDigest"]: ("postcondition", f"{case_id}:postcondition"), operator["patchTemplateDigest"]: ("patch-template", f"{case_id}:template"), projection_digest: ("oracle-projection", "projection"), comparison_digest: ("oracle-comparison", "comparison"), program_digest: ("program", "program"), parser_digest: ("parser", "parser"), options_digest: ("options", "options"), lowering_profile_digest: ("lowering-profile", "lowering-profile")}
    structured = {"definition", "mutation-operator", "mutation-site-registry", "mutation-selector", "mutation-join", "oracle-value"}
    entries = []
    for role, value in sorted(requirements):
        model = "canonical-json" if role in structured else "opaque-bytes"
        if role == "oracle-value":
            content_hash = hashlib.sha256(canonical(oracle_value).encode("utf-8")).hexdigest()
        elif value in opaque_fields:
            _known_role, label = opaque_fields[value]
            content_hash = hashlib.sha256(f"BAG-08 synthetic policy {label}\n".encode("ascii")).hexdigest()
        else:
            content_hash = hashlib.sha256(f"BAG-08 reviewed synthetic policy pin {role}:{value}\n".encode("ascii")).hexdigest()
        entries.append({"role": role, "digest": value, "contentModel": model, "mediaType": "application/json" if model == "canonical-json" else "application/octet-stream", "contentSha256": content_hash, "availability": "external-required", "logicalPath": f"artifact://policy/{role}/{value}", "resolverId": "rust-artifact-store-v1"})
    catalog = {"schemaVersion": 1, "entries": entries, "unboundRequirements": []}
    catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(catalog, "catalogId"))
    corpus = {"definitionDigest": definition_digest, "artifactCatalogDigest": catalog["catalogId"], "tests": [], "bounds": {"depth": 1, "timeMs": 1, "branches": 1, "results": 1}}
    corpus["manifestId"] = digest("k-in-k/policy-corpus/v1", value_without(corpus, "manifestId"))
    oracle = {"oracleId": "policy-oracle", "kind": "final-result", "projectionDigest": projection_digest, "comparisonDigest": comparison_digest, "crashPolicy": "semantic-crash-distinguishes", "baselineTerminalPolicy": "normal-required", "artifacts": [{"role": "oracle-projection", "digest": projection_digest}, {"role": "oracle-comparison", "digest": comparison_digest}]}
    test = {"testId": "policy-test", "programDigest": program_digest, "parserDigest": parser_digest, "startSymbol": "PolicyStart", "optionsDigest": options_digest, "boundsDigest": "76" * 32, "invocationDigest": "77" * 32, "oracleIds": ["policy-oracle"], "patternQueries": []}
    manifest = {"artifactCatalogDigest": catalog["catalogId"], "definitionDigest": definition_digest, "operatorDigest": operator["operatorDigest"], "siteRegistryDigest": site_registry["registryId"], "corpusManifestDigest": corpus["manifestId"], "loweringProfileDigest": lowering_profile_digest, "loweringEvidence": [], "tests": [test], "oracles": [oracle]}
    manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", manifest)
    return catalog, corpus, manifest


def policy_case_registry(case: dict[str, Any]) -> dict[str, dict[str, dict[str, Any]]]:
    operator, site_registry, campaign = case["operator"], case["siteRegistry"], case["campaign"]
    definition_digest = campaign["baseline"]["definitionDigest"]
    catalog, corpus, manifest = policy_case_support(operator, site_registry, definition_digest)
    return {
        "catalogs": {catalog["catalogId"]: catalog}, "manifests": {manifest["manifestId"]: manifest},
        "operators": {operator["operatorDigest"]: operator}, "siteRegistries": {site_registry["registryId"]: site_registry},
        "replays": {}, "diffs": {}, "patterns": {}, "traces": {}, "observations": {}, "definitions": {}, "oracleValues": {}, "terminals": {}, "crashes": {},
        "corpora": {corpus["manifestId"]: corpus},
    }


def refresh_policy_case_roots(case: dict[str, Any]) -> None:
    operator, site_registry, campaign = case["operator"], case["siteRegistry"], case["campaign"]
    operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", value_without(operator, "operatorDigest"))
    site_registry["operatorDigest"] = operator["operatorDigest"]
    site_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", value_without(site_registry, "registryId"))
    campaign["operator"] = {"id": operator["operatorId"], "version": operator["operatorVersion"], "digest": operator["operatorDigest"]}
    campaign["generation"]["siteRegistryDigest"] = site_registry["registryId"]
    campaign["generation"]["policy"] = operator["policy"]
    campaign["generation"]["candidateCap"] = operator["candidateCap"]
    for candidate in campaign["generation"]["candidates"]:
        for origin in candidate["originInstances"]:
            for receipt in origin["editReceipts"]:
                receipt["operator"] = deepcopy(campaign["operator"])
                receipt["patchTemplateDigest"] = operator["patchTemplateDigest"]
            origin["instanceId"] = digest("k-in-k/instance/v1", mutation_instance_payload(campaign["operator"], campaign["baseline"]["definitionDigest"], operator["policy"], origin, candidate["patch"]["patchId"]))
        candidate["candidateId"] = digest("k-in-k/candidate/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": campaign["baseline"]["definitionDigest"], "patchId": candidate["patch"]["patchId"]})
    for rejection in campaign["candidateRejections"]:
        candidate = next((item for item in campaign["generation"]["candidates"] if item["patch"]["patchId"] == rejection["patchId"]), None)
        if candidate is not None:
            rejection["originInstanceIds"] = [origin["instanceId"] for origin in candidate["originInstances"]]
    _, _, manifest = policy_case_support(operator, site_registry, campaign["baseline"]["definitionDigest"])
    campaign["manifestDigest"] = manifest["manifestId"]
    refresh_campaign_ids(campaign)


def normal_operand_role(kind: str) -> str:
    return "pattern-result" if kind == "execution-pattern" else "oracle-value"


def validate_operand_terminal(terminal: Any, kind: str) -> None:
    if terminal is None:
        return
    artifact = terminal["artifact"]
    expected_role = "semantic-crash" if terminal["kind"] == "semantic-crash" else normal_operand_role(kind)
    ok(artifact["role"] == expected_role, "oracle operand artifact has the wrong role")


def failure_disposition(failure: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> str:
    taxonomy = load(PACKAGE / "failure-taxonomy.json") if taxonomy is None else taxonomy
    matches = [placement["consequence"] for entry in taxonomy["entries"] if (entry["stage"], entry["classification"]) == (failure["stage"], failure["classification"]) for placement in entry["placements"] if (placement["context"], placement["scope"]) == (failure["context"], failure["scope"])]
    ok(len(matches) == 1 and "disposition" in matches[0], "failure has no exact taxonomy disposition")
    return matches[0]["disposition"]


FAILURE_CONTEXT_CONSUMERS = {
    "baseline-execution": {"campaign", "oracle"},
    "baseline-oracle-gate": {"campaign", "oracle"},
    "baseline-validation": {"campaign"},
    "campaign": {"campaign"},
    "candidate-generation": {"campaign"},
    "corpus-shared-setup": {"corpus"},
    "mutant-execution": {"campaign", "oracle"},
    "mutant-validation": {"campaign"},
    "mutation-discovery": {"policy-registry"},
    "observation-installation": {"observation-installation"},
    "oracle-operand-production": {"oracle"},
    "oracle-comparison": {"campaign", "oracle"},
    "pattern-path": {"corpus", "pattern"},
    "pattern-test": {"corpus", "pattern"},
    "report-publication": {"report-publication"},
}


def consume_failure_disposition(failure: dict[str, Any], consumer: str, taxonomy: dict[str, Any] | None = None) -> str:
    context = failure["context"]
    ok(context in FAILURE_CONTEXT_CONSUMERS and consumer in FAILURE_CONTEXT_CONSUMERS[context], f"{consumer} is not the registered consequence consumer for {context}")
    return failure_disposition(failure, taxonomy)


def disposition_oracle_outcome(disposition: str, incomparable: bool = False) -> str:
    if incomparable and disposition == "error":
        return "incomparable"
    return "error" if disposition in {"baseline-invalid", "baseline-oracle-failed", "unpublishable-report", "selection-failed", "incomplete-generation", "rejected", "invalid"} else disposition


def failure_outcome(failure: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> str:
    disposition = consume_failure_disposition(failure, "oracle", taxonomy)
    return disposition_oracle_outcome(disposition, failure["classification"] == "incomparable-result")


def report_publication_disposition(failure: dict[str, Any], taxonomy: dict[str, Any] | None = None) -> str:
    disposition = consume_failure_disposition(failure, "report-publication", taxonomy)
    ok(disposition == "unpublishable-report", "report publication failure differs from its taxonomy consequence")
    return disposition


def taxonomy_with_disposition(stage: str, classification: str, context: str, scope: str, disposition: str) -> dict[str, Any]:
    taxonomy = deepcopy(load(PACKAGE / "failure-taxonomy.json"))
    matches = [placement for entry in taxonomy["entries"] if (entry["stage"], entry["classification"]) == (stage, classification) for placement in entry["placements"] if (placement["context"], placement["scope"]) == (context, scope)]
    ok(len(matches) == 1, "taxonomy drift target is not an exact placement")
    matches[0]["consequence"] = {"disposition": disposition}
    taxonomy["taxonomyId"] = digest("k-in-k/failure-taxonomy/v1", value_without(taxonomy, "taxonomyId"))
    schema_path = SCHEMAS / "failure-taxonomy.schema.json"
    schema = load(schema_path)
    validate_schema(taxonomy, schema, schema_path, schema)
    return taxonomy


def validate_oracle_against_declaration(oracle: dict[str, Any], declaration: dict[str, Any], taxonomy: dict[str, Any] | None = None, oracle_values: dict[str, dict[str, Any]] | None = None, terminal_registry: dict[str, dict[str, Any]] | None = None, crash_registry: dict[str, dict[str, Any]] | None = None) -> None:
    ok((oracle["kind"], oracle["projectionDigest"], oracle["comparisonDigest"]) == (declaration["kind"], declaration["projectionDigest"], declaration["comparisonDigest"]), "oracle result invocation semantics drift from declaration")
    wrapper = oracle["failure"]
    failure = None if wrapper is None else wrapper["failure"]
    if failure is not None and failure["classification"] == "baseline-mismatch":
        ok("operand" in oracle and wrapper["sourceSide"] == "comparison" and failure["context"] == "baseline-oracle-gate", "baseline-mismatch escaped the baseline-oracle gate")
    if "operand" in oracle:
        operand = oracle["operand"]
        ok(operand["side"] == "baseline", "baseline oracle result does not identify its side")
        terminal = operand["terminal"]
        validate_operand_terminal(terminal, oracle["kind"])
        if terminal is not None and terminal["kind"] == "semantic-crash" and declaration["baselineTerminalPolicy"] == "normal-required":
            ok(wrapper is not None and wrapper["sourceSide"] == "comparison" and failure["context"] == "baseline-oracle-gate" and failure["stage"] == "oracle" and failure["classification"] == "baseline-mismatch" and oracle["outcome"] == failure_outcome(failure, taxonomy), "normal-required baseline crash did not derive its taxonomy-projected baseline-mismatch outcome")
        elif terminal is not None:
            ok(oracle["outcome"] == "accepted" and wrapper is None, "eligible baseline terminal was not accepted cleanly")
        else:
            ok(wrapper is not None and wrapper["sourceSide"] == "baseline-execution" and failure["context"] == "baseline-execution" and oracle["outcome"] == failure_outcome(failure, taxonomy), "absent baseline operand lacks its exact-source failure")
        return
    operands = oracle["operands"]
    ok([operand["side"] for operand in operands] == ["baseline", "mutant"], "oracle operands are not canonical baseline-then-mutant")
    terminals = [operand["terminal"] for operand in operands]
    for terminal in terminals:
        validate_operand_terminal(terminal, oracle["kind"])
    if oracle["outcome"] == "skipped":
        ok(terminals == [None, None] and wrapper is None and oracle["witnessDigest"] is None, "skipped oracle retained operands, witness, or failure")
        return
    if wrapper is not None:
        source = wrapper["sourceSide"]
        if source == "baseline-execution":
            ok(terminals == [None, None] and failure["context"] == "baseline-execution", "baseline execution failure retained an operand or changed context")
        elif source == "mutant-execution":
            ok(terminals[0] is not None and terminals[1] is None and failure["context"] == "mutant-execution", "mutant execution failure has the wrong absent operand or context")
        else:
            ok(all(terminal is not None for terminal in terminals) and failure["context"] == "oracle-comparison", "comparison failure lacks both operands or changed context")
        expected_outcome = failure_outcome(failure, taxonomy)
        if failure["classification"] == "incomparable-result":
            ok(source == "comparison", "incomparable result lacks its comparison source")
        ok(oracle["outcome"] == expected_outcome, "oracle failure outcome differs from its taxonomy projection")
        ok(oracle["outcome"] != "distinguish", "a failure was classified as a semantic distinction")
        return
    ok(all(terminal is not None for terminal in terminals), "conclusive comparison lacks both operands")
    left, right = terminals
    left_key = (left["kind"], left["artifact"]["digest"])
    right_key = (right["kind"], right["artifact"]["digest"])
    if left["kind"] == right["kind"] == "normal":
        if oracle["kind"] == "final-result" and oracle_values is not None and left_key[1] in oracle_values and right_key[1] in oracle_values:
            equal_values = oracle_values[left_key[1]]["value"] == oracle_values[right_key[1]]["value"]
        else:
            equal_values = left_key == right_key
        expected = "agree" if equal_values else "distinguish"
        ok(oracle["outcome"] == expected, "normal comparison outcome differs from value equality")
    elif left["kind"] == right["kind"] == "semantic-crash" and terminal_registry is not None and crash_registry is not None and left_key[1] in crash_registry and right_key[1] in crash_registry:
        def crash_semantic_value(crash_digest: str) -> tuple[Any, ...]:
            crash = crash_registry[crash_digest]
            terminal_digest = crash["terminalState"]["digest"]
            ok(terminal_digest in terminal_registry, "semantic crash comparison has a dangling terminal state")
            return (crash["executionProfileDigest"], crash["classification"], terminal_registry[terminal_digest]["value"])
        semantically_equal = crash_semantic_value(left_key[1]) == crash_semantic_value(right_key[1])
        if semantically_equal:
            ok(oracle["outcome"] == "agree", "definition-specific but semantically equal crashes did not agree")
        elif declaration["crashPolicy"] == "semantic-crash-distinguishes":
            ok(oracle["outcome"] == "distinguish", "crash distinction differs from declared policy")
        else:
            raise AssertionError("incomparable crash comparison lacks oracle/incomparable-result failure")
    elif left_key == right_key:
        ok(oracle["outcome"] == "agree", "identical semantic crashes did not agree")
    elif declaration["crashPolicy"] == "semantic-crash-distinguishes":
        ok(oracle["outcome"] == "distinguish", "crash distinction differs from declared policy")
    else:
        raise AssertionError("incomparable crash comparison lacks oracle/incomparable-result failure")


def set_oracle_normal_operands(oracle: dict[str, Any], baseline_digest: str | None, mutant_digest: str | None) -> None:
    role = normal_operand_role(oracle["kind"])
    oracle["operands"] = [
        {"side": "baseline", "terminal": None if baseline_digest is None else {"kind": "normal", "artifact": {"role": role, "digest": baseline_digest}}},
        {"side": "mutant", "terminal": None if mutant_digest is None else {"kind": "normal", "artifact": {"role": role, "digest": mutant_digest}}},
    ]


def oracle_operand_digest(oracle: dict[str, Any], index: int) -> str | None:
    terminal = oracle["operands"][index]["terminal"]
    return None if terminal is None else terminal["artifact"]["digest"]


def authorize_lowering_nontermination(failure: dict[str, Any], subject: dict[str, Any], lowering_profile_digest: str, execution_profile_digest: str, mutation_manifest: dict[str, Any], artifact_catalog: dict[str, Any]) -> None:
    ok((failure["stage"], failure["classification"]) == ("lowering", "lowering-nontermination"), "lowering proof attached to another failure")
    ok(len(failure["semanticEvidence"]) == 1 and failure["semanticEvidence"][0]["role"] == "lowering-proof-check-receipt", "lowering nontermination lacks exactly one receipt key")
    declared = {(item["role"], item["digest"]) for item in mutation_manifest["loweringEvidence"]}
    catalog_entries = {(item["role"], item["digest"]): item for item in artifact_catalog["entries"]}
    def resolve(key: dict[str, str]) -> dict[str, Any]:
        typed_key = (key["role"], key["digest"])
        ok(typed_key in declared, "lowering evidence key is omitted from the mutation manifest")
        entry = catalog_entries.get(typed_key)
        ok(entry is not None and entry["availability"] == "bundled", "lowering evidence key is dangling or not bundled")
        verify_catalog_entry_bytes(entry, artifact_role_specs())
        return json.loads(resolve_bundled(entry).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    receipt_key = failure["semanticEvidence"][0]
    receipt = resolve(receipt_key)
    ok(receipt["receiptId"] == digest("k-in-k/lowering-proof-check-receipt/v1", value_without(receipt, "receiptId")), "lowering receipt has identity drift")
    ok((receipt["checkerId"], receipt["checkerVersion"]) == ("portable-finite-cycle-checker", 1), "lowering receipt names an unknown portable checker")
    proof = resolve(receipt["proof"])
    ok(receipt["proof"]["role"] == "lowering-cycle-proof" and proof["proofId"] == digest("k-in-k/lowering-cycle-proof/v1", value_without(proof, "proofId")), "lowering proof has wrong role or identity drift")
    ok(proof["proofKind"] == "finite-cycle-witness-v1", "lowering proof kind is not registered")
    ok(receipt["subject"] == proof["subject"] == subject, "lowering proof subject drift or baseline/mutant reversal")
    ok(receipt["loweringProfileDigest"] == proof["loweringProfileDigest"] == lowering_profile_digest, "lowering proof profile drift")
    ok(receipt["executionProfileDigest"] == proof["executionProfileDigest"] == execution_profile_digest, "lowering proof execution profile drift")
    relation = FROZEN_LOWERING_RELATION
    relation_id = digest("k-in-k/frozen-lowering-relation/v1", relation)
    ok(receipt["relationId"] == proof["relationId"] == relation_id, "lowering proof relation root drift")
    cycle = proof["cycleStates"]
    edges = {tuple(edge) for edge in relation["edges"]}
    ok(len(cycle) >= 3 and cycle[0] == cycle[-1] and len(set(cycle[:-1])) >= 2, "lowering witness is empty, nonclosing, or degenerate")
    ok(all(state in set(relation["states"]) for state in cycle) and all((left, right) in edges for left, right in zip(cycle, cycle[1:])), "lowering witness has a missing state or broken edge")
    ok(receipt["checkedResult"] == "nontermination-confirmed", "receipt verdict is not the recomputed checker result")


def validate_campaign_semantics(campaign: dict[str, Any], registry: dict[str, dict[str, dict[str, Any]]] | None = None, check_artifact_graph: bool = True, taxonomy: dict[str, Any] | None = None) -> None:
    registry = registry or mutation_package_registry()
    baseline_digest = campaign["baseline"]["definitionDigest"]
    operator = campaign["operator"]
    generation = campaign["generation"]
    reject_baseline_mismatch(campaign["failures"], "campaign failures")
    reject_baseline_mismatch(generation["failures"], "generation failures")
    for rejection in campaign["candidateRejections"]:
        reject_baseline_mismatch(rejection["failures"], "candidate rejection failures")
    for mutant in campaign["mutants"]:
        reject_baseline_mismatch(mutant["failures"], "mutant failures")
    ok(operator["digest"] in registry["operators"], "campaign operator digest does not resolve")
    operator_declaration = registry["operators"][operator["digest"]]
    validate_operator_declaration(operator_declaration)
    expected_operator = {"id": operator_declaration["operatorId"], "version": operator_declaration["operatorVersion"], "digest": operator_declaration["operatorDigest"]}
    ok(operator == expected_operator, "campaign operator does not resolve to its declaration")
    ok(generation["policy"] == operator_declaration["policy"], "campaign generation policy differs from operator declaration")
    ok(generation["candidateCap"] == operator_declaration["candidateCap"], "campaign candidate cap differs from operator declaration")
    ok(campaign["manifestDigest"] in registry["manifests"], "campaign manifest digest does not resolve")
    mutation_manifest = registry["manifests"][campaign["manifestDigest"]]
    ok(mutation_manifest["manifestId"] == digest("k-in-k/mutation-manifest/v1", value_without(mutation_manifest, "manifestId")), "mutation manifest ID derivation")
    ok(mutation_manifest["definitionDigest"] == baseline_digest and mutation_manifest["operatorDigest"] == operator["digest"], "mutation manifest baseline/operator mismatch")
    ok(mutation_manifest["artifactCatalogDigest"] in registry["catalogs"], "mutation manifest artifact catalog does not resolve")
    artifact_catalog = registry["catalogs"][mutation_manifest["artifactCatalogDigest"]]
    validate_artifact_catalog(artifact_catalog)
    lowering_evidence_keys = [(item["role"], item["digest"]) for item in mutation_manifest["loweringEvidence"]]
    ok(lowering_evidence_keys == sorted(lowering_evidence_keys) and len(lowering_evidence_keys) == len(set(lowering_evidence_keys)), "mutation manifest lowering evidence keys are duplicate or noncanonical")
    require_catalog_entries(artifact_catalog, lowering_evidence_keys, "mutation manifest lowering evidence")
    catalog_by_key = {(item["role"], item["digest"]): item for item in artifact_catalog["entries"]}
    for key in lowering_evidence_keys:
        ok(catalog_by_key[key]["availability"] == "bundled", "mutation manifest lowering evidence is not bundled")
        verify_catalog_entry_bytes(catalog_by_key[key], artifact_role_specs())
    operator_requirements = [("definition", baseline_digest), ("mutation-operator", operator["digest"]), ("mutation-module", operator_declaration["moduleDigest"]), ("mutation-selector", operator_declaration["selectorDigest"]), ("mutation-join", operator_declaration["joinDigest"]), ("precondition", operator_declaration["preconditionDigest"]), ("postcondition", operator_declaration["postconditionDigest"]), ("patch-template", operator_declaration["patchTemplateDigest"]), ("lowering-profile", mutation_manifest["loweringProfileDigest"])]
    require_catalog_entries(artifact_catalog, operator_requirements, "resolved campaign operator")
    ok(mutation_manifest["siteRegistryDigest"] in registry["siteRegistries"], "mutation manifest site registry digest does not resolve")
    site_registry = registry["siteRegistries"][mutation_manifest["siteRegistryDigest"]]
    ok(generation["siteRegistryDigest"] == mutation_manifest["siteRegistryDigest"], "campaign generation references another site registry")
    ok(site_registry["definitionDigest"] == baseline_digest and site_registry["operatorDigest"] == operator["digest"], "mutation site registry differs from manifest roots")
    validate_patch_template_interface(operator_declaration, site_registry["selector"])
    mutation_sites_by_id = {site["siteId"]: site for site in site_registry["sites"]}
    derivation = derive_policy_instances(operator_declaration, site_registry, taxonomy)
    selection_failure = derivation["selectionFailure"]
    discovery_disposition = derivation["discoveryDisposition"]
    retained_instances = derivation["retained"]
    ok(generation["derivedInstanceCount"] == len(derivation["derived"]) and generation["retainedInstanceCount"] == len(retained_instances), "campaign generation counts do not derive from policy")
    ok(generation["complete"] == derivation["complete"], "campaign generation completeness does not derive from discovery and cap")
    selection_failures = [failure for failure in generation["failures"] if consume_failure_disposition(failure, "campaign", taxonomy) == "selection-failed"]
    if selection_failure is not None:
        ok(campaign["campaignStatus"] == "selection-failed" and not generation["candidates"] and not campaign["candidateRejections"] and not campaign["mutants"] and "score" not in campaign, "selection failure published generation output")
        ok(len(selection_failures) == 1 and selection_failures[0]["classification"] == selection_failure, "selection-failed campaign lacks its derived failure")
    else:
        ok(not selection_failures and campaign["campaignStatus"] != "selection-failed", "successful policy derivation retained selection-failure evidence")
    if discovery_disposition is not None:
        ok(discovery_disposition == "incomplete-generation" and not generation["complete"], "mutation discovery consequence did not force incomplete generation")
    ok(mutation_manifest["corpusManifestDigest"] in registry["corpora"], "mutation manifest corpus digest does not resolve")
    corpus_manifest = registry["corpora"][mutation_manifest["corpusManifestDigest"]]
    ok(corpus_manifest.get("artifactCatalogDigest", mutation_manifest["artifactCatalogDigest"]) == mutation_manifest["artifactCatalogDigest"], "mutation/corpus artifact catalog mismatch")
    ok(corpus_manifest["definitionDigest"] == mutation_manifest["definitionDigest"], "mutation/corpus manifest definition mismatch")
    corpus_tests = corpus_manifest["tests"]
    if check_artifact_graph:
        validate_corpus_manifest_semantics(corpus_manifest, artifact_catalog)
        ok([(test["testId"], test["programDigest"], test["parserDigest"], test["startSymbol"], test["optionsDigest"]) for test in mutation_manifest["tests"]] == [(test["testId"], test["programDigest"], test["parserDigest"], test["startSymbol"], test["optionsDigest"]) for test in corpus_tests], "mutation test plan differs from corpus manifest")
        expected_bounds_digest = digest("k-in-k/bounds/v1", corpus_manifest["bounds"])
        for test in mutation_manifest["tests"]:
            ok(test["boundsDigest"] == expected_bounds_digest, "mutation test bounds digest differs from corpus bounds")
            invocation = {"testId": test["testId"], "programDigest": test["programDigest"], "parserDigest": test["parserDigest"], "startSymbol": test["startSymbol"], "optionsDigest": test["optionsDigest"], "bounds": corpus_manifest["bounds"], "executionMode": corpus_manifest["executionMode"], "solverProfileDigest": corpus_manifest["solverProfileDigest"], "executionProfileDigest": corpus_manifest["executionProfileDigest"], "compatibilityProfileDigest": corpus_manifest["compatibilityProfileDigest"], "observationManifestDigest": corpus_manifest["observationManifestDigest"], "patternQueries": test["patternQueries"]}
            ok(test["invocationDigest"] == digest("k-in-k/test-invocation/v1", invocation), "mutation test invocation digest is not derived from corpus inputs")
    oracle_declarations = {oracle["oracleId"]: oracle for oracle in mutation_manifest["oracles"]}
    ok(len(oracle_declarations) == len(mutation_manifest["oracles"]), "duplicate oracle declaration")
    referenced_oracles = {oracle_id for test in mutation_manifest["tests"] for oracle_id in test["oracleIds"]}
    ok(set(oracle_declarations) == referenced_oracles, "oracle declarations do not exactly cover test oracle references")
    for declaration in oracle_declarations.values():
        artifacts = {artifact["role"]: artifact for artifact in declaration["artifacts"]}
        ok(set(artifacts) == {"oracle-projection", "oracle-comparison"} and artifacts["oracle-projection"]["digest"] == declaration["projectionDigest"] and artifacts["oracle-comparison"]["digest"] == declaration["comparisonDigest"], "oracle declaration artifacts differ from projection/comparison identity")
    validate_mutation_query_roots(mutation_manifest, artifact_catalog)
    oracle_order = [oracle["oracleId"] for oracle in mutation_manifest["oracles"]]

    def validate_oracle_invocation(oracle: dict[str, Any], mutant_definition_digest: str | None = None) -> None:
        ok(oracle["oracleId"] in oracle_declarations, "oracle result references an undeclared oracle")
        declaration = oracle_declarations[oracle["oracleId"]]
        validate_oracle_against_declaration(oracle, declaration, taxonomy, registry.get("oracleValues"), registry.get("terminals"), registry.get("crashes"))
        if not check_artifact_graph:
            return
        slots = [oracle["operand"]] if "operand" in oracle else oracle["operands"]
        operand_artifacts = [slot["terminal"]["artifact"] for slot in slots if slot["terminal"] is not None]
        for slot in slots:
            if slot["terminal"] is None:
                continue
            artifact = slot["terminal"]["artifact"]
            if artifact["role"] == "pattern-result":
                ok(artifact["digest"] in registry["patterns"], "oracle pattern operand is dangling")
            elif artifact["role"] == "semantic-crash":
                ok(artifact["digest"] in registry["crashes"], "oracle semantic-crash operand is dangling")
                crash = registry["crashes"][artifact["digest"]]
                ok(crash["crashDigest"] == digest("k-in-k/semantic-crash/v1", value_without(crash, "crashDigest")), "oracle semantic-crash operand has an invalid self ID")
                ok(crash["terminalState"]["digest"] in registry["terminals"], "oracle semantic-crash terminal state is dangling")
                require_catalog_entries(artifact_catalog, [("semantic-crash", artifact["digest"])], "oracle semantic-crash operand")
                ok(crash["executionProfileDigest"] == corpus_manifest["executionProfileDigest"], "oracle semantic-crash execution profile differs from campaign execution profile")
                expected_definition = baseline_digest if slot["side"] == "baseline" else mutant_definition_digest
                ok(expected_definition is not None and execution_terminal_definition_digest(slot["terminal"], registry["terminals"], registry["crashes"]) == expected_definition, "semantic-crash oracle operand belongs to another definition side")
            else:
                require_catalog_entries(artifact_catalog, [(artifact["role"], artifact["digest"])], "oracle terminal operand")
                ok(artifact["role"] == "oracle-value" and artifact["digest"] in registry["oracleValues"], "final-result oracle value is dangling or opaque")
                expected_definition = baseline_digest if slot["side"] == "baseline" else mutant_definition_digest
                ok(expected_definition is not None and registry["oracleValues"][artifact["digest"]]["definitionDigest"] == expected_definition, "oracle value does not reference the exact operand definition")
    planned_test_ids = campaign["selectedTestIds"]
    manifest_test_ids = [test["testId"] for test in mutation_manifest["tests"]]
    ok(planned_test_ids == manifest_test_ids and len(manifest_test_ids) == len(set(manifest_test_ids)), "campaign selected tests differ from resolved manifest order")
    manifest_test_by_id = {test["testId"]: test for test in mutation_manifest["tests"]}
    ok(len(planned_test_ids) == len(set(planned_test_ids)), "duplicate selected test ID")
    ok(all(failure["scope"] == "campaign" for failure in campaign["failures"]), "top-level failure has non-campaign scope")
    campaign_payload = {"manifestDigest": campaign["manifestDigest"], "operator": operator, "scheduleMode": campaign["scheduleMode"]}
    ok(campaign["campaignId"] == digest("k-in-k/mutation-campaign/v1", campaign_payload), "mutation campaign ID derivation")
    candidate_by_id: dict[str, dict[str, Any]] = {}
    patch_by_id: dict[str, dict[str, Any]] = {}
    instance_ids: set[str] = set()
    instance_count = 0
    reported_selection_keys: list[str] = []
    retained_keys = [canonical(instance) for instance in retained_instances]
    retained_rank = {key: index for index, key in enumerate(retained_keys)}
    ok(len(retained_rank) == len(retained_keys), "policy derivation produced duplicate instances")
    for candidate in generation["candidates"]:
        expected_origins = sorted(candidate["originInstances"], key=lambda origin: (retained_rank.get(canonical({"siteTuple": origin["siteTuple"], "discoveryTuples": origin["discoveryTuples"]}), len(retained_rank)), origin["instanceId"]))
        ok(candidate["originInstances"] == expected_origins, "candidate origins are not in derived instance order")
    expected_candidates = sorted(generation["candidates"], key=lambda candidate: (min(retained_rank.get(canonical({"siteTuple": origin["siteTuple"], "discoveryTuples": origin["discoveryTuples"]}), len(retained_rank)) for origin in candidate["originInstances"]), candidate["candidateId"]))
    ok(generation["candidates"] == expected_candidates, "mutation candidates are not ordered by first derived origin")
    if check_artifact_graph:
        ok(baseline_digest in registry["definitions"], "campaign baseline definition is unavailable")
        baseline_definition = registry["definitions"][baseline_digest]
        validate_mutation_site_registry(site_registry, baseline_definition, operator_declaration)
    for candidate in generation["candidates"]:
        candidate_id = candidate["candidateId"]
        ok(candidate_id not in candidate_by_id, "duplicate candidate ID")
        candidate_by_id[candidate_id] = candidate
        patch = candidate["patch"]
        ok(patch["operatorId"] == operator["id"] and patch["operatorVersion"] == operator["version"], "patch/operator mismatch")
        edits = patch["edits"]
        for edit in edits:
            ok(edit["editId"] == digest("k-in-k/edit/v1", value_without(edit, "editId")), "campaign edit ID derivation")
        edit_order = sorted(edits, key=lambda edit: (edit["targetLineage"] or "", canonical(edit["targetPath"]), edit["operation"], edit["editId"]))
        ok(edits == edit_order, "patch edits are not canonical")
        patch_payload = {"schemaVersion": patch["schemaVersion"], "edits": edits}
        ok(patch["patchId"] == digest("k-in-k/patch/v1", patch_payload), "campaign patch ID derivation")
        ok(patch["patchId"] not in patch_by_id, "duplicate candidate patch was not deduplicated")
        patch_by_id[patch["patchId"]] = patch
        candidate_payload = {"operatorId": operator["id"], "operatorVersion": operator["version"], "baselineDefinitionDigest": baseline_digest, "patchId": patch["patchId"]}
        ok(candidate_id == digest("k-in-k/candidate/v1", candidate_payload), "candidate ID derivation")
        for origin in candidate["originInstances"]:
            site_tuple = origin["siteTuple"]
            selection_key = canonical({"siteTuple": site_tuple, "discoveryTuples": origin["discoveryTuples"]})
            ok(selection_key in retained_rank, "mutation origin is not in the retained policy-derived prefix")
            ok(len(site_tuple) == len(set(site_tuple)) and set(site_tuple) <= set(mutation_sites_by_id), "mutation aggregate/site tuple is duplicate or dangling")
            for discovery_tuple in origin["discoveryTuples"]:
                tuple_sites = discovery_tuple["siteTuple"]
                ok(tuple_sites in site_registry["tuples"], "mutation origin cites a non-discovered tuple")
                ok(discovery_tuple["bindings"] == canonical_discovery_bindings(tuple_sites, mutation_sites_by_id), "mutation origin bindings differ from discovery evidence")
            validate_edit_receipts(operator, operator_declaration, origin, edits, mutation_sites_by_id)
            instance_count += 1
            ok(origin["instanceId"] not in instance_ids, "duplicate instance ID")
            instance_ids.add(origin["instanceId"])
            reported_selection_keys.append(selection_key)
            instance_payload = mutation_instance_payload(operator, baseline_digest, generation["policy"], origin, patch["patchId"])
            ok(origin["instanceId"] == digest("k-in-k/instance/v1", instance_payload), "instance ID derivation")

    ok(len(reported_selection_keys) == len(set(reported_selection_keys)), "campaign reports one derived instance more than once")
    ok(sorted(reported_selection_keys, key=retained_rank.__getitem__) == retained_keys, "campaign origins omit or substitute the retained policy-derived prefix")

    mutant_ids: set[str] = set()
    mutant_candidate_ids: set[str] = set()
    candidate_order = {candidate["candidateId"]: index for index, candidate in enumerate(generation["candidates"])}
    ok(campaign["mutants"] == sorted(campaign["mutants"], key=lambda mutant: (candidate_order.get(mutant["candidateId"], len(candidate_order)), mutant["mutantId"])), "mutants are not in canonical candidate order")
    for mutant in campaign["mutants"]:
        ok(mutant["mutantId"] not in mutant_ids, "duplicate mutant ID")
        mutant_ids.add(mutant["mutantId"])
        ok(mutant["candidateId"] in candidate_by_id, "mutant references missing candidate")
        ok(mutant["candidateId"] not in mutant_candidate_ids, "candidate produced more than one mutant")
        mutant_candidate_ids.add(mutant["candidateId"])
        candidate = candidate_by_id[mutant["candidateId"]]
        ok(mutant["artifacts"] == sorted(mutant["artifacts"], key=lambda artifact: (artifact["role"], artifact["digest"])), "mutant artifacts are not in canonical role/digest order")
        ok(mutant["bounds"] == corpus_manifest["bounds"], "mutant/replay bounds differ from the corpus invocation bounds")
        patch = candidate["patch"]
        ok(mutant["patchId"] == patch["patchId"], "mutant patch reference mismatch")
        mutant_payload = {"baselineDefinitionDigest": baseline_digest, "patchId": mutant["patchId"]}
        ok(mutant["mutantId"] == digest("k-in-k/mutant/v1", mutant_payload), "mutant ID derivation")
        ok(mutant["appliedEditCount"] == len(patch["edits"]), "mutant applied-edit count mismatch")
        diff_value = mutant["diff"]
        ok(diff_value["diffId"] == digest("k-in-k/structural-diff/v1", value_without(diff_value, "diffId")), "mutant diff ID derivation")
        ok(diff_value["baselineDefinitionDigest"] == baseline_digest, "mutant diff baseline mismatch")
        ok(diff_value["mutantDefinitionDigest"] == mutant["outputDefinitionDigest"], "mutant diff output mismatch")
        ok([entry["editId"] for entry in diff_value["entries"]] == [edit["editId"] for edit in patch["edits"]], "diff/edit correspondence mismatch")
        oracle_by_id = {item["oracleId"]: item for item in mutant["oracleResults"]}
        ok(len(oracle_by_id) == len(mutant["oracleResults"]), "duplicate mutant oracle result")
        ok([item["oracleId"] for item in mutant["oracleResults"]] == oracle_order, "mutant oracle results are not in manifest declaration order")
        for oracle in mutant["oracleResults"]:
            validate_oracle_invocation(oracle, mutant["outputDefinitionDigest"])
        test_ids = [test["id"] for test in mutant["tests"]]
        ok(len(test_ids) == len(set(test_ids)), "duplicate mutant test ID")
        ok(test_ids == planned_test_ids, "mutant tests differ from selected-test manifest order")
        for test in mutant["tests"]:
            ok(set(test["oracleIds"]) <= set(oracle_by_id), "test references missing oracle")
            manifest_test = manifest_test_by_id[test["id"]]
            ok((test["boundsDigest"], test["invocationDigest"], test["oracleIds"]) == (manifest_test["boundsDigest"], manifest_test["invocationDigest"], manifest_test["oracleIds"]), "mutant test metadata differs from resolved manifest")
            linked_outcomes = [oracle_by_id[oracle_id]["outcome"] for oracle_id in test["oracleIds"]]
            ok(test["selected"] == (test["status"] != "skipped"), "test selection/status mismatch")
            if test["status"] == "agree":
                ok(all(outcome == "agree" for outcome in linked_outcomes), "agree test has a non-agreeing oracle")
            elif test["status"] == "kill":
                ok("distinguish" in linked_outcomes, "kill test does not reference a distinguishing oracle")
            elif test["status"] in ("timeout", "unknown", "error"):
                compatible = {"timeout": {"timeout"}, "unknown": {"unknown"}, "error": {"error", "incomparable"}}[test["status"]]
                ok(any(outcome in compatible for outcome in linked_outcomes), f"{test['status']} test lacks a corresponding oracle")
        if campaign["scheduleMode"] == "full":
            ok(all(test["selected"] for test in mutant["tests"]), "full schedule skipped a selected test")
        else:
            kill_indices = [index for index, test in enumerate(mutant["tests"]) if test["status"] == "kill"]
            stop = kill_indices[0] if kill_indices else len(mutant["tests"])
            ok(all(test["selected"] for test in mutant["tests"][:stop + (1 if kill_indices else 0)]), "first-kill schedule skipped before its first kill")
            ok(all(not test["selected"] and test["status"] == "skipped" for test in mutant["tests"][stop + 1:]), "first-kill suffix was not skipped")
        outcomes = [item["outcome"] for item in mutant["oracleResults"]]
        all_failures = mutant["failures"] + [item["failure"]["failure"] for item in mutant["oracleResults"] if item["failure"] is not None]
        for failure in all_failures:
            if failure["classification"] == "lowering-nontermination":
                authorize_lowering_nontermination(failure, {"role": "mutant", "baselineDefinitionDigest": baseline_digest, "mutantId": mutant["mutantId"], "mutantDefinitionDigest": mutant["outputDefinitionDigest"]}, mutation_manifest["loweringProfileDigest"], corpus_manifest["executionProfileDigest"], mutation_manifest, artifact_catalog)
        failure_dispositions = [(failure, consume_failure_disposition(failure, "campaign", taxonomy)) for failure in all_failures]
        status = mutant["status"]
        if status == "killed":
            ok(mutant["validation"]["outcome"] == "valid", "killed mutant failed validation")
            ok("distinguish" in outcomes, "killed mutant has no distinguishing oracle")
            ok(any(test["status"] == "kill" and any(oracle_by_id[oracle_id]["outcome"] == "distinguish" for oracle_id in test["oracleIds"]) for test in mutant["tests"]), "killed mutant has no linked killing test")
        elif status == "survived":
            ok(mutant["validation"]["outcome"] == "valid", "survived mutant failed validation")
            ok(outcomes and all(outcome == "agree" for outcome in outcomes), "survived mutant has incomplete/disagreeing oracle")
            ok(all(test["selected"] and test["status"] == "agree" for test in mutant["tests"]), "survived mutant did not execute and agree on every selected test")
        elif status == "invalid":
            ok(mutant["validation"]["outcome"] == "invalid", "invalid mutant has valid validation outcome")
            ok(any(disposition == "invalid" for _, disposition in failure_dispositions), "invalid mutant lacks an invalid taxonomy disposition")
            ok(any(failure["stage"] == mutant["validation"]["closestStage"] and disposition == "invalid" for failure, disposition in failure_dispositions), "invalid mutant closest stage differs from its invalidating failure")
        elif status == "timeout":
            ok(mutant["validation"]["outcome"] == "valid" and any(disposition == "timeout" for _, disposition in failure_dispositions), "timeout mutant lacks a timeout taxonomy disposition after validation")
            ok(any(failure["stage"] == mutant["validation"]["closestStage"] and disposition == "timeout" for failure, disposition in failure_dispositions), "timeout mutant closest stage differs from its timeout failure")
        elif status == "unknown":
            ok(mutant["validation"]["outcome"] == "valid" and any(disposition == "unknown" for _, disposition in failure_dispositions), "unknown mutant lacks an unknown taxonomy disposition after validation")
            ok(any(failure["stage"] == mutant["validation"]["closestStage"] and disposition == "unknown" for failure, disposition in failure_dispositions), "unknown mutant closest stage differs from its unknown failure")
        elif status == "error":
            ok(any(disposition == "error" for _, disposition in failure_dispositions), "error mutant lacks an error taxonomy disposition")
        else:
            raise AssertionError(f"unsupported mutant status {status}")

    no_change_candidate_ids: set[str] = set()
    rejection_keys: set[tuple[str, str, tuple[str, ...]]] = set()
    rejection_status_order = {"duplicate": 0, "no-change": 1}
    patch_candidate_order = {candidate["patch"]["patchId"]: index for index, candidate in enumerate(generation["candidates"])}
    ok(campaign["candidateRejections"] == sorted(campaign["candidateRejections"], key=lambda rejection: (patch_candidate_order.get(rejection["patchId"], len(patch_candidate_order)), rejection_status_order[rejection["status"]], tuple(rejection["originInstanceIds"]))), "candidate rejections are not in candidate order")
    for rejection in campaign["candidateRejections"]:
        patch_id = rejection["patchId"]
        ok(patch_id in patch_by_id, "candidate rejection references missing patch")
        candidate = next(item for item in generation["candidates"] if item["patch"]["patchId"] == patch_id)
        candidate_origins = {origin["instanceId"] for origin in candidate["originInstances"]}
        origin_ids = rejection["originInstanceIds"]
        ok(len(origin_ids) == len(set(origin_ids)) and set(origin_ids) <= candidate_origins, "candidate rejection has missing/duplicate origins")
        key = (rejection["status"], patch_id, tuple(origin_ids))
        ok(key not in rejection_keys, "duplicate candidate rejection record")
        rejection_keys.add(key)
        classifications = {failure["classification"] for failure in rejection["failures"]}
        ok(bool(rejection["failures"]) and all(consume_failure_disposition(failure, "campaign", taxonomy) == "rejected" for failure in rejection["failures"]), "candidate rejection lacks an exact rejected taxonomy disposition")
        if rejection["status"] == "no-change":
            ok(classifications == {"no-change"}, "no-change rejection has another failure")
            no_change_candidate_ids.add(candidate["candidateId"])
        else:
            ok("duplicate-site" in classifications or "duplicate-target" in classifications, "duplicate rejection lacks duplicate failure")
            ok(candidate["candidateId"] in mutant_candidate_ids or campaign["baseline"]["status"] != "valid" or not generation["complete"], "duplicate-only candidate lost its retained mutant")

    ok(not (mutant_candidate_ids & no_change_candidate_ids), "no-change candidate produced a mutant")

    has_score = "score" in campaign
    baseline = campaign["baseline"]
    baseline_oracle_by_id = {item["oracleId"]: item for item in baseline["oracleResults"]}
    ok(len(baseline_oracle_by_id) == len(baseline["oracleResults"]), "duplicate baseline oracle result")
    ok([item["oracleId"] for item in baseline["oracleResults"]] == ([] if baseline["status"] == "baseline-invalid" else oracle_order), "baseline oracle results are not in manifest declaration order/abort state")
    for oracle in baseline["oracleResults"]:
        validate_oracle_invocation(oracle)
    baseline_mismatches = [failure for failure in baseline["failures"] if failure["classification"] == "baseline-mismatch"]
    mismatch_oracles = [oracle for oracle in baseline["oracleResults"] if oracle["failure"] is not None and oracle["failure"]["failure"]["classification"] == "baseline-mismatch"]
    if baseline_mismatches or mismatch_oracles:
        ok(baseline["status"] == "baseline-oracle-failed" and len(baseline_mismatches) == len(mismatch_oracles) > 0, "baseline-mismatch is not confined to a matched baseline-oracle gate disposition")
    baseline_test_ids = [test["id"] for test in baseline["tests"]]
    expected_baseline_test_ids = [] if baseline["status"] == "baseline-invalid" else planned_test_ids
    ok(baseline_test_ids == expected_baseline_test_ids, "baseline tests differ from resolved manifest order/abort state")
    ok([test["oracleIds"] for test in baseline["tests"]] == [manifest_test_by_id[test_id]["oracleIds"] for test_id in expected_baseline_test_ids], "baseline oracle coverage differs from resolved manifest")
    expected_baseline_oracles = set() if baseline["status"] == "baseline-invalid" else {oracle_id for test in mutation_manifest["tests"] for oracle_id in test["oracleIds"]}
    ok(set(baseline_oracle_by_id) == expected_baseline_oracles, "baseline oracle results do not exactly cover the manifest/abort state")
    for test in baseline["tests"]:
        linked = [baseline_oracle_by_id[oracle_id]["outcome"] for oracle_id in test["oracleIds"]]
        if test["status"] == "agree":
            ok(all(outcome == "accepted" for outcome in linked), "agreeing baseline test has a non-accepted oracle")
        elif test["status"] == "skipped":
            ok(all(outcome == "skipped" for outcome in linked), "skipped baseline test retained an oracle result")
    if baseline["status"] == "valid":
        ok(not baseline["failures"] and all(test["status"] == "agree" for test in baseline["tests"]) and all(item["outcome"] == "accepted" for item in baseline["oracleResults"]), "valid baseline lacks complete accepted oracle evidence")
    elif baseline["status"] == "baseline-invalid":
        for failure in baseline["failures"]:
            if failure["classification"] == "lowering-nontermination":
                authorize_lowering_nontermination(failure, {"role": "baseline", "definitionDigest": baseline_digest}, mutation_manifest["loweringProfileDigest"], corpus_manifest["executionProfileDigest"], mutation_manifest, artifact_catalog)
        ok(bool(baseline["failures"]) and not baseline["tests"] and not baseline["oracleResults"] and all(consume_failure_disposition(failure, "campaign", taxonomy) == "baseline-invalid" for failure in baseline["failures"]), "baseline-invalid did not abort before tests/oracles or differs from its taxonomy consequence")
    else:
        ok(bool(baseline["failures"]) and any(test["status"] != "agree" for test in baseline["tests"]) and any(oracle["outcome"] != "accepted" for oracle in baseline["oracleResults"]) and all(consume_failure_disposition(failure, "campaign", taxonomy) == "baseline-oracle-failed" for failure in baseline["failures"]), "baseline-oracle-failed lacks linked rejected test/oracle evidence or differs from its taxonomy consequence")
    if campaign["baseline"]["status"] != "valid":
        ok(campaign["campaignStatus"] == campaign["baseline"]["status"] and not has_score and not campaign["mutants"], "invalid baseline campaign was executed/scored")
    elif selection_failure is not None:
        ok(campaign["campaignStatus"] == "selection-failed" and not has_score, "terminal selection failure was misclassified or scored")
    elif not generation["complete"]:
        ok(campaign["campaignStatus"] == "incomplete-generation" and not has_score, "incomplete generation was scored")
        ok(any(consume_failure_disposition(failure, "campaign", taxonomy) == "incomplete-generation" for failure in generation["failures"]), "incomplete generation lacks its taxonomy disposition")
    elif campaign["campaignStatus"] == "complete":
        ok(has_score and not campaign["failures"], "complete campaign lacks score or retains campaign failures")
        ok(mutant_candidate_ids | no_change_candidate_ids == set(candidate_by_id), f"complete campaign omitted a candidate disposition: mutants={sorted(mutant_candidate_ids)} no-change={sorted(no_change_candidate_ids)} candidates={sorted(candidate_by_id)}")
    elif campaign["campaignStatus"] == "error":
        ok(not has_score and not campaign["mutants"] and bool(campaign["failures"]) and all(consume_failure_disposition(failure, "campaign", taxonomy) == "error" for failure in campaign["failures"]), "error campaign retained results or lacks an error taxonomy disposition")
    if has_score:
        score = campaign["score"]
        statuses = [mutant["status"] for mutant in campaign["mutants"]]
        killed, survived = statuses.count("killed"), statuses.count("survived")
        expected_excluded = {key: statuses.count(key) for key in ("invalid", "timeout", "unknown", "error")}
        rejection_statuses = [item["status"] for item in campaign["candidateRejections"]]
        expected_excluded.update({"duplicate": rejection_statuses.count("duplicate"), "no-change": rejection_statuses.count("no-change")})
        ok(score["killed"] == killed and score["survived"] == survived, "score status counts mismatch")
        ok(score["denominator"] == killed + survived, "score denominator mismatch")
        ok(score["excluded"] == expected_excluded, "score exclusions mismatch")
        if killed + survived == 0:
            ok(score["ratio"] is None, "zero-denominator score has a ratio")
        else:
            divisor = math.gcd(killed, killed + survived)
            expected_ratio = {"numerator": killed // divisor, "denominator": (killed + survived) // divisor}
            ok(score["ratio"] == expected_ratio, "score ratio is not exact and reduced")

    for mutant in campaign["mutants"] if check_artifact_graph else []:
        candidate = candidate_by_id[mutant["candidateId"]]
        patch = candidate["patch"]
        ok(baseline_digest in registry["definitions"], "campaign baseline definition is unavailable")
        derived_definition, derived_diff, patch_failure = apply_portable_patch(registry["definitions"][baseline_digest], patch)
        ok(patch_failure is None and derived_definition is not None and derived_diff is not None, "campaign mutant patch does not apply portably")
        ok(derived_definition["definitionDigest"] == mutant["outputDefinitionDigest"], "mutant output definition digest is not derived from its patch")
        ok(derived_diff == mutant["diff"], "mutant structural diff differs from portable patch derivation")
        ok(mutant["replayManifestDigest"] in registry["replays"], "mutant replay digest is dangling")
        mutation_replay = registry["replays"][mutant["replayManifestDigest"]]
        ok(mutation_replay["kind"] == "mutation-materialization", "mutant replay does not resolve to a materialization replay")
        ok(mutation_replay["definitionDigest"] == baseline_digest, "mutation replay definition differs from campaign baseline")
        replay_mutation = mutation_replay["mutation"]
        ok(replay_mutation == {"operatorDigest": operator["digest"], "candidateId": mutant["candidateId"], "patchId": mutant["patchId"], "mutantId": mutant["mutantId"], "outputDefinitionDigest": mutant["outputDefinitionDigest"]}, "mutation replay identity graph mismatch")
        replay_diff_artifacts = [artifact for artifact in mutation_replay["artifacts"] if artifact["role"] == "structural-diff"]
        ok(len(replay_diff_artifacts) == 1 and replay_diff_artifacts[0]["digest"] == mutant["diff"]["diffId"] and registry["diffs"].get(mutant["diff"]["diffId"]) == mutant["diff"], "mutation replay structural diff differs from campaign evidence")
        ok(mutation_replay["bounds"] == mutant["bounds"], "mutation replay bounds differ from mutant report")
        replay_diff_artifacts = [artifact for artifact in mutation_replay["artifacts"] if artifact["role"] == "structural-diff"]
        ok(len(replay_diff_artifacts) == 1 and replay_diff_artifacts[0]["digest"] == mutant["diff"]["diffId"], "mutation replay structural diff differs from mutant report")
        ok(mutant["diff"]["diffId"] in registry["diffs"] and mutant["diff"] == registry["diffs"][mutant["diff"]["diffId"]], "mutant structural diff does not resolve to its artifact")
        diff_artifacts = [artifact for artifact in mutant["artifacts"] if artifact["role"] == "structural-diff"]
        ok(len(diff_artifacts) == 1 and diff_artifacts[0]["digest"] == mutant["diff"]["diffId"], "structural-diff artifact digest mismatch")
        edits_by_id = {edit["editId"]: edit for edit in patch["edits"]}
        for entry in mutant["diff"]["entries"]:
            edit = edits_by_id[entry["editId"]]
            ok((entry["operation"], entry["targetLineage"], entry["targetPath"]) == (edit["operation"], edit["targetLineage"], edit["targetPath"]), "diff operation/path differs from patch")
            ok(entry["affectedProvenance"]["lineageId"] == edit["targetLineage"] and entry["affectedProvenance"]["contentFingerprint"] == edit["expectedContent"], "diff provenance differs from patch precondition")
        for oracle in mutant["oracleResults"]:
            baseline_value = oracle_operand_digest(oracle, 0)
            mutant_value = oracle_operand_digest(oracle, 1)
            normal_final_operands = oracle["kind"] == "final-result" and "operands" in oracle and all(slot["terminal"] is not None and slot["terminal"]["kind"] == "normal" for slot in oracle["operands"])
            if normal_final_operands and oracle["outcome"] == "agree" and baseline_value is not None:
                ok(baseline_value in registry["oracleValues"] and mutant_value in registry["oracleValues"] and registry["oracleValues"][baseline_value]["value"] == registry["oracleValues"][mutant_value]["value"], "agreeing final-result oracle values differ")
            if oracle["kind"] == "execution-pattern" and oracle["outcome"] in ("agree", "distinguish"):
                ok(baseline_value in registry["patterns"] and mutant_value in registry["patterns"], "pattern oracle value digest is dangling")
                baseline_pattern = registry["patterns"][baseline_value]
                mutant_pattern = registry["patterns"][mutant_value]
                ok(baseline_pattern["inputs"]["definitionDigest"] == baseline_digest and mutant_pattern["inputs"]["definitionDigest"] == mutant["outputDefinitionDigest"], "pattern oracle result definition mismatch")
                ok(baseline_pattern["testId"] == mutant_pattern["testId"] and baseline_pattern["queryId"] == mutant_pattern["queryId"], "pattern oracle compared different test/query identities")
                projections_equal = pattern_oracle_projection(baseline_pattern) == pattern_oracle_projection(mutant_pattern)
                ok(projections_equal == (oracle["outcome"] == "agree"), "pattern oracle outcome differs from normalized comparison projection")
            if oracle["witnessDigest"] is not None:
                ok(oracle["kind"] == "execution-pattern" and oracle["witnessDigest"] in registry["patterns"], "oracle witness digest is dangling")
                witness_result = registry["patterns"][oracle["witnessDigest"]]
                ok(witness_result["outcome"] == "match" and oracle["witnessDigest"] in (baseline_value, mutant_value), "oracle witness does not identify a compared matching result")
    report_payload = value_without(campaign, "reportId")
    ok(campaign["reportId"] == digest("k-in-k/mutation-report/v1", report_payload), "mutation report ID derivation")


def refresh_campaign_ids(campaign: dict[str, Any]) -> None:
    campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
    campaign["reportId"] = digest("k-in-k/mutation-report/v1", value_without(campaign, "reportId"))


def verify_bag10_acceptance_repairs() -> None:
    base = load(FIXTURES / "mutation-campaign.json")
    campaign = deepcopy(base)
    proof_data = load(VECTORS / "lowering-proof-vectors.json")
    failure = deepcopy(proof_data["authorizedFailure"])
    mutant = campaign["mutants"][0]
    mutant.update({"status": "invalid", "validation": {"outcome": "invalid", "closestStage": "lowering"}, "failures": [failure]})
    for test in mutant["tests"]:
        test["status"] = "invalid"
    for oracle in mutant["oracleResults"]:
        oracle.update({"outcome": "skipped", "operands": [{"side": "baseline", "terminal": None}, {"side": "mutant", "terminal": None}], "witnessDigest": None, "failure": None})
    campaign["score"] = {"killed": 0, "survived": 0, "denominator": 0, "ratio": None, "excluded": {"invalid": 1, "timeout": 0, "unknown": 0, "error": 0, "duplicate": 0, "no-change": 0}}
    refresh_campaign_ids(campaign)
    registry = mutation_package_registry()
    schema_path = SCHEMAS / "mutation-campaign.schema.json"
    schema = load(schema_path)
    validate_schema(campaign, schema, schema_path, schema)
    validate_campaign_semantics(campaign, registry=registry, check_artifact_graph=False)

    def changed_manifest(mutator: Any) -> tuple[dict[str, Any], dict[str, dict[str, dict[str, Any]]]]:
        altered_campaign = deepcopy(campaign)
        altered_registry = deepcopy(registry)
        manifest = deepcopy(altered_registry["manifests"][altered_campaign["manifestDigest"]])
        mutator(manifest, altered_registry)
        manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", value_without(manifest, "manifestId"))
        altered_registry["manifests"] = {manifest["manifestId"]: manifest}
        altered_campaign["manifestDigest"] = manifest["manifestId"]
        refresh_campaign_ids(altered_campaign)
        return altered_campaign, altered_registry

    for role, label in (("lowering-proof-check-receipt", "receipt"), ("lowering-cycle-proof", "proof")):
        altered_campaign, altered_registry = changed_manifest(lambda manifest, _registry, role=role: manifest.__setitem__("loweringEvidence", [item for item in manifest["loweringEvidence"] if item["role"] != role]))
        expect_semantic_rejection(lambda value: validate_campaign_semantics(value, registry=altered_registry, check_artifact_graph=False), altered_campaign, f"manifest omitted required lowering {label}")

    def remove_receipt_from_catalog(manifest: dict[str, Any], altered_registry: dict[str, Any]) -> None:
        catalog = deepcopy(next(iter(altered_registry["catalogs"].values())))
        receipt_key = tuple(failure["semanticEvidence"][0].values())
        catalog["entries"] = [entry for entry in catalog["entries"] if (entry["role"], entry["digest"]) != receipt_key]
        catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(catalog, "catalogId"))
        altered_registry["catalogs"] = {catalog["catalogId"]: catalog}
        manifest["artifactCatalogDigest"] = catalog["catalogId"]
    altered_campaign, altered_registry = changed_manifest(remove_receipt_from_catalog)
    expect_semantic_rejection(lambda value: validate_campaign_semantics(value, registry=altered_registry, check_artifact_graph=False), altered_campaign, "catalog omitted referenced lowering receipt")

    baseline_case = next(item for item in proof_data["cases"] if item["subjectRole"] == "baseline")
    def select_baseline_receipt(manifest: dict[str, Any], _registry: dict[str, Any]) -> None:
        manifest["loweringEvidence"] = [deepcopy(baseline_case["proofKey"]), deepcopy(baseline_case["receiptKey"])]
    altered_campaign, altered_registry = changed_manifest(select_baseline_receipt)
    altered_campaign["mutants"][0]["failures"][0]["semanticEvidence"] = [deepcopy(baseline_case["receiptKey"])]
    refresh_campaign_ids(altered_campaign)
    expect_semantic_rejection(lambda value: validate_campaign_semantics(value, registry=altered_registry, check_artifact_graph=False), altered_campaign, "mutant failure accepted baseline receipt/proof-key path")

    manifest = registry["manifests"][campaign["manifestDigest"]]
    catalog = registry["catalogs"][manifest["artifactCatalogDigest"]]
    mutant_subject = {"role": "mutant", "baselineDefinitionDigest": campaign["baseline"]["definitionDigest"], "mutantId": mutant["mutantId"], "mutantDefinitionDigest": mutant["outputDefinitionDigest"]}
    reversed_subject = {"role": "baseline", "definitionDigest": campaign["baseline"]["definitionDigest"]}
    expect_semantic_rejection(lambda value: authorize_lowering_nontermination(value, reversed_subject, manifest["loweringProfileDigest"], load(FIXTURES / "corpus-manifest.json")["executionProfileDigest"], manifest, catalog), failure, "campaign catalog authorized subject reversal")
    drifted_subject = deepcopy(mutant_subject)
    drifted_subject["mutantDefinitionDigest"] = "d" * 64
    expect_semantic_rejection(lambda value: authorize_lowering_nontermination(value, drifted_subject, manifest["loweringProfileDigest"], load(FIXTURES / "corpus-manifest.json")["executionProfileDigest"], manifest, catalog), failure, "campaign catalog authorized mutant-definition drift")
    expect_semantic_rejection(lambda value: authorize_lowering_nontermination(value, mutant_subject, manifest["loweringProfileDigest"], "e" * 64, manifest, catalog), failure, "campaign catalog authorized execution-profile drift")

    missing_report_evidence = deepcopy(campaign)
    missing_report_evidence["mutants"][0]["failures"][0]["semanticEvidence"] = []
    refresh_campaign_ids(missing_report_evidence)
    expect_schema_rejection(missing_report_evidence, "mutation-campaign.schema.json", "report omitted required lowering receipt")
    wrong_role_report = deepcopy(campaign)
    wrong_role_report["mutants"][0]["failures"][0]["semanticEvidence"][0]["role"] = "lowering-cycle-proof"
    refresh_campaign_ids(wrong_role_report)
    expect_schema_rejection(wrong_role_report, "mutation-campaign.schema.json", "report used a proof key where a receipt key was required")

    detailed = deepcopy(campaign)
    detailed_failure = detailed["mutants"][0]["failures"][0]
    detailed_failure["details"] = {"claimedClassification": "time-limit", "claimedRetryability": "same-input-after-resource-change", "claimedStatus": "timeout", "claimedExcluded": "timeout"}
    refresh_campaign_ids(detailed)
    validate_campaign_semantics(detailed, registry=registry, check_artifact_graph=False)
    expect_semantic_rejection(lambda value: ok(value["details"]["claimedClassification"] == value["classification"], "details changed classification"), detailed_failure, "details-only classification change was accepted")
    expect_semantic_rejection(lambda value: ok(value["details"]["claimedRetryability"] == value["retryability"], "details changed retryability"), detailed_failure, "details-only retryability change was accepted")
    bad_status = deepcopy(detailed)
    bad_status["mutants"][0]["status"] = "timeout"
    refresh_campaign_ids(bad_status)
    expect_semantic_rejection(lambda value: validate_campaign_semantics(value, registry=registry, check_artifact_graph=False), bad_status, "details-only status change was accepted")
    bad_score = deepcopy(detailed)
    bad_score["score"]["excluded"].update({"invalid": 0, "timeout": 1})
    refresh_campaign_ids(bad_score)
    expect_semantic_rejection(lambda value: validate_campaign_semantics(value, registry=registry, check_artifact_graph=False), bad_score, "details-only score change was accepted")

    altered_taxonomy = deepcopy(load(PACKAGE / "failure-taxonomy.json"))
    depth_entry = next(entry for entry in altered_taxonomy["entries"] if (entry["stage"], entry["classification"]) == ("execution", "depth-limit"))
    depth_path = next(placement for placement in depth_entry["placements"] if (placement["context"], placement["scope"]) == ("pattern-path", "path"))
    depth_path["consequence"]["disposition"] = "error"
    altered_taxonomy["taxonomyId"] = digest("k-in-k/failure-taxonomy/v1", value_without(altered_taxonomy, "taxonomyId"))
    taxonomy_material = canonical(altered_taxonomy).encode("utf-8")
    altered_catalog = deepcopy(catalog)
    taxonomy_entry = next(entry for entry in altered_catalog["entries"] if entry["role"] == "failure-taxonomy")
    taxonomy_entry.update({"digest": altered_taxonomy["taxonomyId"], "contentSha256": hashlib.sha256(taxonomy_material).hexdigest()})
    altered_catalog["entries"].sort(key=lambda entry: (entry["role"], entry["digest"]))
    altered_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(altered_catalog, "catalogId"))
    altered_corpus = deepcopy(registry["corpora"][manifest["corpusManifestDigest"]])
    altered_corpus["artifactCatalogDigest"] = altered_catalog["catalogId"]
    altered_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(altered_corpus, "manifestId"))
    altered_manifest = deepcopy(manifest)
    altered_manifest.update({"artifactCatalogDigest": altered_catalog["catalogId"], "corpusManifestDigest": altered_corpus["manifestId"]})
    altered_manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", value_without(altered_manifest, "manifestId"))
    altered_report = deepcopy(campaign)
    altered_report["manifestDigest"] = altered_manifest["manifestId"]
    refresh_campaign_ids(altered_report)
    original_roots = (load(PACKAGE / "failure-taxonomy.json")["taxonomyId"], catalog["catalogId"], manifest["corpusManifestDigest"], manifest["manifestId"], campaign["campaignId"], campaign["reportId"])
    altered_roots = (altered_taxonomy["taxonomyId"], altered_catalog["catalogId"], altered_corpus["manifestId"], altered_manifest["manifestId"], altered_report["campaignId"], altered_report["reportId"])
    ok(all(altered != original for altered, original in zip(altered_roots, original_roots)), "taxonomy consequence drift did not refresh every taxonomy/catalog/corpus/manifest/campaign/report root")
    ok(taxonomy_entry["contentSha256"] == hashlib.sha256(taxonomy_material).hexdigest(), "altered taxonomy catalog entry does not bind the refreshed in-memory material")
    stale_pattern = load(FIXTURES / "write-only-pattern-result.json")
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, taxonomy=altered_taxonomy), stale_pattern, "stale unknown pattern result survived a refreshed taxonomy error consequence")

    observation_error = deepcopy(load(FIXTURES / "observation-installation-result.json"))
    observation_error.update({"status": "error", "outputDefinitionDigest": None, "appliedSelectionCount": 0, "installedSelectionIds": [], "failures": [{"stage": "observation", "classification": "malformed-event", "context": "observation-installation", "scope": "test", "retryability": "never", "semanticEvidence": [], "details": {}}]})
    observation_error["resultId"] = digest("k-in-k/observation-installation-result/v1", value_without(observation_error, "resultId"))
    validate_observation_installation_semantics(observation_error)
    observation_drift = taxonomy_with_disposition("observation", "malformed-event", "observation-installation", "test", "unknown")
    expect_semantic_rejection(lambda value: validate_observation_installation_semantics(value, observation_drift), observation_error, "observation installation accepted stale error after refreshed consequence drift")

    policy_case = next(case for case in load(FIXTURES / "mutation-policy-cases.json")["cases"] if case["id"] == "nonexhaustive-prefix")
    validate_policy_registry_shape(policy_case["siteRegistry"])
    discovery_drift = taxonomy_with_disposition("selection", "incomplete-generation", "mutation-discovery", "campaign", "error")
    expect_semantic_rejection(lambda value: validate_policy_registry_shape(value, discovery_drift), policy_case["siteRegistry"], "mutation discovery accepted stale incomplete-generation after refreshed consequence drift")
    expect_semantic_rejection(lambda value: derive_policy_instances(policy_case["operator"], value, discovery_drift), policy_case["siteRegistry"], "policy derivation accepted stale mutation-discovery consequence")

    oracle_declaration = load(FIXTURES / "mutation-manifest.json")["oracles"][0]
    crash_terminal = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": load(FIXTURES / "semantic-crash.json")["crashDigest"]}}
    baseline_gate = deepcopy(base["baseline"]["oracleResults"][0])
    baseline_gate.update({"outcome": "error", "operand": {"side": "baseline", "terminal": deepcopy(crash_terminal)}, "failure": {"sourceSide": "comparison", "failure": {"stage": "oracle", "classification": "baseline-mismatch", "context": "baseline-oracle-gate", "scope": "campaign", "retryability": "never", "semanticEvidence": [], "details": {}}}})
    validate_oracle_against_declaration(baseline_gate, oracle_declaration)
    baseline_gate_drift = taxonomy_with_disposition("oracle", "baseline-mismatch", "baseline-oracle-gate", "campaign", "unknown")
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, oracle_declaration, baseline_gate_drift), baseline_gate, "normal-required baseline gate accepted stale error after refreshed consequence drift")

    incomparable = deepcopy(base["mutants"][0]["oracleResults"][0])
    incomparable["operands"][1]["terminal"] = deepcopy(crash_terminal)
    incomparable.update({"outcome": "incomparable", "failure": {"sourceSide": "comparison", "failure": {"stage": "oracle", "classification": "incomparable-result", "context": "oracle-comparison", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}}})
    incomparable_declaration = {**oracle_declaration, "crashPolicy": "semantic-crash-incomparable"}
    validate_oracle_against_declaration(incomparable, incomparable_declaration)
    incomparable_drift = taxonomy_with_disposition("oracle", "incomparable-result", "oracle-comparison", "mutant", "unknown")
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, incomparable_declaration, incomparable_drift), incomparable, "incomparable oracle accepted stale incomparable outcome after refreshed consequence drift")

    wrapper_schema = schema["$defs"]["oracleFailure"]
    baseline_failure = {"stage": "infrastructure", "classification": "worker-lost", "context": "baseline-execution", "scope": "campaign", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}
    mutant_failure = {**deepcopy(baseline_failure), "context": "mutant-execution", "scope": "mutant"}
    comparison_failure = {"stage": "oracle", "classification": "incomparable-result", "context": "oracle-comparison", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
    mismatches = [
        {"sourceSide": "baseline-execution", "failure": mutant_failure},
        {"sourceSide": "mutant-execution", "failure": baseline_failure},
        {"sourceSide": "comparison", "failure": mutant_failure},
        {"sourceSide": "baseline-execution", "failure": comparison_failure},
    ]
    for index, wrapper in enumerate(mismatches):
        expect_semantic_rejection(lambda value: validate_schema(value, wrapper_schema, schema_path, schema), wrapper, f"oracle source/context reversal {index} was accepted")
    pairwise_gate = {"sourceSide": "comparison", "failure": {"stage": "oracle", "classification": "baseline-mismatch", "context": "baseline-oracle-gate", "scope": "campaign", "retryability": "never", "semanticEvidence": [], "details": {}}}
    pairwise_oracle = deepcopy(base["mutants"][0]["oracleResults"][0])
    pairwise_oracle.update({"outcome": "error", "failure": pairwise_gate})
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, load(FIXTURES / "mutation-manifest.json")["oracles"][0]), pairwise_oracle, "pairwise comparison accepted baseline-oracle-gate context")


def verify_semantic_termination_and_crash_oracle() -> None:
    termination_vectors = load(VECTORS / "execution-pattern-vectors.json")["semanticTerminationCases"]
    ok({case["id"] for case in termination_vectors} == {"crash-with-prior-witness", "crash-with-exhaustive-absence", "missing-crash-evidence", "backend-error-before-path"}, "semantic termination vectors are incomplete")
    oracle_vectors = load(VECTORS / "mutation-vectors.json")["oracleTerminalCases"]
    ok(len(oracle_vectors) == 11 and len({case["id"] for case in oracle_vectors}) == len(oracle_vectors), "oracle terminal vector coverage is incomplete or duplicate")
    for case in oracle_vectors:
        if case.get("failure") is not None:
            derived = "error"
        else:
            left_kind, left_digest = case["baseline"].split(":")
            right_kind, right_digest = case["mutant"].split(":")
            if (left_kind, left_digest) == (right_kind, right_digest):
                derived = "agree"
            elif left_kind == right_kind == "normal":
                derived = "distinguish"
            else:
                derived = "distinguish" if case["policy"] == "semantic-crash-distinguishes" else "incomparable"
        ok(derived == case["expected"], f"{case['id']}: terminal oracle vector outcome drift")
    terminal_schema_path = SCHEMAS / "terminal-state.schema.json"
    terminal_schema = load(terminal_schema_path)
    crash_schema_path = SCHEMAS / "semantic-crash.schema.json"
    crash_schema = load(crash_schema_path)
    trace_schema_path = SCHEMAS / "event-trace.schema.json"
    trace_schema = load(trace_schema_path)
    campaign_schema_path = SCHEMAS / "mutation-campaign.schema.json"
    campaign_schema = load(campaign_schema_path)
    manifest_schema_path = SCHEMAS / "mutation-manifest.schema.json"
    manifest_schema = load(manifest_schema_path)
    terminal = load(FIXTURES / "terminal-state.json")
    mutant_terminal = load(FIXTURES / "terminal-state-mutant.json")
    crash = load(FIXTURES / "semantic-crash.json")
    mutant_crash = load(FIXTURES / "semantic-crash-mutant.json")
    terminals, crashes = terminal_artifact_registry()
    validate_schema(terminal, terminal_schema, terminal_schema_path, terminal_schema)
    validate_schema(crash, crash_schema, crash_schema_path, crash_schema)
    validate_schema(mutant_terminal, terminal_schema, terminal_schema_path, terminal_schema)
    validate_schema(mutant_crash, crash_schema, crash_schema_path, crash_schema)

    bad = deepcopy(terminal)
    bad["terminalStateDigest"] = "f" * 64
    expect_semantic_rejection(lambda value: ok(value["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", value_without(value, "terminalStateDigest")), "terminal self ID"), bad, "wrong terminal-state self ID was accepted")
    bad = deepcopy(terminal)
    bad["value"]["node"] = {"kind": "token", "text": "drift"}
    expect_semantic_rejection(lambda value: ok(value["terminalStateDigest"] == digest("k-in-k/terminal-state/v1", value_without(value, "terminalStateDigest")), "terminal content drift"), bad, "terminal-state drift survived a stale self ID")
    for field in ("exception", "stderr", "exitStatus", "stackTrace"):
        bad = deepcopy(crash)
        bad[field] = "host diagnostic"
        expect_schema_rejection(bad, "semantic-crash.schema.json", f"semantic crash accepted host {field}")
    bad = deepcopy(crash)
    bad["classification"] = "host-exception"
    expect_schema_rejection(bad, "semantic-crash.schema.json", "unknown semantic crash class was accepted")
    bad = deepcopy(crash)
    bad.pop("terminalState")
    expect_schema_rejection(bad, "semantic-crash.schema.json", "semantic crash without terminal evidence was accepted")
    for mutate, label in (
        (lambda value: value.update({"crashDigest": "f" * 64}), "wrong crash self ID"),
        (lambda value: value.update({"executionProfileDigest": "f" * 64}), "crash profile drift"),
        (lambda value: value["terminalState"].update({"digest": "f" * 64}), "crash terminal drift"),
    ):
        bad = deepcopy(crash)
        mutate(bad)
        expect_semantic_rejection(lambda value: ok(value["crashDigest"] == digest("k-in-k/semantic-crash/v1", value_without(value, "crashDigest")), "crash identity"), bad, f"{label} survived a stale crash ID")

    base_trace = load(FIXTURES / "event-trace.json")
    crash_trace = deepcopy(base_trace)
    crash_trace["executionTerminal"] = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": crash["crashDigest"]}}
    crash_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(crash_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    crash_trace_digest = digest("k-in-k/event-trace/v1", crash_trace)
    validate_schema(crash_trace, trace_schema, trace_schema_path, trace_schema)
    validate_trace_semantics(crash_trace, (terminals, crashes))
    pattern = load(FIXTURES / "pattern-result.json")
    crash_match = deepcopy(pattern)
    crash_match["pathResults"][0].update({"pathIdentityDigest": crash_trace["pathIdentityDigest"], "traceDigest": crash_trace_digest, "executionTerminal": deepcopy(crash_trace["executionTerminal"])})
    crash_match["inputs"]["artifacts"] = [{"role": "event-trace", "digest": crash_trace_digest}]
    crash_match["resultId"] = digest("k-in-k/pattern-result/v1", value_without(crash_match, "resultId"))
    validate_pattern_result_semantics(crash_match, {crash_trace_digest: crash_trace})
    ok(crash_match["outcome"] == "match", "complete crashed path lost its prior witness")

    no_match = load(FIXTURES / "mutation-pattern-result.json")
    no_match_trace = deepcopy(load(FIXTURES / "mutation-event-trace.json"))
    no_match_trace["executionTerminal"] = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": mutant_crash["crashDigest"]}}
    no_match_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(no_match_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    no_match_trace_digest = digest("k-in-k/event-trace/v1", no_match_trace)
    no_match["pathResults"][0].update({"pathIdentityDigest": no_match_trace["pathIdentityDigest"], "traceDigest": no_match_trace_digest, "executionTerminal": deepcopy(no_match_trace["executionTerminal"])})
    no_match["inputs"]["artifacts"] = [{"role": "event-trace", "digest": no_match_trace_digest}]
    no_match["resultId"] = digest("k-in-k/pattern-result/v1", value_without(no_match, "resultId"))
    validate_pattern_result_semantics(no_match, {no_match_trace_digest: no_match_trace})
    ok(no_match["outcome"] == "no-match", "complete crashed path fabricated pattern error")

    wrong_definition_trace = deepcopy(load(FIXTURES / "mutation-event-trace.json"))
    wrong_definition_trace["executionTerminal"] = {"kind": "normal", "artifact": {"role": "terminal-state", "digest": terminal["terminalStateDigest"]}}
    wrong_definition_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(wrong_definition_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    expect_semantic_rejection(lambda value: validate_trace_semantics(value, (terminals, crashes)), wrong_definition_trace, "mutant trace reused a baseline terminal state")
    wrong_definition_trace["executionTerminal"] = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": crash["crashDigest"]}}
    wrong_definition_trace["pathIdentityDigest"] = digest("k-in-k/unkeyed-path/v1", value_without(wrong_definition_trace, "pathOrdinal", "pathKey", "pathIdentityDigest"))
    expect_semantic_rejection(lambda value: validate_trace_semantics(value, (terminals, crashes)), wrong_definition_trace, "mutant trace reused a baseline semantic crash")

    for mutate, label in (
        (lambda value: value.update({"complete": False}), "incomplete trace with terminal"),
        (lambda value: value.update({"executionTerminal": None}), "complete trace without terminal"),
        (lambda value: value.update({"stopReason": "stuck"}), "crash paired with stuck stop"),
        (lambda value: value.update({"stopReason": "depth-limit"}), "crash paired with limit stop"),
        (lambda value: value.update({"stopReason": "error"}), "crash paired with error stop"),
    ):
        bad = deepcopy(crash_trace)
        mutate(bad)
        expect_semantic_rejection(validate_trace_semantics, bad, f"{label} was accepted")
    bad = deepcopy(crash_trace)
    bad["executionTerminal"]["artifact"]["digest"] = "f" * 64
    expect_semantic_rejection(validate_trace_semantics, bad, "dangling crash key was accepted")
    bad_pattern = deepcopy(crash_match)
    bad_pattern["pathResults"][0]["executionTerminal"] = deepcopy(base_trace["executionTerminal"])
    bad_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_pattern, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {crash_trace_digest: crash_trace}), bad_pattern, "trace/path terminal drift was accepted")
    bad_pattern = deepcopy(crash_match)
    bad_pattern["pathResults"][0]["failures"] = [{"stage": "execution", "classification": "backend-error", "context": "pattern-path", "scope": "path", "retryability": "never", "semanticEvidence": [], "details": {}}]
    bad_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_pattern, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {crash_trace_digest: crash_trace}), bad_pattern, "semantic crash path carried a generic failure")
    bad_pattern = deepcopy(no_match)
    bad_pattern["pathResults"][0]["status"] = "error"
    bad_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_pattern, "resultId"))
    expect_semantic_rejection(lambda value: validate_pattern_result_semantics(value, {no_match_trace_digest: no_match_trace}), bad_pattern, "well-formed semantic terminal path caused pattern error")

    common = load(SCHEMAS / "common.schema.json")
    old_failure = {"stage": "execution", "classification": "semantic-crash", "context": "mutant-execution", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}
    expect_semantic_rejection(lambda value: validate_schema(value, common["$defs"]["failure"], SCHEMAS / "common.schema.json", common), old_failure, "legacy generic semantic-crash failure was accepted")

    verify_generic_failure_schema_inventory()
    mismatch = {"stage": "oracle", "classification": "baseline-mismatch", "context": "baseline-oracle-gate", "scope": "campaign", "retryability": "never", "semanticEvidence": [], "details": {}}
    bad_installation = deepcopy(load(FIXTURES / "observation-installation-result.json"))
    bad_installation.update({"status": "error", "outputDefinitionDigest": None, "appliedSelectionCount": 0, "installedSelectionIds": [], "failures": [deepcopy(mismatch)]})
    bad_installation["resultId"] = digest("k-in-k/observation-installation-result/v1", value_without(bad_installation, "resultId"))
    expect_schema_rejection(bad_installation, "observation-installation-result.schema.json", "baseline-mismatch in observation installation failures was accepted")
    for placement in ("test", "path"):
        bad_pattern = deepcopy(pattern)
        scoped = deepcopy(mismatch)
        scoped["scope"] = placement
        if placement == "test":
            bad_pattern["failures"] = [scoped]
        else:
            bad_pattern["pathResults"][0]["failures"] = [scoped]
        bad_pattern["resultId"] = digest("k-in-k/pattern-result/v1", value_without(bad_pattern, "resultId"))
        expect_semantic_rejection(validate_pattern_result_semantics, bad_pattern, f"baseline-mismatch in pattern {placement} failures was accepted")
    corpus_manifest = load(FIXTURES / "corpus-manifest.json")
    corpus_result = load(FIXTURES / "corpus-result.json")
    corpus_placements = (
        ("campaign", lambda value: value["failures"].append(deepcopy(mismatch))),
        ("test", lambda value: value["components"][0]["failures"].append({**deepcopy(mismatch), "scope": "test"})),
        ("path", lambda value: value["components"][0]["pathResults"][0]["failures"].append({**deepcopy(mismatch), "scope": "path"})),
    )
    for label, mutate in corpus_placements:
        bad_corpus = deepcopy(corpus_result)
        mutate(bad_corpus)
        bad_corpus["resultId"] = digest("k-in-k/corpus-result/v1", value_without(bad_corpus, "resultId"))
        expect_semantic_rejection(lambda value: validate_corpus_result_semantics(corpus_manifest, value), bad_corpus, f"baseline-mismatch in corpus pattern {label} failures was accepted")
    # The remainder of this historical routine constructs BAG-09 global
    # oracle declarations and operand envelopes.  BAG-12's package verifier
    # above now exercises the corresponding crash truth table, outer failure
    # matrix, profile/definition binding, and campaign fold through the sole
    # published typed authority.
    return
    base_campaign = load(FIXTURES / "mutation-campaign.json")
    generic_placements = (
        ("campaign failures", lambda value: value["failures"].append(deepcopy(mismatch))),
        ("generation failures", lambda value: value["generation"]["failures"].append(deepcopy(mismatch))),
        ("candidate rejection failures", lambda value: value["candidateRejections"].append({"status": "no-change", "patchId": value["generation"]["candidates"][0]["patch"]["patchId"], "originInstanceIds": [value["generation"]["candidates"][0]["originInstances"][0]["instanceId"]], "failures": [deepcopy(mismatch)]})),
        ("mutant failures", lambda value: value["mutants"][0]["failures"].append({**deepcopy(mismatch), "scope": "mutant"})),
    )
    for label, mutate in generic_placements:
        bad_campaign = deepcopy(base_campaign)
        mutate(bad_campaign)
        refresh_campaign_ids(bad_campaign)
        expect_semantic_rejection(validate_campaign_semantics, bad_campaign, f"baseline-mismatch in {label} was accepted")
    policy_cases = {case["id"]: case for case in load(FIXTURES / "mutation-policy-cases.json")["cases"]}
    bad_registry = deepcopy(policy_cases["nonexhaustive-prefix"]["siteRegistry"])
    bad_registry["discovery"]["failure"] = deepcopy(mismatch)
    bad_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", value_without(bad_registry, "registryId"))
    expect_semantic_rejection(validate_policy_registry_shape, bad_registry, "baseline-mismatch in mutation discovery failure was accepted")

    manifest = load(FIXTURES / "mutation-manifest.json")
    declaration = deepcopy(manifest["oracles"][0])
    normal_a = {"kind": "normal", "artifact": {"role": "oracle-value", "digest": "a" * 64}}
    normal_b = {"kind": "normal", "artifact": {"role": "oracle-value", "digest": "b" * 64}}
    crash_a = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": crash["crashDigest"]}}
    crash_mutant = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": mutant_crash["crashDigest"]}}
    crash_b = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": "c" * 64}}
    prototype = {"oracleId": declaration["oracleId"], "kind": declaration["kind"], "projectionDigest": declaration["projectionDigest"], "comparisonDigest": declaration["comparisonDigest"], "outcome": "agree", "operands": [{"side": "baseline", "terminal": deepcopy(normal_a)}, {"side": "mutant", "terminal": deepcopy(normal_a)}], "witnessDigest": None, "failure": None}
    validate_oracle_against_declaration(prototype, declaration)
    unequal = deepcopy(prototype)
    unequal.update({"outcome": "distinguish", "operands": [{"side": "baseline", "terminal": deepcopy(normal_a)}, {"side": "mutant", "terminal": deepcopy(normal_b)}]})
    validate_oracle_against_declaration(unequal, declaration)
    incomparable_failure = {"sourceSide": "comparison", "failure": {"stage": "oracle", "classification": "incomparable-result", "context": "oracle-comparison", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}}
    for policy in ("semantic-crash-distinguishes", "semantic-crash-incomparable"):
        policy_declaration = {**declaration, "crashPolicy": policy}
        identical = deepcopy(prototype)
        identical["operands"] = [{"side": "baseline", "terminal": deepcopy(crash_a)}, {"side": "mutant", "terminal": deepcopy(crash_a)}]
        validate_oracle_against_declaration(identical, policy_declaration)
        for left, right in ((normal_a, crash_a), (crash_a, normal_a), (crash_a, crash_b), (crash_b, crash_a)):
            comparison = deepcopy(prototype)
            comparison["operands"] = [{"side": "baseline", "terminal": deepcopy(left)}, {"side": "mutant", "terminal": deepcopy(right)}]
            if policy == "semantic-crash-distinguishes":
                comparison["outcome"] = "distinguish"
            else:
                comparison.update({"outcome": "incomparable", "failure": deepcopy(incomparable_failure)})
            validate_oracle_against_declaration(comparison, policy_declaration)

    for mutate, label in (
        (lambda value: value["operands"].reverse(), "reordered operand sides"),
        (lambda value: value["operands"][1].update({"side": "baseline"}), "duplicate operand sides"),
        (lambda value: value["operands"].pop(), "missing operand side"),
    ):
        bad = deepcopy(prototype)
        mutate(bad)
        expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), bad, f"{label} was accepted")
    bad = deepcopy(prototype)
    bad["operands"][0]["terminal"]["crash"] = deepcopy(crash_a["artifact"])
    expect_semantic_rejection(lambda value: validate_schema(value, campaign_schema["$defs"]["oracleResult"], campaign_schema_path, campaign_schema), bad, "operand with both normal and crash values was accepted")
    skipped = deepcopy(prototype)
    skipped.update({"outcome": "skipped", "operands": [{"side": "baseline", "terminal": None}, {"side": "mutant", "terminal": None}]})
    validate_oracle_against_declaration(skipped, declaration)
    for mutate, label in (
        (lambda value: value["operands"][0].update({"terminal": None}), "null baseline without failure"),
        (lambda value: value["operands"][1].update({"terminal": None}), "null mutant without failure"),
        (lambda value: value.update({"outcome": "skipped", "failure": deepcopy(incomparable_failure)}), "skipped with failure"),
        (lambda value: value.update({"outcome": "skipped"}), "skipped with operands"),
    ):
        bad = deepcopy(prototype)
        mutate(bad)
        expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), bad, f"{label} was accepted")
    bad = deepcopy(prototype)
    bad.update({"outcome": "distinguish", "operands": [{"side": "baseline", "terminal": deepcopy(crash_a)}, {"side": "mutant", "terminal": deepcopy(crash_a)}]})
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), bad, "identical crashes claimed distinguish")
    bad = deepcopy(prototype)
    bad["operands"] = [{"side": "baseline", "terminal": deepcopy(normal_a)}, {"side": "mutant", "terminal": deepcopy(crash_a)}]
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), bad, "mixed normal/crash claimed agree")
    backend = deepcopy(prototype)
    backend.update({"outcome": "error", "operands": [{"side": "baseline", "terminal": deepcopy(normal_a)}, {"side": "mutant", "terminal": None}], "failure": {"sourceSide": "mutant-execution", "failure": {"stage": "infrastructure", "classification": "worker-lost", "context": "mutant-execution", "scope": "mutant", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}}})
    validate_oracle_against_declaration(backend, declaration)
    backend["outcome"] = "distinguish"
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), backend, "infrastructure failure reported as kill")
    bad = deepcopy(prototype)
    bad.update({"outcome": "error", "failure": {"sourceSide": "comparison", "failure": {"stage": "oracle", "classification": "baseline-mismatch", "context": "baseline-oracle-gate", "scope": "mutant", "retryability": "never", "semanticEvidence": [], "details": {}}}})
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), bad, "baseline-mismatch outside baseline gate was accepted")

    baseline_result = {"oracleId": declaration["oracleId"], "kind": declaration["kind"], "projectionDigest": declaration["projectionDigest"], "comparisonDigest": declaration["comparisonDigest"], "outcome": "accepted", "operand": {"side": "baseline", "terminal": deepcopy(crash_a)}, "failure": None}
    allowed = {**declaration, "baselineTerminalPolicy": "semantic-crash-allowed"}
    validate_oracle_against_declaration(baseline_result, allowed)
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), baseline_result, "baseline crash accepted under normal-required")
    normal_baseline = deepcopy(baseline_result)
    normal_baseline["operand"]["terminal"] = deepcopy(normal_a)
    for policy in ("normal-required", "semantic-crash-allowed"):
        validate_oracle_against_declaration(normal_baseline, {**declaration, "baselineTerminalPolicy": policy})
        rejected = deepcopy(normal_baseline)
        rejected["outcome"] = "error"
        expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, {**declaration, "baselineTerminalPolicy": policy}), rejected, "normal terminal rejected solely by baseline policy")
    fake_self = deepcopy(prototype)
    fake_self.pop("operands")
    fake_self.update({"baselineValueDigest": "a" * 64, "mutantValueDigest": "a" * 64, "valueArtifacts": [], "failure": None})
    expect_semantic_rejection(lambda value: validate_schema(value, campaign_schema["$defs"]["baselineOracleResult"], campaign_schema_path, campaign_schema), fake_self, "fake baseline self-comparison was accepted")
    missing_policy = deepcopy(manifest)
    missing_policy["oracles"][0].pop("baselineTerminalPolicy")
    expect_schema_rejection(missing_policy, "mutation-manifest.schema.json", "missing baseline terminal policy was accepted")
    drifted_policy = deepcopy(manifest)
    drifted_policy["oracles"][0]["baselineTerminalPolicy"] = "semantic-crash-allowed"
    ok(drifted_policy["manifestId"] != digest("k-in-k/mutation-manifest/v1", value_without(drifted_policy, "manifestId")), "baseline policy drift preserved manifest identity")

    positive_registry = mutation_package_registry()
    positive_manifest = deepcopy(manifest)
    positive_manifest["oracles"][0]["baselineTerminalPolicy"] = "semantic-crash-allowed"
    positive_manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", value_without(positive_manifest, "manifestId"))
    positive_campaign = deepcopy(base_campaign)
    positive_campaign["manifestDigest"] = positive_manifest["manifestId"]
    positive_campaign["baseline"]["oracleResults"][0].update({"outcome": "accepted", "operand": {"side": "baseline", "terminal": deepcopy(crash_a)}, "failure": None})
    positive_campaign["mutants"][0]["oracleResults"][0].update({"outcome": "agree", "operands": [{"side": "baseline", "terminal": deepcopy(crash_a)}, {"side": "mutant", "terminal": deepcopy(crash_mutant)}], "failure": None})
    refresh_campaign_ids(positive_campaign)
    positive_registry["manifests"][positive_manifest["manifestId"]] = positive_manifest
    validate_official_instance(positive_campaign, "mutation-campaign.schema.json")
    validate_campaign_semantics(positive_campaign, positive_registry)
    ok(positive_campaign["baseline"]["status"] == "valid" and positive_campaign["campaignStatus"] == "complete" and positive_campaign["score"] == base_campaign["score"], "admitted baseline crash did not preserve full campaign scoring")
    cross_definition_crash = deepcopy(positive_campaign)
    cross_definition_crash["mutants"][0]["oracleResults"][0]["operands"][1]["terminal"] = deepcopy(crash_a)
    refresh_campaign_ids(cross_definition_crash)
    expect_semantic_rejection(lambda value: validate_campaign_semantics(value, positive_registry), cross_definition_crash, "mutant oracle side reused baseline semantic-crash evidence")

    def refresh_profile_drift(orientation: str) -> tuple[dict[str, Any], dict[str, dict[str, dict[str, Any]]]]:
        drift_campaign = deepcopy(positive_campaign)
        drift_registry = deepcopy(positive_registry)
        source_crash = mutant_crash if orientation == "mutant-crash" else crash
        drift_crash = deepcopy(source_crash)
        drift_crash["executionProfileDigest"] = "f" * 64
        drift_crash["crashDigest"] = digest("k-in-k/semantic-crash/v1", value_without(drift_crash, "crashDigest"))
        old_crash_digest = source_crash["crashDigest"]
        new_crash_digest = drift_crash["crashDigest"]
        drift_terminal = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": new_crash_digest}}
        baseline_normal_terminal = deepcopy(base_campaign["mutants"][0]["oracleResults"][0]["operands"][0]["terminal"])
        mutant_normal_terminal = deepcopy(base_campaign["mutants"][0]["oracleResults"][0]["operands"][1]["terminal"])
        normal_admission = deepcopy(base_campaign["baseline"]["oracleResults"][0])
        if orientation == "baseline-admission":
            drift_campaign["baseline"]["oracleResults"][0]["operand"]["terminal"] = deepcopy(drift_terminal)
            drift_campaign["mutants"][0]["oracleResults"][0].update({"outcome": "agree", "operands": [{"side": "baseline", "terminal": deepcopy(baseline_normal_terminal)}, {"side": "mutant", "terminal": deepcopy(mutant_normal_terminal)}]})
        elif orientation == "baseline-crash":
            drift_campaign["baseline"]["oracleResults"][0] = normal_admission
            drift_campaign["mutants"][0]["oracleResults"][0].update({"outcome": "distinguish", "operands": [{"side": "baseline", "terminal": deepcopy(drift_terminal)}, {"side": "mutant", "terminal": deepcopy(mutant_normal_terminal)}]})
        elif orientation == "mutant-crash":
            drift_campaign["baseline"]["oracleResults"][0] = normal_admission
            drift_campaign["mutants"][0]["oracleResults"][0].update({"outcome": "distinguish", "operands": [{"side": "baseline", "terminal": deepcopy(baseline_normal_terminal)}, {"side": "mutant", "terminal": deepcopy(drift_terminal)}]})
        else:
            raise AssertionError(f"unsupported profile-drift orientation {orientation}")
        admission_terminal = drift_campaign["baseline"]["oracleResults"][0]["operand"]["terminal"]
        comparison_operands = drift_campaign["mutants"][0]["oracleResults"][0]["operands"]
        if orientation == "baseline-admission":
            ok(admission_terminal == drift_terminal and all(slot["terminal"]["kind"] == "normal" for slot in comparison_operands), "baseline-admission drift adversary did not isolate admission")
        else:
            crash_side = next(slot["side"] for slot in comparison_operands if slot["terminal"] == drift_terminal)
            ok(drift_campaign["baseline"]["status"] == "valid" and admission_terminal["kind"] == "normal" and crash_side == orientation.removesuffix("-crash"), f"{orientation}: pairwise drift adversary did not preserve normal baseline admission or isolate its operand")
        for owner in [drift_campaign["baseline"], *drift_campaign["mutants"]]:
            for oracle_result in owner["oracleResults"]:
                slots = [oracle_result["operand"]] if "operand" in oracle_result else oracle_result["operands"]
                for slot in slots:
                    terminal_value = slot["terminal"]
                    if terminal_value is not None and terminal_value["kind"] == "semantic-crash" and terminal_value["artifact"]["digest"] == old_crash_digest:
                        terminal_value["artifact"]["digest"] = new_crash_digest

        old_catalog = next(iter(drift_registry["catalogs"].values()))
        drift_catalog = deepcopy(old_catalog)
        crash_entry = next(entry for entry in drift_catalog["entries"] if (entry["role"], entry["digest"]) == ("semantic-crash", old_crash_digest))
        crash_entry.update({"digest": new_crash_digest, "contentSha256": hashlib.sha256(canonical(drift_crash).encode("utf-8")).hexdigest(), "logicalPath": f"artifact://catalog/semantic-crash/{new_crash_digest}"})
        drift_catalog["entries"].sort(key=lambda entry: (entry["role"], entry["digest"]))
        drift_catalog["catalogId"] = digest("k-in-k/artifact-catalog/v1", value_without(drift_catalog, "catalogId"))

        old_corpus = next(iter(drift_registry["corpora"].values()))
        drift_corpus = deepcopy(old_corpus)
        drift_corpus["artifactCatalogDigest"] = drift_catalog["catalogId"]
        drift_corpus["manifestId"] = digest("k-in-k/corpus-manifest/v1", value_without(drift_corpus, "manifestId"))
        drift_manifest = deepcopy(positive_manifest)
        drift_manifest.update({"artifactCatalogDigest": drift_catalog["catalogId"], "corpusManifestDigest": drift_corpus["manifestId"]})
        drift_manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", value_without(drift_manifest, "manifestId"))
        drift_campaign["manifestDigest"] = drift_manifest["manifestId"]
        refresh_campaign_ids(drift_campaign)
        drift_registry["catalogs"] = {drift_catalog["catalogId"]: drift_catalog}
        drift_registry["corpora"] = {drift_corpus["manifestId"]: drift_corpus}
        drift_registry["manifests"] = {drift_manifest["manifestId"]: drift_manifest}
        drift_registry["crashes"].pop(old_crash_digest)
        drift_registry["crashes"][new_crash_digest] = drift_crash
        refreshed_roots = (drift_catalog["catalogId"], drift_corpus["manifestId"], drift_manifest["manifestId"], drift_campaign["campaignId"], drift_campaign["reportId"])
        original_roots = (old_catalog["catalogId"], old_corpus["manifestId"], positive_manifest["manifestId"], positive_campaign["campaignId"], positive_campaign["reportId"])
        ok(all(refreshed != original for refreshed, original in zip(refreshed_roots, original_roots)), f"{orientation}: crash profile drift did not refresh every catalog/corpus/manifest/campaign/report root")
        validate_official_instance(drift_campaign, "mutation-campaign.schema.json")
        return drift_campaign, drift_registry

    for orientation in ("baseline-admission", "baseline-crash", "mutant-crash"):
        drift_campaign, drift_registry = refresh_profile_drift(orientation)
        expect_semantic_rejection(lambda value: validate_campaign_semantics(value, drift_registry), drift_campaign, f"{orientation}: refreshed semantic-crash profile drift was accepted")

    validate_schema(load(FIXTURES / "mutation-campaign.json"), campaign_schema, campaign_schema_path, campaign_schema)
    validate_schema(manifest, manifest_schema, manifest_schema_path, manifest_schema)


def verify_campaign_fixture() -> None:
    campaign = load(FIXTURES / "mutation-campaign.json")
    validate_campaign_semantics(campaign)
    bad = deepcopy(campaign)
    bad["mutants"][0]["status"] = "unclassified-equivalent"
    refresh_campaign_ids(bad)
    expect_schema_rejection(bad, "mutation-campaign.schema.json", "removed equivalence status was accepted")
    bad = deepcopy(campaign)
    bad["mutants"][0]["equivalenceEvidence"] = {"kind": "portable-equivalence-proof", "digest": "3" * 64}
    refresh_campaign_ids(bad)
    expect_schema_rejection(bad, "mutation-campaign.schema.json", "opaque equivalence proof field was accepted")
    bad = deepcopy(campaign)
    bad["mutants"][0]["status"] = "survived"
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "equal final output fabricated survival despite a distinguishing pattern oracle")
    bad = deepcopy(campaign)
    mutant = bad["mutants"][0]
    mutant["status"] = "survived"
    mutant["tests"][0].update({"status": "skipped", "selected": False})
    for oracle in mutant["oracleResults"][:2]:
        oracle.update({"outcome": "skipped", "witnessDigest": None, "failure": None})
        set_oracle_normal_operands(oracle, None, None)
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "survived mutant accepted skipped test/oracle evidence")
    bad = deepcopy(campaign)
    bad["mutants"][0]["candidateId"] = "f" * 64
    expect_semantic_rejection(validate_campaign_semantics, bad, "dangling mutant candidate was accepted")
    bad = deepcopy(campaign)
    bad["mutants"][0]["oracleResults"][1]["outcome"] = "agree"
    expect_semantic_rejection(validate_campaign_semantics, bad, "killed mutant with agreeing oracles was accepted")
    bad = deepcopy(campaign)
    bad["score"]["denominator"] = 2
    expect_semantic_rejection(validate_campaign_semantics, bad, "inconsistent campaign score was accepted")
    bad = deepcopy(campaign)
    bad["baseline"]["status"] = "baseline-invalid"
    expect_semantic_rejection(validate_campaign_semantics, bad, "invalid baseline campaign was scored")
    bad = deepcopy(campaign)
    bad["generation"]["complete"] = False
    expect_semantic_rejection(validate_campaign_semantics, bad, "incomplete generation campaign was scored")
    bad = deepcopy(campaign)
    origin = bad["generation"]["candidates"][0]["originInstances"][0]
    origin["siteTuple"] = ["e" * 64, "f" * 64]
    origin["discoveryTuples"][0]["siteTuple"] = origin["siteTuple"]
    origin["instanceId"] = digest("k-in-k/instance/v1", mutation_instance_payload(bad["operator"], bad["baseline"]["definitionDigest"], bad["generation"]["policy"], origin, bad["generation"]["candidates"][0]["patch"]["patchId"]))
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "arbitrary mutation site tuple was accepted")
    for label, mutate in (
        ("unresolved operator digest", lambda value: value["operator"].update({"digest": "f" * 64})),
        ("operator policy drift", lambda value: value["generation"].update({"policy": "each"})),
        ("operator candidate-cap drift", lambda value: value["generation"].update({"candidateCap": 7})),
        ("dangling mutation replay", lambda value: value["mutants"][0].update({"replayManifestDigest": "f" * 64})),
        ("dangling pattern witness", lambda value: value["mutants"][0]["oracleResults"][1].update({"witnessDigest": "f" * 64})),
        ("wrong structural-diff artifact", lambda value: value["mutants"][0]["artifacts"][0].update({"digest": "f" * 64})),
    ):
        bad = deepcopy(campaign)
        mutate(bad)
        refresh_campaign_ids(bad)
        expect_semantic_rejection(validate_campaign_semantics, bad, f"{label} was accepted")
    bad = deepcopy(campaign)
    bad["mutants"][0]["tests"][1]["id"] = bad["mutants"][0]["tests"][0]["id"]
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "duplicate mutant test ID was accepted")
    bad = deepcopy(campaign)
    bad["mutants"][0]["tests"].reverse()
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "mutant test order drift was accepted")
    bad = deepcopy(campaign)
    bad["baseline"]["oracleResults"][0]["outcome"] = "timeout"
    refresh_campaign_ids(bad)
    expect_semantic_rejection(validate_campaign_semantics, bad, "valid baseline with a non-agreeing oracle was accepted")
    bad = deepcopy(campaign)
    bad["campaignStatus"] = "error"
    bad.pop("score")
    bad["mutants"] = []
    refresh_campaign_ids(bad)
    expect_schema_rejection(bad, "mutation-campaign.schema.json", "unexplained error campaign was accepted")
    declaration = load(FIXTURES / "mutation-manifest.json")["oracles"][0]
    crash_digest = load(FIXTURES / "semantic-crash.json")["crashDigest"]
    crash_terminal = {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": crash_digest}}
    crash_oracle = deepcopy(campaign["mutants"][0]["oracleResults"][0])
    crash_oracle.update({"outcome": "distinguish", "operands": [{"side": "baseline", "terminal": deepcopy(crash_terminal)}, {"side": "mutant", "terminal": deepcopy(campaign["mutants"][0]["oracleResults"][0]["operands"][1]["terminal"])}], "failure": None})
    validate_oracle_against_declaration(crash_oracle, declaration)
    incomparable_declaration = {**declaration, "crashPolicy": "semantic-crash-incomparable"}
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, incomparable_declaration), crash_oracle, "semantic crash ignored incomparable policy")
    infrastructure_oracle = deepcopy(crash_oracle)
    infrastructure_oracle.update({"outcome": "error", "operands": [{"side": "baseline", "terminal": None}, {"side": "mutant", "terminal": None}], "failure": {"sourceSide": "baseline-execution", "failure": {"stage": "infrastructure", "classification": "worker-lost", "context": "baseline-execution", "scope": "campaign", "retryability": "after-external-repair", "semanticEvidence": [], "details": {}}}})
    validate_oracle_against_declaration(infrastructure_oracle, declaration)
    infrastructure_oracle["outcome"] = "distinguish"
    expect_semantic_rejection(lambda value: validate_oracle_against_declaration(value, declaration), infrastructure_oracle, "infrastructure failure killed a mutant")


def verify_policy_generation_fixtures() -> None:
    data = load(FIXTURES / "mutation-policy-cases.json")
    cases = {case["id"]: case for case in data["cases"]}
    ok(len(cases) == len(data["cases"]), "duplicate policy fixture ID")
    for case in data["cases"]:
        # Policy-case campaigns are immutable BAG-10 synthetic envelopes used
        # only to test generation/receipt derivation.  Validate their live
        # operator and site-registry inputs, but do not submit the legacy
        # oracle envelope to BAG-12's published campaign schema.
        for value, schema_name in ((case["operator"], "mutation-operator.schema.json"), (case["siteRegistry"], "mutation-site-registry.schema.json")):
            schema_path = SCHEMAS / schema_name
            schema = load(schema_path)
            validate_schema(value, schema, schema_path, schema)
        validate_campaign_semantics(case["campaign"], policy_case_registry(case), check_artifact_graph=False)

    exact = derive_policy_instances(cases["exact-unary"]["operator"], cases["exact-unary"]["siteRegistry"])
    ok(exact["complete"] and len(exact["retained"]) == 1, "unary exact policy fixture did not derive one instance")
    each = derive_policy_instances(cases["each-multi"]["operator"], cases["each-multi"]["siteRegistry"])
    ok(each["complete"] and len(each["retained"]) == 3, "multi-site each policy fixture did not derive every site")
    tuple_each = derive_policy_instances(cases["tuple-each-supplied"]["operator"], cases["tuple-each-supplied"]["siteRegistry"])
    ok(tuple_each["complete"] and len(tuple_each["retained"]) == 2 and len(cases["tuple-each-supplied"]["campaign"]["generation"]["candidates"]) == 1, "tuple-each did not use and deduplicate only supplied joined tuples")
    all_matches = derive_policy_instances(cases["all-matches-aggregate"]["operator"], cases["all-matches-aggregate"]["siteRegistry"])
    ok(all_matches["complete"] and len(all_matches["retained"]) == 1 and len(all_matches["retained"][0]["siteTuple"]) == 2 and len(all_matches["retained"][0]["discoveryTuples"]) == 2, "all-matches did not preserve one aggregate with per-tuple bindings")
    dedup = cases["deduplicated-patch-origins"]["campaign"]["generation"]["candidates"]
    ok(len(dedup) == 1 and len(dedup[0]["originInstances"]) == 2, "identical-patch fixture did not retain both origins")
    for case_id, classification in (("exact-zero", "cardinality-mismatch"), ("exact-excess", "cardinality-mismatch"), ("exact-wrong-arity", "invalid-join")):
        campaign = cases[case_id]["campaign"]
        ok(campaign["campaignStatus"] == "selection-failed" and not campaign["generation"]["candidates"] and "score" not in campaign and campaign["generation"]["failures"][0]["classification"] == classification, f"{case_id} did not fail atomically")
    for case_id in ("cap-prefix", "nonexhaustive-prefix"):
        campaign = cases[case_id]["campaign"]
        ok(campaign["campaignStatus"] == "incomplete-generation" and not campaign["generation"]["complete"] and "score" not in campaign, f"{case_id} was not an unscored incomplete prefix")

    def reject(case: dict[str, Any], message: str, roots: bool = False) -> None:
        if roots:
            refresh_policy_case_roots(case)
        else:
            refresh_campaign_ids(case["campaign"])
        expect_semantic_rejection(lambda campaign: validate_campaign_semantics(campaign, policy_case_registry(case), check_artifact_graph=False), case["campaign"], message)

    bad = deepcopy(cases["tuple-each-supplied"])
    bad["operator"].update({"policy": "each", "expectedTupleCount": None, "expectedTupleArity": 1})
    reject(bad, "unary each accepted a non-null joined registry", roots=True)
    bad = deepcopy(cases["each-multi"])
    bad["operator"].update({"policy": "tuple-each", "expectedTupleCount": None, "expectedTupleArity": 2})
    reject(bad, "tuple-each accepted a null unary registry", roots=True)

    bad = deepcopy(cases["each-multi"])
    removed = bad["campaign"]["generation"]["candidates"].pop(1)
    bad["campaign"]["candidateRejections"] = [item for item in bad["campaign"]["candidateRejections"] if item["patchId"] != removed["patch"]["patchId"]]
    reject(bad, "complete each campaign omitted its middle instance")
    bad = deepcopy(cases["each-multi"])
    bad["campaign"]["generation"]["candidates"][0]["originInstances"].pop()
    reject(bad, "complete each campaign omitted its final instance", roots=True)
    bad = deepcopy(cases["each-multi"])
    bad["campaign"]["generation"]["candidates"].reverse()
    reject(bad, "complete each candidates were reorderable")
    bad = deepcopy(cases["each-multi"])
    bad["campaign"]["generation"]["candidates"][0]["originInstances"].reverse()
    reject(bad, "complete each deduplicated origins were reorderable")
    bad = deepcopy(cases["tuple-each-supplied"])
    bad["campaign"]["generation"]["candidates"][0]["originInstances"].reverse()
    reject(bad, "tuple-each origins were reorderable")

    for case_id in ("exact-zero", "exact-excess"):
        bad = deepcopy(cases[case_id])
        injected = deepcopy(cases["exact-unary"]["campaign"]["generation"]["candidates"][0])
        if case_id == "exact-excess":
            operator, site_registry = bad["operator"], bad["siteRegistry"]
            site_tuple = site_registry["tuples"][0]
            injected["patch"]["operatorId"] = operator["operatorId"]
            origin = injected["originInstances"][0]
            origin["siteTuple"] = site_tuple
            origin["discoveryTuples"] = [{"siteTuple": site_tuple, "bindings": canonical_discovery_bindings(site_tuple, {site["siteId"]: site for site in site_registry["sites"]})}]
            origin["instanceId"] = digest("k-in-k/instance/v1", mutation_instance_payload({"id": operator["operatorId"], "version": operator["operatorVersion"], "digest": operator["operatorDigest"]}, bad["campaign"]["baseline"]["definitionDigest"], operator["policy"], origin, injected["patch"]["patchId"]))
            injected["candidateId"] = digest("k-in-k/candidate/v1", {"operatorId": operator["operatorId"], "operatorVersion": operator["operatorVersion"], "baselineDefinitionDigest": bad["campaign"]["baseline"]["definitionDigest"], "patchId": injected["patch"]["patchId"]})
        bad["campaign"]["generation"]["candidates"] = [injected]
        reject(bad, f"{case_id} published a candidate after cardinality failure")

    bad = deepcopy(cases["all-matches-aggregate"])
    aggregate = bad["campaign"]["generation"]["candidates"][0]["originInstances"][0]
    bad["campaign"]["generation"]["candidates"][0]["originInstances"] = [{"instanceId": aggregate["instanceId"], "siteTuple": group["siteTuple"], "discoveryTuples": [group], "editReceipts": deepcopy(aggregate["editReceipts"])} for group in aggregate["discoveryTuples"]]
    reject(bad, "all-matches aggregate was split into independent instances", roots=True)
    bad = deepcopy(cases["all-matches-aggregate"])
    origin = bad["campaign"]["generation"]["candidates"][0]["originInstances"][0]
    origin["siteTuple"].reverse()
    reject(bad, "all-matches aggregate site order was mutable", roots=True)
    bad = deepcopy(cases["all-matches-aggregate"])
    origin = bad["campaign"]["generation"]["candidates"][0]["originInstances"][0]
    origin["siteTuple"].pop()
    origin["discoveryTuples"].pop()
    reject(bad, "all-matches aggregate could omit a site", roots=True)

    for case_id in ("cap-prefix", "nonexhaustive-prefix"):
        bad = deepcopy(cases[case_id])
        bad["campaign"]["generation"].update({"complete": True, "failures": []})
        bad["campaign"]["campaignStatus"] = "complete"
        bad["campaign"]["score"] = {"killed": 0, "survived": 0, "denominator": 0, "ratio": None, "excluded": {"invalid": 0, "timeout": 0, "unknown": 0, "error": 0, "duplicate": 0, "no-change": 0}}
        reject(bad, f"{case_id} prefix was marked complete")

    bad = deepcopy(cases["deduplicated-patch-origins"])
    bad["operator"]["candidateCap"] = 1
    bad["campaign"]["generation"]["candidateCap"] = 1
    reject(bad, "candidate cap was applied after patch deduplication", roots=True)
    bad = deepcopy(cases["deduplicated-patch-origins"])
    bad["campaign"]["generation"]["candidates"][0]["originInstances"].pop()
    reject(bad, "identical-patch deduplication discarded an origin", roots=True)
    bad = deepcopy(cases["deduplicated-patch-origins"])
    bad["campaign"]["generation"]["candidates"][0]["originInstances"].reverse()
    reject(bad, "deduplicated origins were permuted after report refresh")
    bad = deepcopy(cases["each-multi"])
    bad["campaign"]["generation"]["candidates"].reverse()
    reject(bad, "deduplicated candidates were permuted after report refresh")

    def reject_receipt(case: dict[str, Any], message: str) -> None:
        campaign = case["campaign"]
        for candidate in campaign["generation"]["candidates"]:
            for origin in candidate["originInstances"]:
                origin["instanceId"] = digest("k-in-k/instance/v1", mutation_instance_payload(campaign["operator"], campaign["baseline"]["definitionDigest"], campaign["generation"]["policy"], origin, candidate["patch"]["patchId"]))
        refresh_campaign_ids(campaign)
        expect_semantic_rejection(lambda value: validate_campaign_semantics(value, policy_case_registry(case), check_artifact_graph=False), campaign, message)

    tuple_origin = cases["tuple-each-supplied"]["campaign"]["generation"]["candidates"][0]["originInstances"][0]
    ok(all(len(receipt["sources"]) == 2 for receipt in tuple_origin["editReceipts"]), "multi-source edit receipts are not represented")
    ok(tuple_origin["editReceipts"][0]["sources"][0] in tuple_origin["editReceipts"][1]["sources"], "one selected source cannot authorize multiple distinct edits")
    dedup_origins = cases["deduplicated-patch-origins"]["campaign"]["generation"]["candidates"][0]["originInstances"]
    ok(len(dedup_origins) == 2 and all(len(origin["editReceipts"]) == 1 for origin in dedup_origins), "identical-patch deduplication lost complete edit receipts")

    for mutation, message in (
        (lambda origin: origin["editReceipts"].pop(), "missing mutation edit receipt was accepted"),
        (lambda origin: origin["editReceipts"].append(deepcopy(origin["editReceipts"][0])), "extra mutation edit receipt was accepted"),
        (lambda origin: origin["editReceipts"].reverse(), "reordered mutation edit receipts were accepted"),
    ):
        bad = deepcopy(cases["tuple-each-supplied"])
        mutation(bad["campaign"]["generation"]["candidates"][0]["originInstances"][0])
        reject_receipt(bad, message)

    bad = deepcopy(cases["deduplicated-patch-origins"])
    origins = bad["campaign"]["generation"]["candidates"][0]["originInstances"]
    foreign_source = deepcopy(origins[1]["editReceipts"][0]["sources"][0])
    origins[0]["editReceipts"][0]["sources"][0] = foreign_source
    reject_receipt(bad, "receipt for another origin's selected site was accepted")

    for mutation, message in (
        (lambda receipt: receipt["sources"][0].update({"discoveryTupleIndex": 1}), "receipt tuple-index/site mismatch was accepted"),
        (lambda receipt: receipt["sources"].reverse(), "noncanonical receipt source order was accepted"),
        (lambda receipt: receipt["sources"].append(deepcopy(receipt["sources"][0])), "duplicate receipt source was accepted"),
        (lambda receipt: receipt["sources"][0].update({"selectorRole": "invented"}), "receipt selector-role drift was accepted"),
        (lambda receipt: receipt["sources"][0].update({"tupleBindings": []}), "receipt tuple-binding drift was accepted"),
        (lambda receipt: receipt.update({"patchTemplateDigest": "f" * 64}), "receipt patch-template drift was accepted"),
        (lambda receipt: receipt["operator"].update({"digest": "f" * 64}), "receipt operator drift was accepted"),
        (lambda receipt: receipt.update({"templateRole": "invented"}), "undeclared receipt template role was accepted"),
        (lambda receipt: receipt.update({"editId": "f" * 64}), "dangling receipt edit ID was accepted"),
    ):
        bad = deepcopy(cases["tuple-each-supplied"])
        mutation(bad["campaign"]["generation"]["candidates"][0]["originInstances"][0]["editReceipts"][0])
        reject_receipt(bad, message)

    for mutate, message in (
        (lambda roles: roles.append(deepcopy(roles[0])), "duplicate patch-template role was accepted"),
        (lambda roles: roles.reverse(), "noncanonical patch-template roles were accepted"),
    ):
        bad_operator = deepcopy(load(FIXTURES / "mutation-operator.json"))
        mutate(bad_operator["patchTemplateRoles"])
        bad_operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", value_without(bad_operator, "operatorDigest"))
        expect_semantic_rejection(validate_operator_declaration, bad_operator, message)
    bad_operator = deepcopy(cases["exact-unary"]["operator"])
    bad_operator["patchTemplateRoles"][0]["sourceSelectorRoles"] = ["site", "site"]
    bad_operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", value_without(bad_operator, "operatorDigest"))
    expect_semantic_rejection(validate_operator_declaration, bad_operator, "duplicate patch-template selector sources were accepted")
    bad_operator = deepcopy(cases["exact-unary"]["operator"])
    bad_registry = deepcopy(cases["exact-unary"]["siteRegistry"])
    bad_operator["patchTemplateRoles"][0]["sourceSelectorRoles"] = ["invented"]
    bad_operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", value_without(bad_operator, "operatorDigest"))
    bad_registry["operatorDigest"] = bad_operator["operatorDigest"]
    bad_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", value_without(bad_registry, "registryId"))
    expect_semantic_rejection(lambda value: validate_mutation_site_registry(value, load(FIXTURES / "semantic-definition-memory.json"), bad_operator), bad_registry, "unresolved patch-template selector role was accepted")

    direct_case = cases["exact-unary"]
    direct_origin = deepcopy(direct_case["campaign"]["generation"]["candidates"][0]["originInstances"][0])
    direct_sites = {site["siteId"]: site for site in direct_case["siteRegistry"]["sites"]}
    direct_operator = deepcopy(direct_case["operator"])
    direct_operator["patchTemplateRoles"] = [{"name": "anchored-insert", "operation": "insert-sentence", "sourceSelectorRoles": ["site"]}]
    direct_operator["operatorDigest"] = digest("k-in-k/mutation-operator/v1", value_without(direct_operator, "operatorDigest"))
    direct_ref = {"id": direct_operator["operatorId"], "version": direct_operator["operatorVersion"], "digest": direct_operator["operatorDigest"]}
    patch_vectors = load(VECTORS / "patch-application-vectors.json")
    insertion_case = next(case for case in patch_vectors["cases"] if case["id"] == "before-and-module-end-insertion")
    insertion_patch = materialize_vector_patch(patch_vectors, insertion_case)
    anchored_edit = next(edit for edit in insertion_patch["edits"] if edit["position"]["kind"] == "before-lineage")
    direct_origin["editReceipts"] = [{"editId": anchored_edit["editId"], "operator": direct_ref, "patchTemplateDigest": direct_operator["patchTemplateDigest"], "templateRole": "anchored-insert", "sources": [{"discoveryTupleIndex": 0, "siteId": direct_origin["siteTuple"][0], "selectorRole": "site", "tupleBindings": deepcopy(direct_origin["discoveryTuples"][0]["bindings"])}]}]
    validate_edit_receipts(direct_ref, direct_operator, direct_origin, [anchored_edit], direct_sites)
    module_edit = next(edit for edit in insertion_patch["edits"] if edit["position"]["kind"] == "module-end")
    direct_origin["editReceipts"][0]["editId"] = module_edit["editId"]
    expect_semantic_rejection(lambda edits: validate_edit_receipts(direct_ref, direct_operator, direct_origin, edits, direct_sites), [module_edit], "module-boundary insertion receipt was accepted")

    bad_edit = deepcopy(direct_case["campaign"]["generation"]["candidates"][0]["patch"]["edits"][0])
    bad_edit["targetLineage"] = "f" * 64
    expect_semantic_rejection(lambda edits: validate_edit_receipts(direct_case["campaign"]["operator"], direct_case["operator"], direct_case["campaign"]["generation"]["candidates"][0]["originInstances"][0], edits, direct_sites), [bad_edit], "unauthorized receipt target lineage was accepted")
    operation_drift = deepcopy(direct_case["operator"])
    operation_drift["patchTemplateRoles"][0]["operation"] = "delete-sentence"
    expect_semantic_rejection(lambda declaration: validate_edit_receipts(direct_case["campaign"]["operator"], declaration, direct_case["campaign"]["generation"]["candidates"][0]["originInstances"][0], direct_case["campaign"]["generation"]["candidates"][0]["patch"]["edits"], direct_sites), operation_drift, "receipt/template operation drift was accepted")

    counter_operator = load(FIXTURES / "counter-mutation-operator.json")
    counter_registry = load(FIXTURES / "counter-mutation-site-registry.json")
    counter_definition = load(FIXTURES / "semantic-definition-counter.json")
    ok(counter_registry["selector"]["clauses"][0]["label"] is None, "label-free mutation selector fixture is missing")
    validate_mutation_site_registry(counter_registry, counter_definition, counter_operator)
    old_site_registry = deepcopy(counter_registry)
    site = old_site_registry["sites"][0]
    old_site_id = digest("k-in-k/site/v1", {"operatorId": counter_operator["operatorId"], "operatorVersion": counter_operator["operatorVersion"], "baselineDefinitionDigest": counter_definition["definitionDigest"], "targetLineage": site["sentenceLineage"], "selectorRole": site["selectorRole"], "bindings": site["bindings"]})
    old_site_registry["sites"][0]["siteId"] = old_site_id
    old_site_registry["tuples"] = [[old_site_id]]
    old_site_registry["registryId"] = digest("k-in-k/mutation-site-registry/v1", value_without(old_site_registry, "registryId"))
    expect_semantic_rejection(lambda value: validate_mutation_site_registry(value, counter_definition, counter_operator), old_site_registry, "legacy mutation site identity without termPath was accepted")


def verify_mutation_status_vectors() -> None:
    data = load(VECTORS / "mutation-status-vectors.json")
    base = load(FIXTURES / data["baseFixture"])
    schema_path = SCHEMAS / "mutation-campaign.schema.json"
    schema = load(schema_path)
    seen: set[str] = set()
    excluded_keys = ("invalid", "timeout", "unknown", "error", "duplicate", "no-change")
    policy_cases = {case["id"]: case for case in load(FIXTURES / "mutation-policy-cases.json")["cases"]}
    for case in data["cases"]:
        ok(case["id"] not in seen, f"duplicate mutation status vector {case['id']}")
        seen.add(case["id"])
        policy_case = deepcopy(policy_cases["nonexhaustive-prefix"]) if case.get("generationComplete") is False else None
        campaign = deepcopy(policy_case["campaign"] if policy_case is not None else base)
        if "baselineStatus" in case:
            campaign["baseline"]["status"] = case["baselineStatus"]
            campaign["baseline"]["failures"] = [case["failure"]]
            if case["baselineStatus"] == "baseline-invalid":
                campaign["baseline"]["tests"] = []
                campaign["baseline"]["oracleResults"] = []
            else:
                campaign["baseline"]["tests"][0]["status"] = "error"
                oracle = campaign["baseline"]["oracleResults"][0]
                crash_digest = load(FIXTURES / "semantic-crash.json")["crashDigest"]
                oracle.update({"outcome": "error", "operand": {"side": "baseline", "terminal": {"kind": "semantic-crash", "artifact": {"role": "semantic-crash", "digest": crash_digest}}}, "failure": {"sourceSide": "comparison", "failure": case["failure"]}})
            campaign["campaignStatus"] = case["expected"]["campaignStatus"]
            campaign["mutants"] = []
            campaign.pop("score", None)
        elif case.get("generationComplete") is False:
            campaign["generation"]["complete"] = False
            campaign["generation"]["failures"] = [case["failure"]]
            campaign["campaignStatus"] = case["expected"]["campaignStatus"]
            campaign["mutants"] = []
            campaign.pop("score", None)
        else:
            mutant = campaign["mutants"][0]
            mutant["status"] = case["mutantStatus"]
            mutant["validation"]["outcome"] = case["validationOutcome"]
            mutant["validation"]["closestStage"] = case["closestStage"]
            mutant["tests"][0]["status"] = case["testStatus"]
            mutant["failures"] = [case["failure"]] if "failure" in case else []
            for oracle, outcome in zip(mutant["oracleResults"], case["oracleOutcomes"]):
                oracle["outcome"] = outcome
                baseline_digest = oracle_operand_digest(oracle, 0)
                mutant_digest = oracle_operand_digest(oracle, 1)
                oracle["failure"] = None
                if outcome == "agree":
                    set_oracle_normal_operands(oracle, baseline_digest, baseline_digest)
                elif outcome == "distinguish":
                    if oracle["kind"] == "execution-pattern":
                        set_oracle_normal_operands(oracle, "91fee7940fce90536792eb9c2b3f06fed287cef9a120f003c6d3d8f203dfbb83", "bc878b18886c5fbb056ce8dbe8c1fd13ab73210169d3363d6cf8b10cdca0b204")
                    else:
                        set_oracle_normal_operands(oracle, baseline_digest, "29" * 32)
                elif outcome == "skipped":
                    set_oracle_normal_operands(oracle, None, None)
                    oracle["witnessDigest"] = None
                elif outcome == "incomparable":
                    oracle["failure"] = {"sourceSide": "comparison", "failure": case["failure"]}
                else:
                    set_oracle_normal_operands(oracle, baseline_digest, None)
                    oracle["failure"] = {"sourceSide": "mutant-execution", "failure": case["failure"]}
            killed = 1 if case["mutantStatus"] == "killed" else 0
            survived = 1 if case["mutantStatus"] == "survived" else 0
            denominator = killed + survived
            ratio = None if denominator == 0 else {"numerator": killed, "denominator": denominator}
            excluded = {key: 1 if case["expected"]["excludedStatus"] == key else 0 for key in excluded_keys}
            campaign["score"] = {"killed": killed, "survived": survived, "denominator": denominator, "ratio": ratio, "excluded": excluded}
        campaign["reportId"] = digest("k-in-k/mutation-report/v1", value_without(campaign, "reportId"))
        validate_schema(campaign, schema, schema_path, schema)
        try:
            validate_campaign_semantics(campaign, policy_case_registry(policy_case) if policy_case is not None else None, check_artifact_graph=False)
        except AssertionError as error:
            raise AssertionError(f"{case['id']}: {error}")
        ok(("score" in campaign) == case["expected"]["scored"], f"{case['id']}: score presence")
        if "score" in campaign:
            ok(campaign["score"]["killed"] == case["expected"]["killed"] and campaign["score"]["survived"] == case["expected"]["survived"], f"{case['id']}: score counts")
    for case in data["statusContradictionCases"]:
        campaign = deepcopy(base)
        mutant = campaign["mutants"][0]
        mutant["status"] = case["mutantStatus"]
        mutant["validation"] = {"outcome": case["validationOutcome"], "closestStage": case["closestStage"]}
        mutant["tests"][0]["status"] = case["testStatus"]
        mutant["failures"] = [case["failure"]]
        for oracle, outcome in zip(mutant["oracleResults"], case["oracleOutcomes"]):
            oracle["outcome"] = outcome
            if outcome in ("timeout", "unknown", "error"):
                set_oracle_normal_operands(oracle, oracle_operand_digest(oracle, 0), None)
                oracle["failure"] = {"sourceSide": "mutant-execution", "failure": case["failure"]}
            else:
                oracle["failure"] = None
        killed = int(case["mutantStatus"] == "killed")
        survived = int(case["mutantStatus"] == "survived")
        excluded = {key: int(case["mutantStatus"] == key) for key in excluded_keys}
        campaign["score"] = {"killed": killed, "survived": survived, "denominator": killed + survived, "ratio": ({"numerator": killed, "denominator": killed + survived} if killed + survived else None), "excluded": excluded}
        refresh_campaign_ids(campaign)
        expect_semantic_rejection(lambda value: validate_campaign_semantics(value, check_artifact_graph=False), campaign, f"{case['id']}: contradictory status was accepted")
    materialized_schedule_reports: list[dict[str, Any]] = []
    for case in data["scheduleCases"]:
        executed: list[str] = []
        killing: list[str] = []
        for test in case["manifestOrder"]:
            executed.append(test["id"])
            if test["outcome"] == "distinguish":
                killing.append(test["id"])
                if case["mode"] == "first-kill":
                    break
        status = "killed" if killing else "survived"
        ok(status == case["expected"]["status"] and executed == case["expected"]["executed"] and killing == case["expected"]["killingTests"], f"{case['id']}: scheduling semantics")
        campaign = deepcopy(base)
        campaign["scheduleMode"] = case["mode"]
        campaign["selectedTestIds"] = [item["id"] for item in case["manifestOrder"]]
        campaign["campaignId"] = digest("k-in-k/mutation-campaign/v1", {"manifestDigest": campaign["manifestDigest"], "operator": campaign["operator"], "scheduleMode": campaign["scheduleMode"]})
        mutant = campaign["mutants"][0]
        mutant["status"] = status
        mutant["tests"] = []
        mutant["oracleResults"] = []
        for item in case["manifestOrder"]:
            was_executed = item["id"] in executed
            distinguished = was_executed and item["outcome"] == "distinguish"
            oracle_outcome = "distinguish" if distinguished else ("agree" if was_executed else "skipped")
            test_status = "kill" if distinguished else ("agree" if was_executed else "skipped")
            oracle_id = f"schedule-{item['id']}"
            mutant["tests"].append({"id": item["id"], "status": test_status, "selected": was_executed, "boundsDigest": "24" * 32, "invocationDigest": digest("k-in-k/test-invocation/v1", {"mode": case["mode"], "testId": item["id"]}), "oracleIds": [oracle_id]})
            oracle_result = {"oracleId": oracle_id, "kind": "final-result", "projectionDigest": "21" * 32, "comparisonDigest": "22" * 32, "outcome": oracle_outcome, "operands": [], "witnessDigest": None, "failure": None}
            set_oracle_normal_operands(oracle_result, "23" * 32 if was_executed else None, ("29" * 32 if distinguished else "23" * 32) if was_executed else None)
            mutant["oracleResults"].append(oracle_result)
        campaign["baseline"]["tests"] = [{"id": item["id"], "status": "agree", "oracleIds": [f"schedule-{item['id']}"]} for item in case["manifestOrder"]]
        campaign["baseline"]["oracleResults"] = [{"oracleId": f"schedule-{item['id']}", "kind": "final-result", "projectionDigest": "21" * 32, "comparisonDigest": "22" * 32, "outcome": "accepted", "operand": {"side": "baseline", "terminal": {"kind": "normal", "artifact": {"role": "oracle-value", "digest": "23" * 32}}}, "failure": None} for item in case["manifestOrder"]]
        synthetic_corpus = {"definitionDigest": campaign["baseline"]["definitionDigest"], "bounds": deepcopy(mutant["bounds"]), "tests": [{"testId": test["id"], "programDigest": digest("k-in-k/test-program/v1", {"testId": test["id"]}), "optionsDigest": "55" * 32} for test in mutant["tests"]]}
        synthetic_corpus["manifestId"] = digest("k-in-k/synthetic-corpus-manifest/v1", synthetic_corpus)
        used_oracle_ids = [oracle_id for test in mutant["tests"] for oracle_id in test["oracleIds"]]
        synthetic_oracles = [{"oracleId": oracle_id, "version": 1, "kind": "final-result", "projectionDigest": "21" * 32, "comparisonDigest": "22" * 32, "crashPolicy": "semantic-crash-distinguishes", "baselineTerminalPolicy": "normal-required", "artifacts": [{"role": "oracle-projection", "digest": "21" * 32}, {"role": "oracle-comparison", "digest": "22" * 32}]} for oracle_id in used_oracle_ids]
        synthetic_manifest = {"schemaVersion": 1, "artifactCatalogDigest": load(FIXTURES / "artifact-catalog.json")["catalogId"], "definitionDigest": campaign["baseline"]["definitionDigest"], "operatorDigest": campaign["operator"]["digest"], "siteRegistryDigest": load(FIXTURES / "mutation-manifest.json")["siteRegistryDigest"], "corpusManifestDigest": synthetic_corpus["manifestId"], "loweringProfileDigest": load(FIXTURES / "mutation-manifest.json")["loweringProfileDigest"], "loweringEvidence": [], "oracles": synthetic_oracles, "tests": [{"testId": test["id"], "programDigest": synthetic_corpus["tests"][index]["programDigest"], "optionsDigest": synthetic_corpus["tests"][index]["optionsDigest"], "boundsDigest": test["boundsDigest"], "invocationDigest": test["invocationDigest"], "oracleIds": test["oracleIds"], "patternQueries": []} for index, test in enumerate(mutant["tests"])]}
        synthetic_manifest["manifestId"] = digest("k-in-k/mutation-manifest/v1", synthetic_manifest)
        campaign["manifestDigest"] = synthetic_manifest["manifestId"]
        registry = mutation_package_registry()
        registry["manifests"][synthetic_manifest["manifestId"]] = synthetic_manifest
        registry["corpora"][synthetic_corpus["manifestId"]] = synthetic_corpus
        refresh_campaign_ids(campaign)
        validate_schema(campaign, schema, schema_path, schema)
        validate_campaign_semantics(campaign, registry=registry, check_artifact_graph=False)
        materialized_schedule_reports.append(campaign)
    ok([report["mutants"][0]["status"] for report in materialized_schedule_reports] == ["killed", "killed"], "first-kill/full materialized reports disagree on classification")
    ok(materialized_schedule_reports[0]["reportId"] != materialized_schedule_reports[1]["reportId"], "distinct schedule reports collapsed to one ID")

    for case in data["candidateRejectionCases"]:
        campaign = deepcopy(base)
        candidate = campaign["generation"]["candidates"][0]
        if case["status"] == "duplicate":
            rejected_candidate = candidate
            rejected_origins = [candidate["originInstances"][0]["instanceId"]]
        else:
            rejected_candidate = deepcopy(candidate)
            rejected_candidate["patch"]["edits"] = [deepcopy(rejected_candidate["patch"]["edits"][0])]
            rejected_candidate["patch"]["edits"][0]["value"] = {"kind": "term", "term": {"encoding": "portable-term-v1", "sort": "Address", "node": {"kind": "token", "text": "0"}}}
            rejected_candidate["patch"]["edits"][0]["editId"] = digest("k-in-k/edit/v1", value_without(rejected_candidate["patch"]["edits"][0], "editId"))
            rejected_candidate["patch"]["patchId"] = digest("k-in-k/patch/v1", {"schemaVersion": 1, "edits": rejected_candidate["patch"]["edits"]})
            for origin in rejected_candidate["originInstances"]:
                origin["editReceipts"] = [deepcopy(origin["editReceipts"][0])]
                origin["editReceipts"][0]["editId"] = rejected_candidate["patch"]["edits"][0]["editId"]
                payload = mutation_instance_payload(campaign["operator"], campaign["baseline"]["definitionDigest"], campaign["generation"]["policy"], origin, rejected_candidate["patch"]["patchId"])
                origin["instanceId"] = digest("k-in-k/instance/v1", payload)
            candidate_payload = {"operatorId": campaign["operator"]["id"], "operatorVersion": campaign["operator"]["version"], "baselineDefinitionDigest": campaign["baseline"]["definitionDigest"], "patchId": rejected_candidate["patch"]["patchId"]}
            rejected_candidate["candidateId"] = digest("k-in-k/candidate/v1", candidate_payload)
            campaign["generation"]["candidates"] = [rejected_candidate]
            campaign["mutants"] = []
            campaign["score"].update({"killed": 0, "survived": 0, "denominator": 0, "ratio": None})
            rejected_origins = [origin["instanceId"] for origin in rejected_candidate["originInstances"]]
        campaign["candidateRejections"] = [{"status": case["status"], "patchId": rejected_candidate["patch"]["patchId"], "originInstanceIds": rejected_origins, "failures": [case["failure"]]}]
        campaign["score"]["excluded"][case["expected"]["excludedKey"]] = case["expected"]["excludedCount"]
        campaign["reportId"] = digest("k-in-k/mutation-report/v1", value_without(campaign, "reportId"))
        validate_schema(campaign, schema, schema_path, schema)
        validate_campaign_semantics(campaign)
        ok(len(campaign["mutants"]) == case["expected"]["mutantCount"], f"{case['id']}: rejection created an output mutant")

    missing_disposition = deepcopy(base)
    missing_disposition["mutants"] = []
    missing_disposition["score"] = {"killed": 0, "survived": 0, "denominator": 0, "ratio": None, "excluded": {key: 0 for key in excluded_keys}}
    missing_disposition["reportId"] = digest("k-in-k/mutation-report/v1", value_without(missing_disposition, "reportId"))
    expect_semantic_rejection(validate_campaign_semantics, missing_disposition, "complete campaign silently omitted a candidate disposition")
    for case in data["scoreCases"]:
        killed = case["statuses"].count("killed")
        survived = case["statuses"].count("survived")
        denominator = killed + survived
        if denominator:
            divisor = math.gcd(killed, denominator)
            ratio = {"numerator": killed // divisor, "denominator": denominator // divisor}
        else:
            ratio = None
        derived = {"killed": killed, "survived": survived, "denominator": denominator, "ratio": ratio}
        ok(derived == case["expected"], "exact mutation score vector")


def verify_cross_feature() -> None:
    for case in load(VECTORS / "cross-feature-vectors.json")["cases"]:
        expected = case["expected"]
        if case["id"] == "unchanged-final-result-killed-by-event-pattern":
            ok(case["baseline"]["finalResultDigest"] == case["mutant"]["finalResultDigest"], "cross vector final result changed")
            ok(any(item["kind"] == "execution-pattern" and item["outcome"] == "distinguish" for item in case["oracles"]), "cross vector lacks pattern distinction")
            ok(expected["mutantStatus"] == "killed" and expected["scoreEntries"] == 1, "cross vector kill classification")
        elif case["id"] == "observation-does-not-retarget-mutation":
            ok(case["baselineObservationRevision"] == case["mutantObservationRevision"], "observation revisions differ")
            ok(set(case["eventOriginalLineages"]) <= set(case["mutationTargetLineages"]), "event origin lost mutation target")
        else:
            ok(expected["mutantStatus"] == "unknown" and not expected["scoreIncluded"], "unknown pattern incorrectly scored")


def main() -> int:
    json_files = sorted(PACKAGE.rglob("*.json"))
    for path in json_files:
        load(path)
    ok(bool(json_files), "no JSON artifacts found")
    validate_fixture("semantic-identity.json", "semantic-identity.schema.json")
    validate_fixture("patch.json", "patch.schema.json")
    validate_fixture("event-trace.json", "event-trace.schema.json")
    validate_fixture("pattern-result.json", "pattern-result.schema.json")
    validate_fixture("mutation-campaign.json", "mutation-campaign.schema.json")
    verify_interchange_artifacts()
    verify_inventory()
    verify_completion_checklist()
    verify_closure_matrix()
    verify_taxonomy()
    verify_lowering_proof_protocol()
    verify_canonicalization()
    verify_identity()
    verify_bag13_local_well_formedness()
    verify_execution()
    verify_bag11_adversaries()
    verify_corpus_vectors()
    verify_observation()
    verify_mutation()
    verify_patch_applications()
    verify_bag12_package(PACKAGE, {
        "ok": ok,
        "expect_schema_rejection": expect_schema_rejection,
        "validate_pattern_result_semantics": validate_pattern_result_semantics,
    })
    verify_bag14_package(PACKAGE, {
        "ok": ok,
        "expect_schema_rejection": expect_schema_rejection,
    })
    verify_bag15_package(PACKAGE, {
        "ok": ok,
        "expect_schema_rejection": expect_schema_rejection,
        "validate_pattern_result_semantics": validate_pattern_result_semantics,
    })
    verify_bag16_package(PACKAGE, {
        "ok": ok,
        "expect_schema_rejection": expect_schema_rejection,
    })
    verify_semantic_termination_and_crash_oracle()
    verify_policy_generation_fixtures()
    verify_cross_feature()
    print(f"PASS backend-agnostic-k-in-k-v1: {CHECKS} zero-backend checks")
    return 0


if __name__ == "__main__":
    try:
        if sys.argv[1:] == ["--official-only"]:
            verify_official_draft_2020_12(official_fixture_schemas(), official_package_schemas())
            print("PASS official Draft 2020-12 schema and fixture validation")
            raise SystemExit(0)
        if sys.argv[1:]:
            raise SystemExit("usage: verify.py [--official-only]")
        raise SystemExit(main())
    except (AssertionError, KeyError, ValueError, json.JSONDecodeError) as error:
        print(f"FAIL backend-agnostic-k-in-k-v1: {error}", file=sys.stderr)
        raise SystemExit(1)
