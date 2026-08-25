#!/usr/bin/env python3
"""Static and cached checks for production-bound R3-G-05C graph deltas."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


SCHEMA = "R3-G-05-existing-graph-projection-v1"
FIELDS = {
    "wrong-generated-cell-metadata": "generatedCell.metadata",
    "wrong-parent-production": "parent.production",
    "wrong-cell-production": "generatedCell.production",
    "wrong-left-marker-production": "leftMarker.production",
    "wrong-right-marker-production": "rightMarker.production",
    "wrong-left-marker-term": "leftMarker.term",
    "wrong-right-marker-term": "rightMarker.term",
    "wrong-append-production": "append.production",
    "wrong-singleton-production": "singleton.production",
    "wrong-event-production": "event.production",
    "wrong-origin-production": "origin.production",
    "wrong-rewrite-metadata": "rewrite.metadata",
    "wrong-variable-name": "variable.name",
    "wrong-variable-sort": "variable.sort",
    "wrong-variable-metadata": "variable.metadata",
    "wrong-token-sort": "payloadToken.sort",
    "wrong-token-metadata": "payloadToken.metadata",
    "wrong-payload-lineage": "payload.lineage",
    "wrong-payload-label": "payload.label",
    "wrong-payload-module": "payload.module",
    "wrong-payload-source": "payload.source",
    "wrong-payload-location": "payload.location",
    "partial-graph": "traceGraph.partial",
    "duplicate-graph": "traceGraph.duplicate",
    "extra-graph": "traceGraph.extra",
}
MODES = tuple(f"{base}-{side}" for base in FIELDS for side in ("first", "second"))
PRIMITIVE_FIELDS = frozenset(
    field for field in FIELDS.values() if not field.startswith("traceGraph."))


def digest_text(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def parse_fingerprint_map(value: object, mode: str) -> dict[str, str]:
    if not isinstance(value, str):
        raise SystemExit(f"structured projection map is not a string: {mode}")
    if not value:
        return {}
    result: dict[str, str] = {}
    for entry in value.split(","):
        try:
            path, fingerprint = entry.split(":", 1)
        except ValueError:
            raise SystemExit(f"malformed structured projection map: {mode}") from None
        if path in result or len(fingerprint) != 64:
            raise SystemExit(f"duplicate/malformed projection field: {mode}")
        result[path] = fingerprint
    return result


def static_binding_check(java_path: Path | None = None) -> None:
    """Reject the 2927325 name-salted, whole-rule, parallel-toy pattern."""
    if java_path is None:
        java_path = (Path(__file__).resolve().parent
                     / "src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java")
    java = java_path.read_text(encoding="utf-8")
    required = (
        "record ExistingGraphSnapshot", "ExistingGraphSnapshot.capture(",
        "record StructuredGraphDelta", "construction.before.delta(construction.after)",
        "delta.changedPaths.equals(List.of(trace.mutationStructuralField))",
        "sha256(delta.canonical())", "record MalformedExistingConstruction",
        "exactExistingParent(prepared, prepared.parent)",
        "mutationHostIndependentRejection = true",
        "fieldFingerprintMap()",
        "actualMalformedGraph", "hostRequire(resolved == item.parent",
        "both parent layers do not equal independently declared production authority",
        '"insert", "parent.child[2]"', '"remove", removalPath',
        "trace.pairTransactionInvocationCount++",
        "validatePreparedAlreadyPresent(List.of(malformedPrepared))",
        "replaceProductionAuthority", "replaceProductionMetadata",
        "narrow production mutation changed sort or metadata",
        "productionStructure(typedProduction)",
        ".remove(Att.SORT(), Sort.class).toString()",
        "rewrite.att().equals(KRewrite(before, after).att())",
    )
    for witness in required:
        if witness not in java:
            raise SystemExit(f"production-bound mutation witness missing: {witness}")
    malformed = java[java.index("private MalformedExistingConstruction constructMalformedExistingInput"):
                     java.index("private static TermPath childPath")]
    if "Att.empty()" in malformed:
        raise SystemExit("broad Att.empty() mutation remains in the production mutator")
    fingerprint = java[java.index("trace.mutationFingerprint ="):
                       java.index("trace.mutationProductionMutatorBound", java.index("trace.mutationFingerprint ="))]
    if "mutationStructuralField" in fingerprint or "memberIndex" in fingerprint:
        raise SystemExit("mutation fingerprint is salted by a claim or member index")
    if "originalTarget.body" in java or "mutatedTarget.body" in java:
        raise SystemExit("whole-rule-only mutation fingerprint remains")
    negative = java[java.index("private Definition malformedExistingNegative"):
                    java.index("private MalformedExistingConstruction constructMalformedExistingInput")]
    if "executePairTransaction(" in negative:
        raise SystemExit("malformed-existing path can enter the pair transaction")


def cached_record_check(records: Path) -> None:
    fingerprints: set[str] = set()
    graph_deltas: set[tuple[str, str]] = set()
    cases: set[tuple[int, str]] = set()
    for mode in MODES:
        path = records / f"negative-{mode}.json"
        if not path.is_file():
            raise SystemExit(f"missing structured mutation record: {mode}")
        record = json.loads(path.read_text(encoding="utf-8"))
        base, side = mode.rsplit("-", 1)
        member = 0 if side == "first" else 1
        field = FIELDS[base]
        if record.get("mutationProjectionSchema") != SCHEMA:
            raise SystemExit(f"mutation projection schema mismatch: {mode}")
        operation = record.get("mutationStructuralOperation")
        changed_path = record.get("mutationChangedFieldPaths")
        if record.get("mutationStructuralField") != field:
            raise SystemExit(f"claimed structured field mismatch: {mode}")
        if record.get("mutationMemberIndex") != member:
            raise SystemExit(f"mutation member mismatch: {mode}")
        before_structure = record.get("mutationBeforeStructure")
        after_structure = record.get("mutationAfterStructure")
        before_map = parse_fingerprint_map(
            record.get("mutationBeforeProjectionFingerprintMap"), mode)
        after_map = parse_fingerprint_map(
            record.get("mutationAfterProjectionFingerprintMap"), mode)
        if before_structure != "exact" or set(before_map) != PRIMITIVE_FIELDS:
            raise SystemExit(f"valid structured before projection is incomplete: {mode}")
        field_before = record.get("mutationFieldBeforeFingerprint")
        field_after = record.get("mutationFieldAfterFingerprint")
        graph_before = record.get("mutationBeforeFingerprint")
        graph_after = record.get("mutationAfterFingerprint")
        fingerprint = record.get("mutationFingerprint")
        values = (field_before, field_after, graph_before, graph_after, fingerprint)
        if not all(isinstance(value, str) and len(value) == 64 for value in values):
            raise SystemExit(f"structured delta fingerprints are malformed: {mode}")
        if field_before == field_after or graph_before == graph_after:
            raise SystemExit(f"structured delta did not change actual graph state: {mode}")
        if field.startswith("traceGraph."):
            expected_structure = field.removeprefix("traceGraph.")
            expected_operation = "remove" if expected_structure == "partial" else "insert"
            path_valid = (changed_path.startswith(
                "generatedCell.child[1].rewrite.after.")
                if expected_structure == "partial"
                else changed_path == "parent.child[2]")
            reference = record.get("mutationReferenceFragmentFingerprint")
            if (after_structure != expected_structure or after_map
                    or operation != expected_operation or not path_valid
                    or not isinstance(reference, str) or len(reference) != 64
                    or (expected_structure == "partial"
                        and field_after != digest_text("absent"))
                    or (expected_structure in ("duplicate", "extra")
                        and field_before != digest_text("absent"))
                    or (expected_structure == "duplicate" and field_after != reference)
                    or (expected_structure == "extra" and field_after == reference)):
                raise SystemExit(f"structural graph operation projection mismatch: {mode}")
        else:
            changed = sorted(
                path for path in PRIMITIVE_FIELDS
                if before_map.get(path) != after_map.get(path))
            if (operation != "replace" or changed_path != field
                    or after_structure != "exact" or set(after_map) != PRIMITIVE_FIELDS
                    or changed != [field]
                    or field_before != before_map[field]
                    or field_after != after_map[field]):
                raise SystemExit(f"structured before/after delta mismatch: {mode}")
        expected = digest_text(
            f"{operation}|{changed_path}|{field_before}|{field_after}|"
            f"{graph_before}|{graph_after}")
        if fingerprint != expected:
            raise SystemExit(f"mutation fingerprint is not derived from actual delta: {mode}")
        if fingerprint in fingerprints or (graph_before, graph_after) in graph_deltas:
            raise SystemExit(f"actual production mutation alias: {mode}")
        fingerprints.add(fingerprint)
        graph_deltas.add((graph_before, graph_after))
        if (member, field) in cases:
            raise SystemExit(f"duplicate structured mutation case: {mode}")
        cases.add((member, field))
        if (record.get("mutationProductionMutatorBound") is not True
                or record.get("mutationKConflictBeforePairTransaction") is not True
                or record.get("mutationHostIndependentRejection") is not True):
            raise SystemExit(f"K/host/production binding facts are incomplete: {mode}")
        if any(record.get(name) != 0 for name in (
            "pairTransactionInvocationCount", "ruleApplicationCount",
            "ruleTransformerTraversalCount")):
            raise SystemExit(f"mutation performed a pair transaction, edit, or traversal: {mode}")
        if record.get("outputDefinitionConstructed") or record.get("backendConstructed"):
            raise SystemExit(f"mutation constructed output/backend state: {mode}")
    if (len(fingerprints) != len(MODES) or len(graph_deltas) != len(MODES)
            or len(cases) != len(MODES)):
        raise SystemExit("cached structured mutation matrix is not exact")


def cached_validator_self_test(records: Path) -> None:
    """Exercise claim mismatch, host-fact, and actual-delta alias rejection."""
    records.mkdir(parents=True)
    for ordinal, mode in enumerate(MODES):
        base, side = mode.rsplit("-", 1)
        field = FIELDS[base]
        field_before = digest_text(f"field-before:{ordinal}")
        field_after = digest_text(f"field-after:{ordinal}")
        graph_before = digest_text(f"graph-before:{ordinal}")
        graph_after = digest_text(f"graph-after:{ordinal}")
        record = {
            "mutationProjectionSchema": SCHEMA,
            "mutationStructuralField": field,
            "mutationChangedFieldPaths": field,
            "mutationStructuralOperation": "replace",
            "mutationMemberIndex": 0 if side == "first" else 1,
            "mutationBeforeStructure": "exact",
            "mutationAfterStructure": (
                field.removeprefix("traceGraph.")
                if field.startswith("traceGraph.") else "exact"),
            "mutationBeforeProjectionFingerprintMap": "",
            "mutationAfterProjectionFingerprintMap": "",
            "mutationFieldBeforeFingerprint": field_before,
            "mutationFieldAfterFingerprint": field_after,
            "mutationBeforeFingerprint": graph_before,
            "mutationAfterFingerprint": graph_after,
            "mutationFingerprint": "",
            "mutationProductionMutatorBound": True,
            "mutationKConflictBeforePairTransaction": True,
            "mutationHostIndependentRejection": True,
            "pairTransactionInvocationCount": 0,
            "ruleApplicationCount": 0,
            "ruleTransformerTraversalCount": 0,
            "outputDefinitionConstructed": False,
            "backendConstructed": False,
        }
        before_map = {
            name: digest_text(f"before:{ordinal}:{name}")
            for name in sorted(PRIMITIVE_FIELDS)
        }
        after_map = dict(before_map)
        if field.startswith("traceGraph."):
            structure = field.removeprefix("traceGraph.")
            record["mutationStructuralOperation"] = (
                "remove" if structure == "partial" else "insert")
            record["mutationChangedFieldPaths"] = (
                "generatedCell.child[1].rewrite.after.cPathNil.child[1]"
                if structure == "partial" else "parent.child[2]")
            record["mutationReferenceFragmentFingerprint"] = digest_text(
                f"reference:{ordinal}")
            if structure == "partial":
                record["mutationFieldAfterFingerprint"] = digest_text("absent")
            else:
                record["mutationFieldBeforeFingerprint"] = digest_text("absent")
                record["mutationFieldAfterFingerprint"] = (
                    record["mutationReferenceFragmentFingerprint"]
                    if structure == "duplicate" else digest_text(f"extra:{ordinal}"))
        else:
            record["mutationReferenceFragmentFingerprint"] = digest_text(
                f"reference:{ordinal}")
            after_map[field] = record["mutationFieldAfterFingerprint"]
            before_map[field] = record["mutationFieldBeforeFingerprint"]
        record["mutationBeforeProjectionFingerprintMap"] = ",".join(
            f"{name}:{value}" for name, value in before_map.items())
        record["mutationAfterProjectionFingerprintMap"] = (
            "" if field.startswith("traceGraph.") else ",".join(
                f"{name}:{value}" for name, value in after_map.items()))
        record["mutationFingerprint"] = digest_text(
            f'{record["mutationStructuralOperation"]}|'
            f'{record["mutationChangedFieldPaths"]}|'
            f'{record["mutationFieldBeforeFingerprint"]}|'
            f'{record["mutationFieldAfterFingerprint"]}|{graph_before}|{graph_after}')
        (records / f"negative-{mode}.json").write_text(
            json.dumps(record), encoding="utf-8")
    cached_record_check(records)

    def rejected(mode: str, field: str, value: object) -> None:
        path = records / f"negative-{mode}.json"
        record = json.loads(path.read_text(encoding="utf-8"))
        original = record[field]
        record[field] = value
        path.write_text(json.dumps(record), encoding="utf-8")
        try:
            cached_record_check(records)
        except SystemExit:
            pass
        else:
            raise AssertionError(f"cached mutation validator accepted {field} mutation")
        record[field] = original
        path.write_text(json.dumps(record), encoding="utf-8")

    rejected(MODES[0], "mutationChangedFieldPaths", "claimed.alias")
    rejected(MODES[0], "mutationHostIndependentRejection", False)
    first = json.loads((records / f"negative-{MODES[0]}.json").read_text(encoding="utf-8"))
    second_path = records / f"negative-{MODES[1]}.json"
    second = json.loads(second_path.read_text(encoding="utf-8"))
    for key in ("mutationBeforeFingerprint", "mutationAfterFingerprint"):
        second[key] = first[key]
    second["mutationFingerprint"] = digest_text(
        f'{second["mutationStructuralOperation"]}|{second["mutationChangedFieldPaths"]}|'
        f'{second["mutationFieldBeforeFingerprint"]}|'
        f'{second["mutationFieldAfterFingerprint"]}|{second["mutationBeforeFingerprint"]}|'
        f'{second["mutationAfterFingerprint"]}')
    second_path.write_text(json.dumps(second), encoding="utf-8")
    try:
        cached_record_check(records)
    except SystemExit:
        pass
    else:
        raise AssertionError("cached mutation validator accepted an actual graph-delta alias")


def main() -> None:
    static_binding_check()
    if len(sys.argv) == 2:
        cached_record_check(Path(sys.argv[1]).resolve())
    elif len(sys.argv) != 1:
        raise SystemExit("usage: mutation_sensitivity.py [RECORD_DIRECTORY]")
    print(f"R3-G-05 production-bound mutation sensitivity: pass ({len(MODES)} cases)")


if __name__ == "__main__":
    main()
