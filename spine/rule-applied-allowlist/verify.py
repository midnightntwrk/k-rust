#!/usr/bin/env python3
"""Checkout-stable, zero-backend verifier for committed R3-G-05 evidence."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import project_runtime as runtime_projector
import mutation_sensitivity
from cache_integrity import (
    EXACT_FINAL_TIMEOUT_REPORT_WITNESS,
    EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION,
    EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
    require_exact_timeout_report,
    require_exact_wall_timeout,
)


ACTIVATION = "2d74814f561d17922384db3d8f21ffba9c2eeae0"
REPAIR_ACTIVATION = "6f5cff55845ff94aa96884dec3bd7c6b1de92cc2"
METADATA_REPAIR_ACTIVATION = "2c79c78c1dea7611adf1d11ab2a50c1a309ad90c"
STRUCTURAL_REPAIR_ACTIVATION = "52f0d3b4b3b6b81100d09d080b55ae5eafede698"
LAUNCHER_REPAIR_ACTIVATION = "c76b4fa2169b7f02de3856c8b67673be2756938f"
SECURE_PUBLICATION_REPAIR_ACTIVATION = "3fc61ff24bea53f519005da66a98a6f148c00c8a"
FIRST_WRITER_REAPING_REPAIR_ACTIVATION = "7bba98ba9ccb14c91c443f9a9f99c6c9154d8aa4"
WATCHDOG_IDENTITY_REPAIR_ACTIVATION = "de8e5a89b6e0bfc51b4fc5f15581368760f8d630"
PRIVATE_GATE_REPAIR_ACTIVATION = "6c0c5dc6bc1c78b9101d1f46cf08dccb4bec2761"
STOPPED_PROCESS_REPAIR_ACTIVATION = "9bcb273863027af51a9381ecb02edace9a896adf"
DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION = "698d92123d75b40cd5b12d19244829cae308f426"
PARSER_ADVERSARY_REPAIR_ACTIVATION = "4006fac28ec20f47f136593fd135da36ccee4ea7"
NESTED_DESCRIPTOR_REPAIR_ACTIVATION = "dfadc62bb090580a32f2b0f2a95e74eaefdd7e4d"
CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION = "f5e07a4f47929ebbe76f9c5eb22f73ff39e65745"
FINAL_2048_HEAP_CYCLE_ACTIVATION = "d995a8cc93462a43260bdadba256a90d61b0ffe2"
SCHEMA = "KRuleAppliedAllowlist-v1"
TRANSFORMATION = "exact-two-rule-applied-allowlist@1"
EXPECTED_FAILURES = {
    "zero-target",
    "one-target",
    "three-target",
    "duplicate-target",
    "noncanonical-member-order",
    "stale-first",
    "stale-second",
    "unsupported-path-first",
    "unsupported-path-second",
    "conflict-existing-first",
    "conflict-existing-second",
    "partial-existing-first",
    "partial-existing-second",
    "false-already-present",
    "false-apply-existing",
    "unsupported-shape",
    "forced-preparation-failure-first",
    "forced-preparation-failure-second",
    "missing-cell-metadata-first",
    "missing-cell-metadata-second",
    "ambiguous-cell-metadata-first",
    "ambiguous-cell-metadata-second",
    "missing-constructor-metadata-first",
    "missing-constructor-metadata-second",
    "ambiguous-constructor-metadata-first",
    "ambiguous-constructor-metadata-second",
    "unknown-constructor-first",
    "unknown-constructor-second",
    "sort-invalid-first",
    "sort-invalid-second",
    "freshness-invalid-first",
    "freshness-invalid-second",
    "payload-invalid-first",
    "payload-invalid-second",
    "malformed-result",
    "multiple-result",
    "residual-result",
    "unknown-result",
    "noncanonical-result",
    "fixture-literal-scan",
    "wrong-generated-cell-metadata-first", "wrong-generated-cell-metadata-second",
    "wrong-parent-production-first", "wrong-parent-production-second",
    "wrong-cell-production-first", "wrong-cell-production-second",
    "wrong-left-marker-production-first", "wrong-left-marker-production-second",
    "wrong-right-marker-production-first", "wrong-right-marker-production-second",
    "wrong-left-marker-term-first", "wrong-left-marker-term-second",
    "wrong-right-marker-term-first", "wrong-right-marker-term-second",
    "wrong-append-production-first", "wrong-append-production-second",
    "wrong-singleton-production-first", "wrong-singleton-production-second",
    "wrong-event-production-first", "wrong-event-production-second",
    "wrong-origin-production-first", "wrong-origin-production-second",
    "wrong-rewrite-metadata-first", "wrong-rewrite-metadata-second",
    "wrong-variable-name-first", "wrong-variable-name-second",
    "wrong-variable-sort-first", "wrong-variable-sort-second",
    "wrong-variable-metadata-first", "wrong-variable-metadata-second",
    "wrong-token-sort-first", "wrong-token-sort-second",
    "wrong-token-metadata-first", "wrong-token-metadata-second",
    "wrong-payload-lineage-first", "wrong-payload-lineage-second",
    "wrong-payload-label-first", "wrong-payload-label-second",
    "wrong-payload-module-first", "wrong-payload-module-second",
    "wrong-payload-source-first", "wrong-payload-source-second",
    "wrong-payload-location-first", "wrong-payload-location-second",
    "partial-graph-first", "partial-graph-second",
    "duplicate-graph-first", "duplicate-graph-second",
    "extra-graph-first", "extra-graph-second",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def runtime_selftest(task: Path) -> None:
    text = (task / "fixtures/runtime-two-event.pretty").read_text(encoding="utf-8")
    valid = runtime_projector.project(text, 2, False)
    require(len(valid["trace"]) == 2, "valid runtime pair did not project")
    start = text.index("<trace>") + len("<trace>")
    end = text.index("</trace>")
    prefix, suffix = text[:start], text[end:]
    origin = 'ruleOrigin ( "id" , "label" , "module" , "source" , "location" )'
    first = runtime_projector.EVENT.match(text[start:end])
    require(first is not None, "valid runtime does not start with an event")
    mutations = (
        prefix + "\nruleApplied ( .K ) ruleApplied ( .K )\n" + origin + " " + origin + "\n" + suffix,
        text[:end] + "\n.List\n" + text[end:],
        text.replace("ListItem ( ruleApplied", "ruleApplied", 1),
        prefix + first.group(0) + "\n" + suffix,
    )
    for mutation in mutations:
        try:
            runtime_projector.project(mutation, 2, False)
        except ValueError:
            continue
        raise SystemExit("zero-backend runtime adversary was accepted")


def main(root: Path) -> None:
    task = root / "spine/rule-applied-allowlist"
    evidence = root / "evidence/r3-g-05-atomic-rule-applied-allowlist"
    result_path = evidence / "results.json"
    report_path = evidence / "report.md"
    mutation_sensitivity.static_binding_check()
    require(result_path.is_file() and report_path.is_file(), "R3-G-05 evidence is missing")
    result = json.loads(result_path.read_text(encoding="utf-8"))
    runtime_selftest(task)

    require(result["activationRevision"] == ACTIVATION, "activation pin mismatch")
    require(result["repairActivationRevision"] == REPAIR_ACTIVATION,
            "repair activation pin mismatch")
    require(result["metadataRepairActivationRevision"] == METADATA_REPAIR_ACTIVATION,
            "metadata repair activation pin mismatch")
    require(result["structuralRepairActivationRevision"] == STRUCTURAL_REPAIR_ACTIVATION,
            "structural repair activation pin mismatch")
    require(result["launcherRepairActivationRevision"] == LAUNCHER_REPAIR_ACTIVATION,
            "launcher repair activation pin mismatch")
    require(result["securePublicationRepairActivationRevision"]
            == SECURE_PUBLICATION_REPAIR_ACTIVATION,
            "secure-publication repair activation pin mismatch")
    require(result["firstWriterReapingRepairActivationRevision"]
            == FIRST_WRITER_REAPING_REPAIR_ACTIVATION,
            "first-writer/reaping repair activation pin mismatch")
    require(result["watchdogIdentityRepairActivationRevision"]
            == WATCHDOG_IDENTITY_REPAIR_ACTIVATION,
            "watchdog identity repair activation pin mismatch")
    require(result["privateGateRepairActivationRevision"]
            == PRIVATE_GATE_REPAIR_ACTIVATION,
            "private gate repair activation pin mismatch")
    require(result["stoppedProcessRepairActivationRevision"]
            == STOPPED_PROCESS_REPAIR_ACTIVATION,
            "stopped-process repair activation pin mismatch")
    require(result["driverFailureRecoveryRepairActivationRevision"]
            == DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION,
            "driver/failure-recovery repair activation pin mismatch")
    require(result["parserAdversaryRepairActivationRevision"]
            == PARSER_ADVERSARY_REPAIR_ACTIVATION,
            "parser-adversary repair activation pin mismatch")
    require(result["nestedDescriptorRepairActivationRevision"]
            == NESTED_DESCRIPTOR_REPAIR_ACTIVATION,
            "nested-descriptor repair activation pin mismatch")
    require(result["cleanHeadJavaScratchRepairActivationRevision"]
            == CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION,
            "clean-head/Java-scratch repair activation pin mismatch")
    require(result["final2048HeapCycleActivationRevision"]
            == FINAL_2048_HEAP_CYCLE_ACTIVATION,
            "final 2048 MiB cycle activation pin mismatch")
    require(result["exactFinalTimeoutBindingActivationRevision"]
            == EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION,
            "exact final timeout binding activation pin mismatch")
    require(result["exactTimeoutReportVerificationActivationRevision"]
            == EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
            "exact-timeout report verification activation pin mismatch")
    require(result["startingRevision"] == EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
            "starting revision mismatch")
    implementation_head = result["implementationRevision"]
    require(isinstance(implementation_head, str)
            and re.fullmatch(r"[0-9a-f]{40}", implementation_head) is not None,
            "implementation revision is not an exact commit ID")
    require(result["pins"]["implementationHead"] == implementation_head
            and result["rawRun"]["implementationHead"] == implementation_head,
            "final evidence implementation-head bindings differ")
    require(subprocess.run(
        ["git", "cat-file", "-e", f"{implementation_head}^{{commit}}"], cwd=root,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False).returncode == 0,
        "recorded implementation revision is not an available commit object")
    require(subprocess.run(
        ["git", "merge-base", "--is-ancestor",
         FINAL_2048_HEAP_CYCLE_ACTIVATION, implementation_head], cwd=root,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False).returncode == 0,
        "R3-G-05N activation is not an ancestor of the implementation revision")
    require(subprocess.run(
        ["git", "merge-base", "--is-ancestor",
         EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION, implementation_head], cwd=root,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False).returncode == 0,
        "R3-G-05O activation is not an ancestor of the implementation revision")
    require(subprocess.run(
        ["git", "merge-base", "--is-ancestor",
         EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION, implementation_head], cwd=root,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False).returncode == 0,
        "R3-G-05P activation is not an ancestor of the implementation revision")
    require(result["repositorySnapshots"] == {
        "beforeHead": implementation_head,
        "afterHead": implementation_head,
        "cleanImplementationCheckoutRequiredBeforeReservation": True,
    }, "repository snapshots do not bind the clean implementation revision")
    require(result["contract"]["schema"] == SCHEMA, "schema mismatch")
    require(result["contract"]["transformation"] == TRANSFORMATION, "transformation mismatch")
    require(result["verdict"] == "pass", "committed verdict is not pass")
    require(result["substantiveFullOracleCycleCount"] == 5, "cycle count is not five")
    require(result["cycleHistory"] == [
        {"cycle": 1, "verdict": "failed", "stage": "frontend-setup",
         "step": "driver-compilation", "exitStatus": 1, "finalEvidence": False},
        {"cycle": 2, "verdict": "failed", "stage": "frontend-setup",
         "step": "parser-canonicality-self-test", "exitStatus": 1,
         "finalEvidence": False},
        {"cycle": 3, "verdict": "failed", "stage": "configuration-compile",
         "step": "nested-self-fd-working-directory", "exitStatus": 113,
         "finalEvidence": False},
        {"cycle": 4, "verdict": "failed", "stage": "positive-pair-transactions",
         "step": "nested-krun-java-heap-oom-1536", "exitStatus": 113,
         "finalEvidence": False},
        {"cycle": 5, "verdict": "pass", "finalEvidence": True},
    ], "cycle history does not bind failed cycles 1/2/3/4 and passing cycle 5")
    targets = result["targets"]
    require(len(targets) == 2, "portable target count is not two")
    lineages = [item["lineage"] for item in targets]
    require(lineages == sorted(lineages) and len(set(lineages)) == 2, "target order/distinctness mismatch")
    require({item["label"] for item in targets} == {"bump-state", "drop-state"}, "target labels mismatch")
    require(all(item["source"].startswith("repo://") for item in targets), "nonportable source committed")
    require(all(item["operation"] == "appendGeneratedCellTerm" for item in targets), "operation mismatch")
    require(result["atomicity"] == {
        "candidateCount": 2,
        "validatedOperationCount": 2,
        "applicationCount": 2,
        "changedPrimarySourceRuleCount": 2,
        "singleTransformerTraversal": True,
        "noIntermediateDefinitionExposed": True,
    }, "atomicity evidence mismatch")
    require(result["idempotence"] == {
        "secondPassStatus": "already-present",
        "independentlyValidatedCount": 2,
        "applicationCount": 0,
        "sameDefinitionReference": True,
        "partialInstrumentationRejected": True,
    }, "idempotence evidence mismatch")
    require(set(result["failures"]) == EXPECTED_FAILURES, "failure matrix mismatch")
    require(all(item["status"] == "rejected"
                and item["applicationCount"] == 0
                and item["transformerTraversalCount"] == 0
                and not item["outputDefinitionConstructed"]
                and not item["backendConstructed"]
                for item in result["failures"].values()), "failure atomicity/backend mismatch")
    require(result["mutationSensitivity"] == {
        "caseCount": len(mutation_sensitivity.MODES),
        "distinctStructuralFieldsPerMember": True,
        "distinctMutationFingerprints": True,
        "kConflictBeforePairTransaction": True,
        "hostIndependentRejection": True,
        "actualProductionGraphDeltaValidated": True,
        "aliasRejection": True,
    }, "mutation-sensitivity summary mismatch")
    mutation_fingerprints = set()
    for mode in mutation_sensitivity.MODES:
        item = result["failures"][mode]
        base, side = mode.rsplit("-", 1)
        field = mutation_sensitivity.FIELDS[base]
        before_map = mutation_sensitivity.parse_fingerprint_map(
            item["mutationBeforeProjectionFingerprintMap"], mode)
        after_map = mutation_sensitivity.parse_fingerprint_map(
            item["mutationAfterProjectionFingerprintMap"], mode)
        if field.startswith("traceGraph."):
            structure = field.removeprefix("traceGraph.")
            expected_operation = "remove" if structure == "partial" else "insert"
            changed_path = item["mutationChangedFieldPaths"]
            path_valid = (changed_path.startswith(
                "generatedCell.child[1].rewrite.after.")
                if structure == "partial" else changed_path == "parent.child[2]")
            reference = item["mutationReferenceFragmentFingerprint"]
            projection_valid = (
                item["mutationBeforeStructure"] == "exact"
                and item["mutationAfterStructure"] == structure
                and set(before_map) == mutation_sensitivity.PRIMITIVE_FIELDS
                and not after_map
                and item["mutationStructuralOperation"] == expected_operation
                and path_valid
                and isinstance(reference, str) and len(reference) == 64
                and (structure != "partial" or item["mutationFieldAfterFingerprint"]
                     == mutation_sensitivity.digest_text("absent"))
                and (structure not in ("duplicate", "extra")
                     or item["mutationFieldBeforeFingerprint"]
                     == mutation_sensitivity.digest_text("absent"))
                and (structure != "duplicate"
                     or item["mutationFieldAfterFingerprint"] == reference)
                and (structure != "extra"
                     or item["mutationFieldAfterFingerprint"] != reference))
        else:
            changed = sorted(
                path for path in mutation_sensitivity.PRIMITIVE_FIELDS
                if before_map.get(path) != after_map.get(path))
            projection_valid = (
                item["mutationBeforeStructure"] == "exact"
                and item["mutationAfterStructure"] == "exact"
                and item["mutationStructuralOperation"] == "replace"
                and item["mutationChangedFieldPaths"] == field
                and set(before_map) == mutation_sensitivity.PRIMITIVE_FIELDS
                and set(after_map) == mutation_sensitivity.PRIMITIVE_FIELDS
                and changed == [field]
                and item["mutationFieldBeforeFingerprint"] == before_map[field]
                and item["mutationFieldAfterFingerprint"] == after_map[field])
        require(item["mutationStructuralField"] == mutation_sensitivity.FIELDS[base]
                and item["mutationProjectionSchema"] == mutation_sensitivity.SCHEMA
                and item["mutationMemberIndex"] == (0 if side == "first" else 1)
                and item["mutationFieldBeforeFingerprint"]
                    != item["mutationFieldAfterFingerprint"]
                and item["mutationBeforeFingerprint"] != item["mutationAfterFingerprint"]
                and item["productionMutatorBound"]
                and item["pairTransactionInvocationCount"] == 0
                and projection_valid
                and item["kConflictBeforePairTransaction"]
                and item["hostIndependentRejection"],
                f"structured mutation evidence mismatch: {mode}")
        fingerprint = item["mutationFingerprint"]
        expected_fingerprint = mutation_sensitivity.digest_text(
            f'{item["mutationStructuralOperation"]}|'
            f'{item["mutationChangedFieldPaths"]}|'
            f'{item["mutationFieldBeforeFingerprint"]}|'
            f'{item["mutationFieldAfterFingerprint"]}|'
            f'{item["mutationBeforeFingerprint"]}|'
            f'{item["mutationAfterFingerprint"]}')
        require(isinstance(fingerprint, str) and len(fingerprint) == 64
                and fingerprint == expected_fingerprint
                and fingerprint not in mutation_fingerprints,
                f"duplicate/malformed mutation fingerprint: {mode}")
        mutation_fingerprints.add(fingerprint)
    require(result["zeroBackendAdversarial"]["runtimeProjectorCaseCount"] == 4,
            "zero-backend runtime case count mismatch")
    require(result["zeroBackendAdversarial"]["nestedDescriptorPathProcessCases"] == 12
            and result["zeroBackendAdversarial"]["cleanCheckoutRefusalCases"] == 4
            and result["zeroBackendAdversarial"]["ignoredCheckoutPathAcceptanceCases"] == 1
            and result["zeroBackendAdversarial"]["finalCyclePolicyRefusalCases"] == 13,
            "descriptor/checkout adversary counts mismatch")
    require(result["resourcePolicy"]["routineBackendInvocations"] == 0, "routine backend count mismatch")
    require(result["resourcePolicy"]["javaMaxHeapMiB"] == 2048, "heap cap mismatch")
    require(result["resourcePolicy"]["javaActiveProcessorCount"] == 2, "CPU cap mismatch")
    require(result["resourcePolicy"]["nonblockingFlock"], "lock policy mismatch")
    require_exact_wall_timeout(result["resourcePolicy"], "final evidence resource policy")
    require(result["rawRun"]["successful"] and result["rawRun"]["authorized"], "raw-run provenance mismatch")
    require(result["terminalPublication"] == {
        "schema": "R3-G-05-outer-success-v1",
        "requiredByPublishGate": True,
        "exactInnerStatus": 0,
        "integrityManifestSha256Bound": True,
        "sessionRecordSha256Bound": True,
        "watchdogRecordSha256Bound": True,
        "watchdogReadySha256Bound": True,
        "validatedBeforeRawExecution": True,
        "privateReadinessAuthenticated": True,
        "watchdogOnlyGateReleaseAcknowledged": True,
        "targetGateReleaseAcknowledged": True,
        "doubleBracketedSessionSelection": True,
        "nonInferentialExitClassification": True,
        "pidfdGenerationBound": True,
        "descriptorOwnerGenerationBound": True,
        "descriptorOwnerFdExcludedFromTarget": True,
        "nestedBoundaryPrePostChecks": True,
        "provisionalResultsRejectedOnPostcheckFailure": True,
        "outerDescriptorOwnerSynchronousThroughReap": True,
        "stableNestedAndImmediatePublicationPathsSplit": True,
        "watchdogDispositionBound": True,
        "targetSessionEmpty": True,
        "activeJournalAbsent": True,
        "failureMarkerAbsent": True,
    }, "secure terminal-publication evidence mismatch")
    artifacts = result["artifacts"]
    require(artifacts["outsideTaskBuildCount"] == 0
            and artifacts["externalKUnchanged"]
            and not artifacts["transformationArtifactsOutsideTaskBuild"]
            and not artifacts["backendArtifactsOutsideTaskBuild"]
            and artifacts["derivedFromFullUntrackedSnapshots"]
            and artifacts["derivedFromExpectedPathScans"], "artifact boundary mismatch")
    watchdog = result["resourcePolicy"]["watchdog"]
    require(watchdog["completed"] and not watchdog["fired"]
            and watchdog["sessionTerminationProven"]
            and watchdog["terminalOuterPublicationGate"]
            and watchdog["validatedBeforeRawExecution"]
            and watchdog["privateReadinessAuthenticated"]
            and watchdog["watchdogOnlyGateRelease"]
            and watchdog["doubleBracketedSessionSelection"]
            and watchdog["nonInferentialExitClassification"]
            and watchdog["pidfdGenerationBound"]
            and watchdog["separateLauncherAndDescriptorOwnerPidfds"]
            and watchdog["descriptorOwnerGenerationBound"]
            and watchdog["descriptorOwnerFdExcludedFromTarget"]
            and watchdog["nestedBoundaryPrePostChecks"]
            and watchdog["provisionalResultsRejectedOnPostcheckFailure"]
            and watchdog["rssLimitMiB"] == 6144
            and watchdog["availableMemoryFloorMiB"] == 4096
            and watchdog["swapFreeFloorMiB"] == 1024,
            "whole-session watchdog evidence mismatch")
    require(result["resourcePolicy"]["descriptorPath"] == {
        "outerFixedFd": 198,
        "outerOwnerSynchronousThroughSessionReap": True,
        "stableOwnerQualifiedNestedPaths": True,
        "stableOwnerQualifiedJavaScratchPath": True,
        "immediateSelfFdPublicationPaths": True,
        "immediateOnlyRecordPublicationPath": True,
        "scratchAndRecordSameDescriptorTree": True,
        "supervisorAndTargetOwnerFdExcluded": True,
        "preAndPostBoundaryIdentityChecks": True,
        "failedPostcheckRejectsProvisionalResults": True,
    }, "descriptor path resource evidence mismatch")
    require(result["resourcePolicy"]["dedicatedSession"]
            and result["resourcePolicy"]["boundedTimeout"],
            "session/timeout resource evidence mismatch")

    pinned = result["pins"]["taskSources"]
    require({
        "spine/rule-applied-allowlist/descriptor_owner.py",
        "spine/rule-applied-allowlist/descriptor_owner_selftest.py",
        "spine/rule-applied-allowlist/checkout_integrity.py",
        "tasks/wave-3/R3-G-05L-nested-child-descriptor-path-repair.md",
        "tasks/wave-3/R3-G-05M-clean-head-and-java-scratch-repair.md",
        "tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md",
        "tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md",
        "tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md",
    }.issubset(pinned), "nested descriptor semantic sources are not pinned")
    for relative, expected in pinned.items():
        require(sha(root / relative) == expected, f"source hash mismatch: {relative}")
    require(result["pins"]["contracts"]["launcherRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05D-waiting-launcher-and-failure-provenance-repair.md"),
            "launcher repair packet pin mismatch")
    require(result["pins"]["contracts"]["securePublicationRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05E-whole-session-and-secure-publication-repair.md"),
            "secure-publication repair packet pin mismatch")
    require(result["pins"]["contracts"]["firstWriterReapingRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05F-first-writer-session-reaping-repair.md"),
            "first-writer/reaping repair packet pin mismatch")
    require(result["pins"]["contracts"]["watchdogIdentityRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05G-watchdog-readiness-and-process-identity-repair.md"),
            "watchdog identity repair packet pin mismatch")
    require(result["pins"]["contracts"]["privateGateRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05H-private-watchdog-gate-and-session-selection-repair.md"),
            "private gate repair packet pin mismatch")
    require(result["pins"]["contracts"]["stoppedProcessRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05I-stopped-process-and-exit-boundary-repair.md"),
            "stopped-process repair packet pin mismatch")
    require(result["pins"]["contracts"]["driverFailureRecoveryRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05J-driver-compilation-and-failure-recovery-repair.md"),
            "driver/failure-recovery repair packet pin mismatch")
    require(result["pins"]["contracts"]["parserAdversaryRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05K-parser-adversary-binding-repair.md"),
            "parser-adversary repair packet pin mismatch")
    require(result["pins"]["contracts"]["nestedDescriptorRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05L-nested-child-descriptor-path-repair.md"),
            "nested-descriptor repair packet pin mismatch")
    require(result["pins"]["contracts"]["cleanHeadJavaScratchRepairPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05M-clean-head-and-java-scratch-repair.md"),
            "clean-head/Java-scratch repair packet pin mismatch")
    require(result["pins"]["contracts"]["final2048HeapCyclePacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md"),
            "final 2048 MiB cycle packet pin mismatch")
    require(result["pins"]["contracts"]["exactFinalTimeoutBindingPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md"),
            "exact final timeout binding packet pin mismatch")
    require(result["pins"]["contracts"]["exactTimeoutReportVerificationPacketSha256"]
            == sha(root / "tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md"),
            "exact-timeout report verification packet pin mismatch")
    require(sha(report_path) == result["evidence"]["reportSha256"], "report hash mismatch")

    java = (task / "src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java").read_text(encoding="utf-8")
    config_java = (task / "src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java").read_text(encoding="utf-8")
    forbidden = re.compile(r'"[^"\n]*(?:bump-state|drop-state|ruleApplied|ruleOrigin|<trace>|\.List)[^"\n]*"')
    require(not forbidden.search(java + config_java), "fixture/event literal crossed into Java")
    require("executePairTransaction" in java and "IdentityHashMap" in java, "atomic pair implementation missing")
    require("replacements.size() == 2" in java, "exact replacement guard missing")
    for witness in ("record OperationAuthority", "record ResultIdentity",
                    "countExactGeneratedUpdates", "returned == input"):
        require(witness in java, f"Java authority witness missing: {witness}")
    require("resolveMarkerEnvelope" not in java and "item.name.equals(result.name)" not in java,
            "Java-owned fixture/marker selection remains")
    require('private static final String JAVA_SCRATCH_ENV = "R3_G_05_JAVA_SCRATCH"' in java,
            "Java scratch environment binding is missing")
    require('Files.createTempFile(javaScratch, "trace-", ".kink")' in java
            and 'Files.createTempFile(javaScratch, "configuration-", ".kink")' in config_java,
            "both Java helpers do not use the stable scratch path")
    trace_run_k = java[java.index("private static String runK("):
                       java.index("private static String required(")]
    configuration_run_k = config_java[config_java.index("private static String runK("):
                                      config_java.index("private static String replaceSource(")]
    require("recordPath.getParent()" not in trace_run_k + configuration_run_k,
            "record path remains a Java nested-scratch authority")

    k_source = (task / "src/rule-applied-allowlist.k").read_text(encoding="utf-8")
    for literal in (SCHEMA, TRANSFORMATION, 'cApply("bump"', 'cApply("drop"',
                    '"_+Int_"', '"_-Int_"', "<=String", "oAllowlistMemberCons",
                    "oOperationAuthority", "oResultIdentity", "#oExpectedTrace",
                    "#oProductionMeta", "oTermMetadataAuthority"):
        require(literal in k_source, f"K ownership witness missing: {literal}")
    require("#oIsAnyExactTrace" not in k_source, "broad existing-graph suppression remains")
    require("#oMetaComplete" not in k_source, "nonempty metadata remained an exactness authority")

    scripts = (task / "verify.sh").read_text(encoding="utf-8")
    require(not re.search(r"\b(?:kompile|krun|java|javac)\b", scripts), "routine verifier names a backend/compiler process")
    report = report_path.read_text(encoding="utf-8")
    require_exact_timeout_report(report)
    require("temporal" in report.lower() and "does not" in report.lower(), "limitation statement missing")
    for witness in ("fixed\ndescriptor 198", "/proc/<outer-wrapper-pid>/fd/198",
                    "/proc/self/fd/<immediate-fd>", "failed post-check",
                    "stable owner-qualified `java-scratch`", "exact clean implementation",
                    "nested `krun` exhausted the enforced 1536 MiB", "Cycle 5 passed"):
        require(witness in report, f"nested descriptor report witness missing: {witness}")
    package = json.loads((root / "package.json").read_text(encoding="utf-8"))
    require(package["scripts"]["r3:g:rule-applied-allowlist"]
            == "bash spine/rule-applied-allowlist/verify.sh", "package script mismatch")


if __name__ == "__main__":
    require(len(sys.argv) == 2, "usage: verify.py REPO_ROOT")
    main(Path(sys.argv[1]).resolve())
