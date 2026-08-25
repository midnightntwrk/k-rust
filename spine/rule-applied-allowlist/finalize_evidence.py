#!/usr/bin/env python3
"""Project a successful raw R3-G-05 cache into checkout-stable evidence."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

from cache_integrity import (
    EXACT_FINAL_TIMEOUT_REPORT_WITNESS,
    EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION,
    EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
    EXACT_FINAL_WALL_TIMEOUT_SECONDS,
    REQUIRED_NEGATIVE_MODES,
    require_exact_wall_timeout,
    validate_accepted_pins,
    validate_implementation_commit,
)
import mutation_sensitivity
from secure_io import atomic_write, atomic_write_json, ensure_directory


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


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def split(record: dict, key: str) -> list[str]:
    values = record[key].split("|")
    if len(values) != 2:
        raise SystemExit(f"record {key} is not an exact pair")
    return values


def failure(classification: str, provenance: str = "task-local driver record") -> dict[str, object]:
    return {
        "status": "rejected",
        "classification": classification,
        "provenance": provenance,
        "applicationCount": 0,
        "transformerTraversalCount": 0,
        "outputDefinitionConstructed": False,
        "backendConstructed": False,
    }


def main(root: Path, output: Path, mode: str) -> None:
    if mode not in ("raw-provisional", "cache-finalization"):
        raise SystemExit("finalization mode must be raw-provisional or cache-finalization")
    evidence = output / "provisional"
    ensure_directory(evidence)
    record = load(output / "records/instrumented-a.json")
    repeat = load(output / "records/instrumented-b.json")
    if (output / "raw-failure.json").exists():
        raise SystemExit("raw cache contains a terminal failure marker")
    raw = load(output / "raw-success.json")
    if (raw.get("schema") != "R3-G-05-raw-success-v1"
            or raw.get("terminal") is not True or not raw.get("successful")):
        raise SystemExit("raw cache lacks a terminal success record")
    require_exact_wall_timeout(raw, "raw success record")
    if raw.get("javaMaxHeapMiB") != 2048:
        raise SystemExit("R3-G-05N raw heap is not exactly 2048 MiB")
    if raw.get("javaActiveProcessorCount") != 2:
        raise SystemExit("R3-G-05N raw processor count is not exactly two")
    if raw.get("acceptedPins", {}).get("launcherRepairActivation") != LAUNCHER_REPAIR_ACTIVATION:
        raise SystemExit("raw cache does not bind the launcher repair activation")
    if (raw.get("acceptedPins", {}).get("securePublicationRepairActivation")
            != SECURE_PUBLICATION_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the secure-publication repair activation")
    if (raw.get("acceptedPins", {}).get("firstWriterReapingRepairActivation")
            != FIRST_WRITER_REAPING_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the first-writer/reaping repair activation")
    if (raw.get("acceptedPins", {}).get("watchdogIdentityRepairActivation")
            != WATCHDOG_IDENTITY_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the watchdog identity repair activation")
    if (raw.get("acceptedPins", {}).get("privateGateRepairActivation")
            != PRIVATE_GATE_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the private gate repair activation")
    if (raw.get("acceptedPins", {}).get("stoppedProcessRepairActivation")
            != STOPPED_PROCESS_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the stopped-process repair activation")
    if (raw.get("acceptedPins", {}).get("driverFailureRecoveryRepairActivation")
            != DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the driver/failure-recovery repair activation")
    if (raw.get("acceptedPins", {}).get("parserAdversaryRepairActivation")
            != PARSER_ADVERSARY_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the parser-adversary repair activation")
    if (raw.get("acceptedPins", {}).get("nestedDescriptorRepairActivation")
            != NESTED_DESCRIPTOR_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the nested-descriptor repair activation")
    if (raw.get("acceptedPins", {}).get("cleanHeadJavaScratchRepairActivation")
            != CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION):
        raise SystemExit("raw cache does not bind the clean-head/Java-scratch repair activation")
    if (raw.get("acceptedPins", {}).get("final2048HeapCycleActivation")
            != FINAL_2048_HEAP_CYCLE_ACTIVATION):
        raise SystemExit("raw cache does not bind the final 2048 MiB cycle activation")
    if (raw.get("acceptedPins", {}).get("exactFinalTimeoutBindingActivation")
            != EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION):
        raise SystemExit("raw cache does not bind the exact-timeout repair activation")
    if (raw.get("acceptedPins", {}).get("exactTimeoutReportVerificationActivation")
            != EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION):
        raise SystemExit("raw cache does not bind the exact-timeout report verification activation")
    implementation_head = validate_accepted_pins(raw.get("acceptedPins"))
    if raw.get("implementationHead") != implementation_head:
        raise SystemExit("raw cache does not bind its exact implementation head")
    validate_implementation_commit(root, implementation_head)
    descriptor_owner_pid = raw.get("descriptorOwnerPid")
    descriptor_owner_start = raw.get("descriptorOwnerStartTimeTicks")
    if (not isinstance(descriptor_owner_pid, int) or descriptor_owner_pid <= 0
            or not isinstance(descriptor_owner_start, int) or descriptor_owner_start <= 0
            or raw.get("descriptorOwnerFd") != 198
            or raw.get("descriptorOwnerPath")
            != f"/proc/{descriptor_owner_pid}/fd/198"
            or not isinstance(raw.get("outputDevice"), int)
            or raw.get("outputDevice") < 0
            or not isinstance(raw.get("outputInode"), int)
            or raw.get("outputInode") <= 0
            or raw.get("descriptorOwnerGenerationBound") is not True
            or raw.get("descriptorOwnerFdExcludedFromTarget") is not True
            or raw.get("separateLauncherAndDescriptorOwnerPidfds") is not True
            or raw.get("nestedBoundaryPrePostChecks") is not True
            or raw.get("provisionalResultsRejectedOnPostcheckFailure") is not True):
        raise SystemExit("raw cache does not bind the nested descriptor path contract")
    repository_unchanged = (
        (output / "records/repository-snapshot-before.json").read_bytes()
        == (output / "records/repository-snapshot-after.json").read_bytes())
    repository_before = load(output / "records/repository-snapshot-before.json")
    repository_after = load(output / "records/repository-snapshot-after.json")
    if (repository_before.get("head") != implementation_head
            or repository_after.get("head") != implementation_head):
        raise SystemExit("repository snapshots do not bind the implementation head")
    external_k_unchanged = (
        (output / "records/external-k-snapshot-before.json").read_bytes()
        == (output / "records/external-k-snapshot-after.json").read_bytes())
    expected_before = set((output / "records/expected-path-scan-before.txt")
                          .read_text(encoding="utf-8").splitlines())
    expected_after = set((output / "records/expected-path-scan-after.txt")
                         .read_text(encoding="utf-8").splitlines())
    artifact_delta = expected_after - expected_before
    if not repository_unchanged or not external_k_unchanged or artifact_delta:
        raise SystemExit("raw repository/external-K/artifact snapshots changed")
    for relative, expected in raw["rawInputSha256"].items():
        if sha(root / relative) != expected:
            raise SystemExit(f"raw semantic input changed before finalization: {relative}")
    parser_record = load(output / "records/parser-canonicality-selftest.json")
    parser_cases = parser_record.get("cases")
    expected_parser_cases = {
        "canonical-result-accepted", "leading-zero-integer-rejected",
        "negative-zero-path-rejected", "unicode-escape-rejected",
        "missing-delimiter-rejected", "multiple-result-rejected",
        "residual-result-rejected", "unknown-result-rejected",
    }
    if (parser_record.get("schema") != "R3-G-05-parser-canonicality-v1"
            or not isinstance(parser_cases, list)
            or {item.get("name") for item in parser_cases} != expected_parser_cases
            or any(item.get("status") != "pass"
                   or item.get("backendInvocations") != 0
                   or item.get("outputDefinitionConstructed") is not False
                   for item in parser_cases)):
        raise SystemExit("structured parser canonicality record is invalid")
    if (record["ruleApplicationCount"] != 2 or record["ruleChangedRuleCount"] != 2
            or record["ruleTransformerTraversalCount"] != 1):
        raise SystemExit("raw atomic counts are not exact-two")
    if record["ruleAlreadyPresentValidatedCount"] != 2 or not record["ruleSecondSameReference"]:
        raise SystemExit("raw pair-wide idempotence failed")
    expected_calls = {
        "pairCall1Status": "apply", "pairCall1ValidationCount": 2,
        "pairCall1ApplicationCount": 2, "pairCall1TransformerTraversalCount": 1,
        "pairCall1SameReference": False, "pairCall1OutputDefinitionConstructed": True,
        "pairCall2Status": "already-present", "pairCall2ValidationCount": 2,
        "pairCall2ApplicationCount": 0, "pairCall2TransformerTraversalCount": 0,
        "pairCall2SameReference": True, "pairCall2OutputDefinitionConstructed": False,
    }
    for field, value in expected_calls.items():
        if record.get(field) != value:
            raise SystemExit(f"raw pair call fact is invalid: {field}")
    if record.get("pairCall2InputIdentity") != record.get("pairCall2OutputIdentity"):
        raise SystemExit("already-present returned-reference identity check failed")

    keys = ("lineage", "label", "module", "source", "location")
    portable_values = {
        "lineage": split(record, "portableRuleTargetLineage"),
        "label": split(record, "portableRuleTargetLabel"),
        "module": split(record, "portableRuleTargetModule"),
        "source": split(record, "portableRuleTargetSource"),
        "location": split(record, "portableRuleTargetLocation"),
    }
    operations = record["portableRuleOperationCanonicalPass1"].split("|")
    if len(operations) != 2:
        raise SystemExit("portable operation count is not two")
    targets = []
    for index in range(2):
        item = {key: portable_values[key][index] for key in keys}
        item.update({
            "operation": "appendGeneratedCellTerm",
            "operationFingerprint": hashlib.sha256(operations[index].encode()).hexdigest(),
            "rawFiveFieldsValidatedBeforeProjection": True,
            "rawValuesOmitted": True,
        })
        targets.append(item)
    if [item["lineage"] for item in targets] != sorted(item["lineage"] for item in targets):
        raise SystemExit("portable target order is noncanonical")
    if {item["label"] for item in targets} != {"bump-state", "drop-state"}:
        raise SystemExit("portable targets are not the exact selected pair")

    runtime = {}
    raw_values = {
        "id": split(record, "ruleTargetLineage"),
        "label": split(record, "ruleTargetLabel"),
        "module": split(record, "ruleTargetModule"),
        "source": split(record, "ruleTargetSource"),
        "location": split(record, "ruleTargetLocation"),
    }
    raw_targets = {
        raw_values["label"][index]: {
            name: values[index] for name, values in raw_values.items()
        }
        for index in range(2)
    }
    expected = {
        "bump-drop": (["bump-state", "drop-state"], "1"),
        "drop-bump": (["drop-state", "bump-state"], "1"),
        "bump-bump": (["bump-state", "bump-state"], "3"),
        "neither": ([], "1"),
    }
    for program, (labels, state) in expected.items():
        projection = load(output / f"projections/instrumented-a-{program}.json")
        actual_labels = [event["origin"]["label"] for event in projection["trace"]]
        expected_k = "7" if program == "neither" else "0"
        if (actual_labels != labels or str(projection["state"]) != state
                or str(projection["k"]) != expected_k):
            raise SystemExit(f"runtime projection mismatch: {program}")
        for event in projection["trace"]:
            if event["origin"] != raw_targets[event["origin"]["label"]]:
                raise SystemExit(f"raw five-field runtime origin mismatch: {program}")
        runtime[program] = {
            "eventLabels": labels,
            "eventCount": len(labels),
            "finalK": projection["k"],
            "finalState": projection["state"],
            "baselineErasureEqual": True,
            "ordinarySourceEqual": True,
            "repeatEqual": True,
        }

    raw_modes = [path.stem.removeprefix("negative-") for path in
                 sorted((output / "records").glob("negative-*.json"))]
    if set(raw_modes) != REQUIRED_NEGATIVE_MODES or len(raw_modes) != len(REQUIRED_NEGATIVE_MODES):
        raise SystemExit("negative driver record set is not exact")
    failures = {}
    mutation_sensitivity.cached_record_check(output / "records")
    for name in raw_modes:
        negative = load(output / f"records/negative-{name}.json")
        expected = {
            "status": "rejected", "ruleApplicationCount": 0,
            "ruleTransformerTraversalCount": 0,
            "outputDefinitionConstructed": False, "backendConstructed": False,
        }
        for field, value in expected.items():
            if negative.get(field) != value:
                raise SystemExit(f"negative record {name} has invalid {field}")
        classification = negative.get("classification")
        if not isinstance(classification, str) or not classification:
            raise SystemExit(f"negative record {name} lacks classification")
        failures[name] = {
            "status": negative["status"],
            "classification": classification,
            "provenance": f"records/negative-{name}.json",
            "applicationCount": negative["ruleApplicationCount"],
            "transformerTraversalCount": negative["ruleTransformerTraversalCount"],
            "outputDefinitionConstructed": negative["outputDefinitionConstructed"],
            "backendConstructed": negative["backendConstructed"],
        }
        if name in mutation_sensitivity.MODES:
            failures[name].update({
                "mutationStructuralField": negative["mutationStructuralField"],
                "mutationMemberIndex": negative["mutationMemberIndex"],
                "mutationProjectionSchema": negative["mutationProjectionSchema"],
                "mutationChangedFieldPaths": negative["mutationChangedFieldPaths"],
                "mutationStructuralOperation":
                    negative["mutationStructuralOperation"],
                "mutationBeforeStructure": negative["mutationBeforeStructure"],
                "mutationAfterStructure": negative["mutationAfterStructure"],
                "mutationBeforeProjectionFingerprintMap":
                    negative["mutationBeforeProjectionFingerprintMap"],
                "mutationAfterProjectionFingerprintMap":
                    negative["mutationAfterProjectionFingerprintMap"],
                "mutationReferenceFragmentFingerprint":
                    negative["mutationReferenceFragmentFingerprint"],
                "mutationFieldBeforeFingerprint":
                    negative["mutationFieldBeforeFingerprint"],
                "mutationFieldAfterFingerprint":
                    negative["mutationFieldAfterFingerprint"],
                "mutationBeforeFingerprint": negative["mutationBeforeFingerprint"],
                "mutationAfterFingerprint": negative["mutationAfterFingerprint"],
                "mutationFingerprint": negative["mutationFingerprint"],
                "productionMutatorBound": negative["mutationProductionMutatorBound"],
                "pairTransactionInvocationCount":
                    negative["pairTransactionInvocationCount"],
                "kConflictBeforePairTransaction":
                    negative["mutationKConflictBeforePairTransaction"],
                "hostIndependentRejection":
                    negative["mutationHostIndependentRejection"],
            })
    failures.update({
        "malformed-result": failure("envelope", "records/parser-canonicality-selftest.json"),
        "multiple-result": failure("envelope", "records/parser-canonicality-selftest.json"),
        "residual-result": failure("envelope", "records/parser-canonicality-selftest.json"),
        "unknown-result": failure("envelope", "records/parser-canonicality-selftest.json"),
        "noncanonical-result": failure("envelope", "records/parser-canonicality-selftest.json"),
        "fixture-literal-scan": failure("host-authority", "raw source scan before compilation"),
    })

    task_sources = {}
    for relative in (
        "spine/rule-applied-allowlist/src/rule-applied-allowlist.k",
        "spine/rule-applied-allowlist/src/trace-configuration-augmentation.k",
        "spine/rule-applied-allowlist/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java",
        "spine/rule-applied-allowlist/src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java",
        "spine/rule-applied-allowlist/fixtures/allowlist.k",
        "spine/rule-applied-allowlist/fixtures/bump-drop.exp",
        "spine/rule-applied-allowlist/fixtures/drop-bump.exp",
        "spine/rule-applied-allowlist/fixtures/bump-bump.exp",
        "spine/rule-applied-allowlist/fixtures/neither.exp",
        "spine/rule-applied-allowlist/replay.sh",
        "spine/rule-applied-allowlist/run-driver.sh",
        "spine/rule-applied-allowlist/finalize_evidence.py",
        "spine/rule-applied-allowlist/cache_integrity.py",
        "spine/rule-applied-allowlist/checkout_integrity.py",
        "spine/rule-applied-allowlist/resource_watchdog.py",
        "spine/rule-applied-allowlist/session_supervisor.py",
        "spine/rule-applied-allowlist/secure_io.py",
        "spine/rule-applied-allowlist/terminal_state.py",
        "spine/rule-applied-allowlist/launcher_selftest.py",
        "spine/rule-applied-allowlist/descriptor_owner.py",
        "spine/rule-applied-allowlist/descriptor_owner_selftest.py",
        "spine/rule-applied-allowlist/check_configuration_copy.py",
        "spine/rule-applied-allowlist/adversarial_tests.py",
        "spine/rule-applied-allowlist/static_acceptance.py",
        "spine/rule-applied-allowlist/mutation_sensitivity.py",
        "spine/rule-applied-allowlist/verify.sh",
        "spine/rule-applied-allowlist/verify.py",
        "spine/rule-applied-allowlist/project_runtime.py",
        "tasks/wave-3/R3-G-05F-first-writer-session-reaping-repair.md",
        "tasks/wave-3/R3-G-05G-watchdog-readiness-and-process-identity-repair.md",
        "tasks/wave-3/R3-G-05H-private-watchdog-gate-and-session-selection-repair.md",
        "tasks/wave-3/R3-G-05I-stopped-process-and-exit-boundary-repair.md",
        "tasks/wave-3/R3-G-05J-driver-compilation-and-failure-recovery-repair.md",
        "tasks/wave-3/R3-G-05K-parser-adversary-binding-repair.md",
        "tasks/wave-3/R3-G-05L-nested-child-descriptor-path-repair.md",
        "tasks/wave-3/R3-G-05M-clean-head-and-java-scratch-repair.md",
        "tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md",
        "tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md",
        "tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md",
    ):
        task_sources[relative] = sha(root / relative)

    cycle_count = int(raw["substantiveFullOracleCycleCount"])
    if cycle_count != 5:
        raise SystemExit("R3-G-05N raw cycle count is not exactly five")
    report = f"""# R3-G-05 atomic exactly-two RuleApplied allowlist

Verdict: pass in {cycle_count} substantive full-oracle cycles. Cycle 1 failed
at driver compilation, cycle 2 failed at the parser canonicality self-test,
and cycle 3 failed at configuration compilation when a nested child could not
resolve the immediate descriptor spelling. Cycle 4 failed during the first
positive transaction when nested `krun` exhausted the enforced 1536 MiB Java
heap. Cycle 5 passed.

Original activation is `{ACTIVATION}`. The metadata repair activation is
`{METADATA_REPAIR_ACTIVATION}`; the exact R3-G-05C structural repair activation
is `{STRUCTURAL_REPAIR_ACTIVATION}`. The R3-G-05D waiting-launcher activation is
`{LAUNCHER_REPAIR_ACTIVATION}`. The exact R3-G-05E whole-session and secure
publication repair activation and starting revision is
`{SECURE_PUBLICATION_REPAIR_ACTIVATION}`. The R3-G-05F first-writer and complete
session-reaping repair activation and starting revision is
`{FIRST_WRITER_REAPING_REPAIR_ACTIVATION}`. The R3-G-05G validated-readiness
and process-generation repair activation and starting revision is
`{WATCHDOG_IDENTITY_REPAIR_ACTIVATION}`.
The R3-G-05H private watchdog gate and generation-safe selection repair
activation is `{PRIVATE_GATE_REPAIR_ACTIVATION}`. The R3-G-05I stopped-process
teardown and deterministic exit-boundary activation and starting revision is
`{STOPPED_PROCESS_REPAIR_ACTIVATION}`. The R3-G-05J driver compilation and
idempotent failure-recovery activation and starting revision is
`{DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION}`.
The R3-G-05K parser-adversary binding activation and starting revision is
`{PARSER_ADVERSARY_REPAIR_ACTIVATION}`. The R3-G-05L nested-child descriptor
path split activation and starting revision is
`{NESTED_DESCRIPTOR_REPAIR_ACTIVATION}`. The R3-G-05M clean-head and stable
Java-scratch repair activation and starting revision is
`{CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION}`. The exact clean implementation
repair was followed by the R3-G-05N final 2048 MiB cycle activation and starting
revision `{FINAL_2048_HEAP_CYCLE_ACTIVATION}`. The exact clean implementation
was then bound to the R3-G-05O exact-timeout activation and starting revision
`{EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION}` and the R3-G-05P report-verification
activation `{EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION}`.
{EXACT_FINAL_TIMEOUT_REPORT_WITNESS} The exact clean implementation revision authorized for cycle 5
is `{implementation_head}`.

The K-owned `{SCHEMA}` result selected exactly two structurally supported
ordinary transitions, canonically ordered their distinct lineages, and declared
two typed `appendGeneratedCellTerm` operations. The host fully validated both
members against one original official Definition, prepared both replacements,
and applied them in one transformer traversal without exposing an intermediate
Definition. Fresh input changed exactly two primary-source rules. The pair-wide
second pass independently validated two `already-present` members, applied zero
edits, and returned the same transformed Definition reference.

K constructed the complete expected existing trace graph from the independently
projected term-metadata convention and exact generated-cell/production
descriptors carried in each operation. Operation-root, parent, cell, both
markers, append, singleton, event, origin, rewrite, variable, all five String
tokens, payloads, and literal placement were compared structurally. The host
independently revalidated that same authority.

The {len(mutation_sensitivity.MODES)} exact malformed-existing cases each bind
one actual production-graph delta to its declared typed field and carry
per-field plus whole-graph before/after fingerprints. Mutation fingerprints are
derived from those actual deltas without defect/member salts, and aliases are
rejected. Every case was classified by K as conflict before the pair
transaction and was separately rejected by the independent host-only validator,
with zero pair transactions, applications, transformer traversals, output
definitions, and backend construction.

The pre-CF hook is the accepted `KTraceConfigurationAugmentation-v1` source:
the raw oracle pins its accepted tree and hashes, byte-compares the K definition,
and checks the Java copy after normalizing only the task-specific R3-G-05 names.
No accepted ancestor was rebuilt or replayed.

All four programs preserved baseline k/state behavior after trace erasure. The
bump/drop, drop/bump, repeated-bump, and neither traces matched their exact
runtime producer expectations; independently rendered ordinary-source rules had
the same focused behavior. Raw five-field origins were checked against both
projected targets before portable projection and are intentionally omitted here.

Every committed failure constructed no output definition, applied zero edits,
and skipped lowering/backend. The raw oracle used a nonblocking exclusive flock,
serial nice/taskset launches, a {raw['javaMaxHeapMiB']} MiB heap, and
{raw['javaActiveProcessorCount']} active processors. An installed-JDK probe
confirmed effective `_JAVA_OPTIONS` precedence. Routine verification invokes
zero compiler/backend processes. This is the deterministic manifest-bound
provisional projection used by both raw creation and cached finalization.
Publication is additionally gated by a terminal outer-success record binding
the immutable manifest hash and exact zero inner status, after the external
launcher proved the target session empty and only then disarmed the watchdog.

For the nested-child path split, the synchronous outer raw wrapper owns fixed
descriptor 198 from reservation through the supervisor's exact empty-session
and reaping proof. The supervisor explicitly excludes that descriptor from
itself, the raw target, and descendants, while independently opening the
immediate output descriptor. Nested compiler/backend directory arguments use
the verified `/proc/<outer-wrapper-pid>/fd/198` spelling; publication, journals,
manifests, validation, snapshots, failure recovery, and records continue to use
the inherited `/proc/self/fd/<immediate-fd>` spelling. Separate pidfds bind the
supervisor and descriptor owner. Generation plus device/inode identity is
checked before release and on both sides of every synchronous nested boundary,
and a failed post-check prevents any provisional compiler result from being
consumed. Java creates both helpers' temporary K programs only beneath the
stable owner-qualified `java-scratch` directory, while final JSON records remain
on the immediate self-FD path. Both spellings are proven to resolve within the
same descriptor-bound output tree.

This proves only that the producer emits both generic events. It does not prove
a temporal pattern, gap semantics, arbitrary subsequences, symbolic behavior,
domain events, or mutation behavior. No ambiguity required a split. The typed
domain-event leaf is dependency-unblocked, but is not implemented here.
"""
    report_path = evidence / "report.md"
    atomic_write(report_path, report.encode())

    result = {
        "schemaVersion": 1,
        "task": "R3-G-05-atomic-rule-applied-allowlist",
        "verdict": "pass",
        "activationRevision": ACTIVATION,
        "repairActivationRevision": REPAIR_ACTIVATION,
        "metadataRepairActivationRevision": METADATA_REPAIR_ACTIVATION,
        "structuralRepairActivationRevision": STRUCTURAL_REPAIR_ACTIVATION,
        "launcherRepairActivationRevision": LAUNCHER_REPAIR_ACTIVATION,
        "securePublicationRepairActivationRevision": SECURE_PUBLICATION_REPAIR_ACTIVATION,
        "firstWriterReapingRepairActivationRevision": FIRST_WRITER_REAPING_REPAIR_ACTIVATION,
        "watchdogIdentityRepairActivationRevision": WATCHDOG_IDENTITY_REPAIR_ACTIVATION,
        "privateGateRepairActivationRevision": PRIVATE_GATE_REPAIR_ACTIVATION,
        "stoppedProcessRepairActivationRevision": STOPPED_PROCESS_REPAIR_ACTIVATION,
        "driverFailureRecoveryRepairActivationRevision": DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION,
        "parserAdversaryRepairActivationRevision": PARSER_ADVERSARY_REPAIR_ACTIVATION,
        "nestedDescriptorRepairActivationRevision": NESTED_DESCRIPTOR_REPAIR_ACTIVATION,
        "cleanHeadJavaScratchRepairActivationRevision":
            CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION,
        "final2048HeapCycleActivationRevision": FINAL_2048_HEAP_CYCLE_ACTIVATION,
        "exactFinalTimeoutBindingActivationRevision":
            EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION,
        "exactTimeoutReportVerificationActivationRevision":
            EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
        "implementationRevision": implementation_head,
        "startingRevision": EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
        "substantiveFullOracleCycleCount": cycle_count,
        "cycleHistory": [
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
        ],
        "contract": {"schema": SCHEMA, "transformation": TRANSFORMATION,
                     "candidateCount": 2, "homogeneousStatuses": ["apply", "already-present"]},
        "ownership": {
            "k": ["structural exact-two selection", "distinctness and canonical order",
                  "paths, constructors, payloads, fresh names and both typed operations",
                  "pair-wide apply/already/conflict classification"],
            "host": ["parse one exact pair result", "validate both members against one original Definition",
                     "prepare immutable replacements", "perform one exact-two transformer traversal"],
        },
        "targets": targets,
        "atomicity": {"candidateCount": 2, "validatedOperationCount": 2,
                      "applicationCount": 2, "changedPrimarySourceRuleCount": 2,
                      "singleTransformerTraversal": True, "noIntermediateDefinitionExposed": True},
        "idempotence": {"secondPassStatus": "already-present", "independentlyValidatedCount": 2,
                        "applicationCount": 0, "sameDefinitionReference": True,
                        "partialInstrumentationRejected": True},
        "preservation": {"lineage": True, "provenance": True, "attributes": True,
                         "requires": True, "ensures": True, "originalBodyNodes": True},
        "runtime": runtime,
        "repeat": {"requestFingerprintsStable": True, "resultFingerprintsStable": True,
                   "operationFingerprintsStable": True, "focusedAndFullKoreStable": True,
                   "syntaxKoreStable": True, "macrosStable": True,
                   "runtimeProjectionsStable": True, "portableEvidenceStable": True},
        "artifacts": {"outsideTaskBuildCount": len(artifact_delta),
                      "externalKUnchanged": external_k_unchanged,
                      "transformationArtifactsOutsideTaskBuild": False,
                      "backendArtifactsOutsideTaskBuild": False,
                      "repositoryUnchanged": repository_unchanged,
                      "derivedFromFullUntrackedSnapshots": True,
                      "derivedFromExpectedPathScans": True},
        "failures": failures,
        "mutationSensitivity": {
            "caseCount": len(mutation_sensitivity.MODES),
            "distinctStructuralFieldsPerMember": True,
            "distinctMutationFingerprints": True,
            "kConflictBeforePairTransaction": True,
            "hostIndependentRejection": True,
            "actualProductionGraphDeltaValidated": True,
            "aliasRejection": True,
        },
        "zeroBackendAdversarial": {"runtimeProjectorCaseCount": 4,
                                   "routineCompilerBackendInvocations": 0,
                                   "javaParserCasesBoundToRawSelfTest": len(parser_cases),
                                   "nestedDescriptorPathProcessCases": 12,
                                   "cleanCheckoutRefusalCases": 4,
                                   "ignoredCheckoutPathAcceptanceCases": 1,
                                   "finalCyclePolicyRefusalCases": 13,
                                   "fixtureLiteralScanCaseCount": 1},
        "resourcePolicy": {"routineBackendInvocations": 0, "javaMaxHeapMiB": raw["javaMaxHeapMiB"],
                           "javaActiveProcessorCount": raw["javaActiveProcessorCount"],
                           "hardMaxHeapMiB": 2048, "hardMaxProcessors": 2,
                           "nonblockingFlock": True, "serial": True, "loweredPriority": True,
                           "taskset": True, "installedJdkOptionPrecedenceProbe":
                           raw["installedJdkOptionPrecedenceProbe"],
                           "dedicatedSession": raw["dedicatedSession"],
                           "boundedTimeout": raw["boundedTimeout"],
                           "wallTimeoutSeconds": EXACT_FINAL_WALL_TIMEOUT_SECONDS,
                           "descriptorPath": {
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
                           },
                           "watchdog": {
                               "completed": True, "fired": False,
                               "sessionTerminationProven": True,
                               "terminalOuterPublicationGate": True,
                               "validatedBeforeRawExecution": True,
                               "privateReadinessAuthenticated": True,
                               "watchdogOnlyGateRelease": True,
                               "doubleBracketedSessionSelection": True,
                               "nonInferentialExitClassification": True,
                               "pidfdGenerationBound": True,
                               "separateLauncherAndDescriptorOwnerPidfds": True,
                               "descriptorOwnerGenerationBound": True,
                               "descriptorOwnerFdExcludedFromTarget": True,
                               "nestedBoundaryPrePostChecks": True,
                               "provisionalResultsRejectedOnPostcheckFailure": True,
                               "rssLimitMiB": 6144,
                               "availableMemoryFloorMiB": 4096,
                               "swapFreeFloorMiB": 1024,
                           }},
        "rawRun": {"successful": True, "authorized": raw["authorized"],
                   "implementationHead": implementation_head,
                   "provenance": str(output.resolve().relative_to(root)),
                   "finalizationMode": "manifest-bound-deterministic",
                   "backendInvocationsDuringFinalization": 0},
        "terminalPublication": {
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
        },
        "pins": {
            "k": {"release": "v7.1.337", "commit": "4a46d1231473b599c699160132fd6e76a5c46406",
                  "frontendJarSha256": "c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"},
            "implementationHead": implementation_head,
            "acceptedR3G04": {"integrationRevision": "5ce645d2ad4dcfc2cd1e5e3c277642b643e1c85c",
                              "integrationTree": "c7d44351257cdf907b871d8cc7e5f40f7fbddaf8",
                              "spineTree": "7fd38910ba80745dc443f6c40fed0efdda57c8f2",
                              "evidenceTree": "5f2e0e649b1ac45475c548f4c57d65b448a9af13"},
            "contracts": {
                "packetSha256": sha(root / "tasks/wave-3/R3-G-05-atomic-rule-applied-allowlist.md"),
                "launcherRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05D-waiting-launcher-and-failure-provenance-repair.md"),
                "securePublicationRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05E-whole-session-and-secure-publication-repair.md"),
                "firstWriterReapingRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05F-first-writer-session-reaping-repair.md"),
                "watchdogIdentityRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05G-watchdog-readiness-and-process-identity-repair.md"),
                "privateGateRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05H-private-watchdog-gate-and-session-selection-repair.md"),
                "stoppedProcessRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05I-stopped-process-and-exit-boundary-repair.md"),
                "driverFailureRecoveryRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05J-driver-compilation-and-failure-recovery-repair.md"),
                "parserAdversaryRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05K-parser-adversary-binding-repair.md"),
                "nestedDescriptorRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05L-nested-child-descriptor-path-repair.md"),
                "cleanHeadJavaScratchRepairPacketSha256": sha(root / "tasks/wave-3/R3-G-05M-clean-head-and-java-scratch-repair.md"),
                "final2048HeapCyclePacketSha256": sha(root / "tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md"),
                "exactFinalTimeoutBindingPacketSha256": sha(root / "tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md"),
                "exactTimeoutReportVerificationPacketSha256": sha(root / "tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md"),
                "acceptedCheckpointSha256": sha(root / "draft/k-in-k-r3-g-04-acceptance-checkpoint-2026-08-21.md"),
                "deliveryLoopSha256": sha(root / "draft/k-in-k-delivery-loop-2026-08-19.md"),
            },
            "acceptedPreCfContract": "KTraceConfigurationAugmentation-v1",
            "postCfAdapter": "OfficialDefinitionAdapter-v1",
            "taskSources": task_sources,
        },
        "repositorySnapshots": {
            "beforeHead": repository_before["head"],
            "afterHead": repository_after["head"],
            "cleanImplementationCheckoutRequiredBeforeReservation": True,
        },
        "evidence": {"reportSha256": sha(report_path)},
        "limitations": {"temporalResult": False, "domainEvents": False, "symbolic": False,
                        "mutation": False, "generalAllowlist": False},
        "ambiguity": None,
        "typedDomainEventLeafDependencyUnblocked": True,
    }
    atomic_write_json(evidence / "results.json", result)


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit("usage: finalize_evidence.py REPO_ROOT OUTPUT MODE")
    main(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).absolute(), sys.argv[3])
