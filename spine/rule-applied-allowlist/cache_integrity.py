#!/usr/bin/env python3
"""Zero-backend cache, path, snapshot, and publication integrity for R3-G-05."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import tempfile
import threading
from pathlib import Path

import mutation_sensitivity
import secure_io as secure_io_module
from resource_watchdog import session_members
from secure_io import (
    SecureIOError,
    atomic_write,
    atomic_write_json,
    durable_unlink,
    ensure_directory,
    publish_integrity_manifest,
    publish_outer_success,
    reserve_output,
    verify_directory,
)


SCHEMA = "R3-G-05-raw-integrity-v1"
CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION = "f5e07a4f47929ebbe76f9c5eb22f73ff39e65745"
FINAL_2048_HEAP_CYCLE_ACTIVATION = "d995a8cc93462a43260bdadba256a90d61b0ffe2"
EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION = "b67605c7228f8459173fceba527fb6d364e0e069"
EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION = "7a072969a09260a1e3263de94b84dc3d54fac5d2"
EXACT_FINAL_WALL_TIMEOUT_SECONDS = 7200
EXACT_FINAL_TIMEOUT_REPORT_WITNESS = "Cycle 5 used the exact 7200-second wall timeout."
WATCHDOG_DONE_CONTENT = b"external-empty-session-verification\n"
WATCHDOG_DONE_SHA256 = hashlib.sha256(WATCHDOG_DONE_CONTENT).hexdigest()
PROVISIONAL = ("provisional/results.json", "provisional/report.md")
FAILURE_FIELDS = {
    "status": "rejected",
    "ruleApplicationCount": 0,
    "ruleTransformerTraversalCount": 0,
    "outputDefinitionConstructed": False,
    "backendConstructed": False,
}
SEMANTIC_INPUTS = (
    "tasks/wave-3/R3-G-05-atomic-rule-applied-allowlist.md",
    "tasks/wave-3/R3-G-05A-atomic-rule-applied-allowlist-acceptance-repair.md",
    "tasks/wave-3/R3-G-05B-exact-existing-metadata-repair.md",
    "tasks/wave-3/R3-G-05C-structural-mutation-and-host-exactness-repair.md",
    "tasks/wave-3/R3-G-05D-waiting-launcher-and-failure-provenance-repair.md",
    "tasks/wave-3/R3-G-05E-whole-session-and-secure-publication-repair.md",
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
    "draft/k-in-k-r3-g-04-acceptance-checkpoint-2026-08-21.md",
    "draft/k-in-k-delivery-loop-2026-08-19.md",
    "investigations/r2-g-05-pre-cf-hook-prototype/upstream.patch",
    "investigations/w1-inprocess-adapter/normalize_identity_kore.py",
    "spine/trace-configuration-composition/src/trace-configuration-augmentation.k",
    "spine/trace-configuration-composition/src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java",
    "spine/rule-applied-allowlist/src/rule-applied-allowlist.k",
    "spine/rule-applied-allowlist/src/trace-configuration-augmentation.k",
    "spine/rule-applied-allowlist/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java",
    "spine/rule-applied-allowlist/src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java",
    "spine/rule-applied-allowlist/fixtures/allowlist.k",
    "spine/rule-applied-allowlist/fixtures/bump-drop.exp",
    "spine/rule-applied-allowlist/fixtures/drop-bump.exp",
    "spine/rule-applied-allowlist/fixtures/bump-bump.exp",
    "spine/rule-applied-allowlist/fixtures/neither.exp",
    "spine/rule-applied-allowlist/fixtures/ordinary-template.k",
    "spine/rule-applied-allowlist/render_ordinary.py",
    "spine/rule-applied-allowlist/project_runtime.py",
    "spine/rule-applied-allowlist/project_rule_kore.py",
    "spine/rule-applied-allowlist/selftest_runtime.py",
    "spine/rule-applied-allowlist/compare_repeat_records.py",
    "spine/rule-applied-allowlist/check_configuration_copy.py",
    "spine/rule-applied-allowlist/replay.sh",
    "spine/rule-applied-allowlist/run-driver.sh",
    "spine/rule-applied-allowlist/finalize_evidence.py",
    "spine/rule-applied-allowlist/cache_integrity.py",
    "spine/rule-applied-allowlist/resource_watchdog.py",
    "spine/rule-applied-allowlist/session_supervisor.py",
    "spine/rule-applied-allowlist/secure_io.py",
    "spine/rule-applied-allowlist/terminal_state.py",
    "spine/rule-applied-allowlist/launcher_selftest.py",
    "spine/rule-applied-allowlist/descriptor_owner.py",
    "spine/rule-applied-allowlist/descriptor_owner_selftest.py",
    "spine/rule-applied-allowlist/checkout_integrity.py",
    "spine/rule-applied-allowlist/adversarial_tests.py",
    "spine/rule-applied-allowlist/static_acceptance.py",
    "spine/rule-applied-allowlist/mutation_sensitivity.py",
    "spine/rule-applied-allowlist/verify.py",
    "spine/rule-applied-allowlist/verify.sh",
    "spine/rule-applied-allowlist/.gitignore",
)
REQUIRED_NEGATIVE_MODES = {
    "zero-target", "one-target", "three-target", "duplicate-target",
    "noncanonical-member-order", "stale-first", "stale-second",
    "unsupported-path-first", "unsupported-path-second",
    "conflict-existing-first", "conflict-existing-second",
    "partial-existing-first", "partial-existing-second",
    "false-already-present", "false-apply-existing", "unsupported-shape",
    "forced-preparation-failure-first", "forced-preparation-failure-second",
    "missing-cell-metadata-first", "missing-cell-metadata-second",
    "ambiguous-cell-metadata-first", "ambiguous-cell-metadata-second",
    "missing-constructor-metadata-first", "missing-constructor-metadata-second",
    "ambiguous-constructor-metadata-first", "ambiguous-constructor-metadata-second",
    "unknown-constructor-first", "unknown-constructor-second",
    "sort-invalid-first", "sort-invalid-second",
    "freshness-invalid-first", "freshness-invalid-second",
    "payload-invalid-first", "payload-invalid-second",
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
STATIC_ACCEPTED_PINS = {
    "activation": "2d74814f561d17922384db3d8f21ffba9c2eeae0",
    "repairActivation": "6f5cff55845ff94aa96884dec3bd7c6b1de92cc2",
    "metadataRepairActivation": "2c79c78c1dea7611adf1d11ab2a50c1a309ad90c",
    "structuralRepairActivation": "52f0d3b4b3b6b81100d09d080b55ae5eafede698",
    "launcherRepairActivation": "c76b4fa2169b7f02de3856c8b67673be2756938f",
    "securePublicationRepairActivation": "3fc61ff24bea53f519005da66a98a6f148c00c8a",
    "firstWriterReapingRepairActivation": "7bba98ba9ccb14c91c443f9a9f99c6c9154d8aa4",
    "watchdogIdentityRepairActivation": "de8e5a89b6e0bfc51b4fc5f15581368760f8d630",
    "privateGateRepairActivation": "6c0c5dc6bc1c78b9101d1f46cf08dccb4bec2761",
    "stoppedProcessRepairActivation": "9bcb273863027af51a9381ecb02edace9a896adf",
    "driverFailureRecoveryRepairActivation": "698d92123d75b40cd5b12d19244829cae308f426",
    "parserAdversaryRepairActivation": "4006fac28ec20f47f136593fd135da36ccee4ea7",
    "nestedDescriptorRepairActivation": "dfadc62bb090580a32f2b0f2a95e74eaefdd7e4d",
    "cleanHeadJavaScratchRepairActivation": CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION,
    "final2048HeapCycleActivation": FINAL_2048_HEAP_CYCLE_ACTIVATION,
    "exactFinalTimeoutBindingActivation": EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION,
    "exactTimeoutReportVerificationActivation": EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION,
    "acceptedR3G04": "5ce645d2ad4dcfc2cd1e5e3c277642b643e1c85c",
    "acceptedR3G04Tree": "c7d44351257cdf907b871d8cc7e5f40f7fbddaf8",
    "acceptedR3G04SpineTree": "7fd38910ba80745dc443f6c40fed0efdda57c8f2",
    "acceptedR3G04EvidenceTree": "5f2e0e649b1ac45475c548f4c57d65b448a9af13",
    "externalKCommit": "4a46d1231473b599c699160132fd6e76a5c46406",
    "externalKRelease": "v7.1.337",
    "frontendJarSha256": "c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2",
}


def validate_accepted_pins(value: object) -> str:
    if not isinstance(value, dict):
        fail("accepted source/tree pin set is not an object")
    implementation_head = value.get("implementationHead")
    if (not isinstance(implementation_head, str)
            or len(implementation_head) != 40
            or any(character not in "0123456789abcdef" for character in implementation_head)):
        fail("accepted pins lack an exact implementation head")
    if value != {**STATIC_ACCEPTED_PINS, "implementationHead": implementation_head}:
        fail("accepted source/tree pin set mismatch")
    return implementation_head


def validate_implementation_commit(root: Path, implementation_head: str) -> None:
    if subprocess.run(
            ["git", "cat-file", "-e", f"{implementation_head}^{{commit}}"],
            cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            check=False).returncode:
        fail("recorded implementation head does not name an existing commit")
    if subprocess.run(
            ["git", "merge-base", "--is-ancestor",
             FINAL_2048_HEAP_CYCLE_ACTIVATION, implementation_head],
            cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            check=False).returncode:
        fail("R3-G-05N activation is not an ancestor of the recorded implementation head")
    if subprocess.run(
            ["git", "merge-base", "--is-ancestor",
             EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION, implementation_head],
            cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            check=False).returncode:
        fail("R3-G-05O activation is not an ancestor of the recorded implementation head")
    if subprocess.run(
            ["git", "merge-base", "--is-ancestor",
             EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION, implementation_head],
            cwd=root, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            check=False).returncode:
        fail("R3-G-05P activation is not an ancestor of the recorded implementation head")


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def require_exact_wall_timeout(record: object, label: str) -> None:
    value = record.get("wallTimeoutSeconds") if isinstance(record, dict) else None
    if type(value) is not int or value != EXACT_FINAL_WALL_TIMEOUT_SECONDS:
        fail(f"{label} does not bind the exact 7200-second wall timeout")


def require_exact_timeout_report(report: object) -> None:
    if (not isinstance(report, str)
            or report.count(EXACT_FINAL_TIMEOUT_REPORT_WITNESS) != 1):
        fail("final Markdown does not contain the unique exact 7200-second timeout witness")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"invalid JSON record {path}: {error}")
    if not isinstance(value, dict):
        fail(f"record is not an object: {path}")
    return value


def physical_child(candidate: Path, parent: Path, *, must_exist: bool) -> Path:
    """Resolve a task path while rejecting lexical traversal and every symlink."""
    if ".." in candidate.parts:
        fail("path traversal is forbidden")
    parent = parent.resolve(strict=True)
    absolute = candidate if candidate.is_absolute() else Path.cwd() / candidate
    probe = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        probe /= part
        if probe.exists() or probe.is_symlink():
            if stat.S_ISLNK(probe.lstat().st_mode):
                fail(f"symlink path component is forbidden: {probe}")
    if must_exist and not absolute.exists():
        fail(f"path does not exist: {absolute}")
    resolved = absolute.resolve(strict=must_exist)
    try:
        relative = resolved.relative_to(parent)
    except ValueError:
        fail(f"path escapes canonical parent: {resolved}")
    if not relative.parts:
        fail("path must be a strict child of the task build directory")
    return resolved


def output_path(root: Path, supplied: Path, *, must_exist: bool) -> Path:
    root = root.resolve(strict=True)
    task_build = root / "spine/rule-applied-allowlist/build"
    probe = root
    for part in ("spine", "rule-applied-allowlist", "build"):
        probe /= part
        if probe.exists() or probe.is_symlink():
            if probe.is_symlink():
                fail(f"task build ancestor may not be a symlink: {probe}")
    ensure_directory(task_build)
    return physical_child(supplied, task_build, must_exist=must_exist)


def regular_files(output: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for path in sorted(output.rglob("*")):
        relative = path.relative_to(output).as_posix()
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            fail(f"raw cache contains a symlink: {relative}")
        if relative in (
            "integrity-manifest.json", "raw-stage.json", "outer-success.json",
            "outer-session.json", "records/watchdog.json", "records/watchdog.done",
        ):
            continue
        if stat.S_ISREG(mode):
            values[relative] = digest(path)
    return values


def semantic_hashes(root: Path) -> dict[str, str]:
    values = {}
    for relative in SEMANTIC_INPUTS:
        path = root / relative
        if not path.is_file() or path.is_symlink():
            fail(f"semantic input is missing or symlinked: {relative}")
        values[relative] = digest(path)
    return values


def git_snapshot(repository: Path) -> dict:
    repository = repository.resolve(strict=True)
    names = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=repository, check=True, stdout=subprocess.PIPE,
    ).stdout.split(b"\0")
    stage_raw = subprocess.run(
        ["git", "ls-files", "-z", "--stage"], cwd=repository, check=True,
        stdout=subprocess.PIPE,
    ).stdout
    stage = {}
    for entry in stage_raw.split(b"\0"):
        if not entry:
            continue
        metadata, encoded_name = entry.split(b"\t", 1)
        mode, object_id, stage_number = metadata.decode().split()
        if stage_number == "0":
            stage[os.fsdecode(encoded_name)] = (mode, object_id)
    files = {}
    for encoded in sorted(item for item in names if item):
        relative = os.fsdecode(encoded)
        path = repository / relative
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            content = os.readlink(path).encode()
            kind = "symlink"
        elif stat.S_ISREG(mode):
            content = path.read_bytes()
            kind = "file"
        elif stat.S_ISDIR(mode) and relative in stage and stage[relative][0] == "160000":
            content = stage[relative][1].encode()
            kind = "gitlink"
        else:
            fail(f"snapshot encountered unsupported path type: {relative}")
        files[relative] = {
            "type": kind,
            "mode": stat.S_IMODE(mode),
            "sha256": hashlib.sha256(content).hexdigest(),
        }
    def git(*arguments: str) -> str:
        return subprocess.run(
            ["git", *arguments], cwd=repository, check=True, text=True,
            stdout=subprocess.PIPE,
        ).stdout
    return {
        "schema": "R3-G-05-git-snapshot-v1",
        "head": git("rev-parse", "HEAD").strip(),
        "indexSha256": hashlib.sha256(stage_raw).hexdigest(),
        "submodules": git("submodule", "status", "--recursive"),
        "files": files,
    }


def write_snapshot(repository: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(
        json.dumps(git_snapshot(repository), sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )


def validate_failure_records(output: Path) -> list[str]:
    names = []
    for path in sorted((output / "records").glob("negative-*.json")):
        record = load(path)
        for field, expected in FAILURE_FIELDS.items():
            if record.get(field) != expected:
                fail(f"failure record {path.name} has invalid {field}")
        if not isinstance(record.get("classification"), str) or not record["classification"]:
            fail(f"failure record {path.name} lacks classification")
        names.append(path.stem.removeprefix("negative-"))
    if set(names) != REQUIRED_NEGATIVE_MODES or len(names) != len(REQUIRED_NEGATIVE_MODES):
        fail("raw cache negative driver record set is not exact")
    return names


def validate_parser_record(output: Path) -> dict:
    record = load(output / "records/parser-canonicality-selftest.json")
    cases = record.get("cases")
    if record.get("schema") != "R3-G-05-parser-canonicality-v1" or not isinstance(cases, list):
        fail("parser canonicality record has invalid schema")
    expected = {
        "canonical-result-accepted",
        "leading-zero-integer-rejected",
        "negative-zero-path-rejected",
        "unicode-escape-rejected",
        "missing-delimiter-rejected",
        "multiple-result-rejected",
        "residual-result-rejected",
        "unknown-result-rejected",
    }
    actual = {case.get("name") for case in cases if isinstance(case, dict)}
    if actual != expected or len(cases) != len(expected):
        fail("parser canonicality cases are not exact")
    for case in cases:
        if (case.get("status") != "pass" or case.get("backendInvocations") != 0
                or case.get("outputDefinitionConstructed") is not False):
            fail("parser canonicality case lacks zero-backend facts")
    return record


def validate_snapshots(output: Path, implementation_head: str) -> None:
    pairs = (
        ("records/repository-snapshot-before.json", "records/repository-snapshot-after.json"),
        ("records/external-k-snapshot-before.json", "records/external-k-snapshot-after.json"),
        ("records/expected-path-scan-before.txt", "records/expected-path-scan-after.txt"),
    )
    for before, after in pairs:
        if not (output / before).is_file() or not (output / after).is_file():
            fail(f"snapshot pair is missing: {before}")
        if (output / before).read_bytes() != (output / after).read_bytes():
            fail(f"snapshot changed across raw execution: {before}")
    for relative in (
            "records/repository-snapshot-before.json",
            "records/repository-snapshot-after.json"):
        snapshot = load(output / relative)
        if (snapshot.get("schema") != "R3-G-05-git-snapshot-v1"
                or snapshot.get("head") != implementation_head):
            fail(f"repository snapshot does not bind the implementation head: {relative}")


def validate_raw_claims(output: Path, *, allow_active_stage: bool = False,
                        require_outer: bool = True) -> str:
    if (output / "raw-failure.json").exists() or (output / "raw-failure.json").is_symlink():
        fail("raw cache contains a terminal failure marker")
    if (not allow_active_stage
            and ((output / "raw-stage.json").exists() or (output / "raw-stage.json").is_symlink())):
        fail("raw cache contains an unterminated stage record")
    if not (output / "raw-success.json").is_file() or (output / "raw-success.json").is_symlink():
        fail("raw cache lacks a terminal success record")
    raw = load(output / "raw-success.json")
    if raw.get("schema") != "R3-G-05-raw-success-v1" or raw.get("terminal") is not True:
        fail("raw success record is not terminal")
    require_exact_wall_timeout(raw, "raw success record")
    implementation_head = validate_accepted_pins(raw.get("acceptedPins"))
    if raw.get("implementationHead") != implementation_head:
        fail("raw success does not bind the accepted implementation head")
    required_true = (
        "successful", "authorized", "serial", "nonblockingFlock", "loweredPriority",
        "dedicatedSession", "boundedTimeout", "watchdogEnabled",
        "watchdogReadinessBeforeExecution", "watchdogPidfdGenerationBound",
        "privateWatchdogReadinessAuthenticated", "watchdogOnlyGateRelease",
        "doubleBracketedSessionSelection", "nonInferentialExitClassification",
        "descriptorOwnerGenerationBound", "descriptorOwnerFdExcludedFromTarget",
        "separateLauncherAndDescriptorOwnerPidfds",
        "nestedBoundaryPrePostChecks", "provisionalResultsRejectedOnPostcheckFailure",
    )
    if any(raw.get(field) is not True for field in required_true):
        fail("raw success record is missing a required resource fact")
    if raw.get("javaMaxHeapMiB") != 2048 or raw.get("javaActiveProcessorCount") != 2:
        fail("raw success record does not use packet defaults")
    if raw.get("hardMaxHeapMiB") != 2048 or raw.get("hardMaxProcessors") != 2:
        fail("raw success record does not bind hard maxima")
    descriptor_pid = raw.get("descriptorOwnerPid")
    descriptor_start = raw.get("descriptorOwnerStartTimeTicks")
    if (not isinstance(descriptor_pid, int) or descriptor_pid <= 0
            or not isinstance(descriptor_start, int) or descriptor_start <= 0
            or raw.get("descriptorOwnerFd") != 198
            or not isinstance(raw.get("outputDevice"), int)
            or raw.get("outputDevice") < 0
            or not isinstance(raw.get("outputInode"), int)
            or raw.get("outputInode") <= 0
            or raw.get("descriptorOwnerPath") != f"/proc/{descriptor_pid}/fd/198"):
        fail("raw success record does not bind the exact outer descriptor owner")
    if raw.get("substantiveFullOracleCycleCount") != 5:
        fail("R3-G-05N raw success cycle count is not exactly five")
    if require_outer:
        validate_outer_terminal(output)
    validate_failure_records(output)
    mutation_sensitivity.cached_record_check(output / "records")
    validate_parser_record(output)
    validate_snapshots(output, implementation_head)
    required = {
        "raw-success.json", "records/instrumented-a.json", "records/instrumented-b.json",
        "records/runtime-projector-selftest.json", "records/parser-canonicality-selftest.json",
        "records/watchdog.json", "records/watchdog.ready.json",
        "logs/parser-self-test.stdout", "logs/parser-self-test.stderr",
        "logs/jdk-option-precedence.stdout", "logs/jdk-option-precedence.stderr",
        "instrumented-a/definition.kore", "instrumented-b/definition.kore",
        "instrumented-a/macros.kore", "instrumented-b/macros.kore",
        "instrumented-a/syntaxDefinition.kore", "instrumented-b/syntaxDefinition.kore",
        "projections/instrumented-a-definition.normalized.kore",
        "projections/instrumented-b-definition.normalized.kore",
    }
    for label in ("bump-state", "drop-state"):
        required.add(f"projections/instrumented-a-{label}.kore")
        required.add(f"projections/instrumented-b-{label}.kore")
    for program in ("bump-drop", "drop-bump", "bump-bump", "neither"):
        required.add(f"projections/ordinary-{program}.json")
        required.add(f"runtime/ordinary-{program}.pretty")
        for suffix in ("a", "b"):
            required.update({
                f"runtime/instrumented-{suffix}-{program}.pretty",
                f"runtime/baseline-{suffix}-{program}.pretty",
                f"projections/instrumented-{suffix}-{program}.json",
                f"projections/instrumented-{suffix}-{program}-erased.json",
                f"projections/baseline-{suffix}-{program}.json",
            })
    for mode in REQUIRED_NEGATIVE_MODES:
        required.add(f"records/negative-{mode}.json")
        required.add(f"logs/negative-{mode}.stdout")
        required.add(f"logs/negative-{mode}.stderr")
    missing = sorted(name for name in required if not (output / name).is_file())
    if missing:
        fail("raw cache required file set is incomplete: " + ", ".join(missing[:8]))
    for relative in PROVISIONAL:
        if not (output / relative).is_file():
            fail(f"provisional evidence is missing: {relative}")
    return implementation_head


def create_manifest(root: Path, output: Path) -> None:
    if (output / "integrity-manifest.json").exists():
        fail("initial manifest creation refuses an existing manifest")
    implementation_head = validate_raw_claims(
        output, allow_active_stage=True, require_outer=False)
    validate_implementation_commit(root, implementation_head)
    raw = load(output / "raw-success.json")
    manifest = {
        "schema": SCHEMA,
        "wallTimeoutSeconds": EXACT_FINAL_WALL_TIMEOUT_SECONDS,
        "semanticInputs": semantic_hashes(root),
        "acceptedPins": raw.get("acceptedPins"),
        "files": regular_files(output),
    }
    if validate_accepted_pins(manifest["acceptedPins"]) != implementation_head:
        fail("raw record does not bind the exact accepted implementation head")
    publish_integrity_manifest(output, manifest)


def validate_outer_terminal(output: Path, manifest: dict | None = None) -> dict:
    outer_path = output / "outer-success.json"
    session_path = output / "outer-session.json"
    watchdog_path = output / "records/watchdog.json"
    ready_path = output / "records/watchdog.ready.json"
    for path, label in ((outer_path, "outer success"), (session_path, "outer session"),
                        (watchdog_path, "watchdog"), (ready_path, "watchdog readiness")):
        if not path.is_file() or path.is_symlink():
            fail(f"raw cache lacks a regular {label} record")
    if (output / "raw-stage.json").exists() or (output / "raw-stage.json").is_symlink():
        fail("raw cache contains an active outer journal")
    outer = load(outer_path)
    session = load(session_path)
    watchdog = load(watchdog_path)
    ready = load(ready_path)
    watchdog_done = output / "records/watchdog.done"
    manifest_path = output / "integrity-manifest.json"
    expected_manifest_hash = digest(manifest_path)
    if (outer.get("schema") != "R3-G-05-outer-success-v1"
            or outer.get("terminal") is not True
            or outer.get("innerStatus") != 0
            or outer.get("integrityManifestSha256") != expected_manifest_hash
            or outer.get("sessionRecordSha256") != digest(session_path)
            or outer.get("watchdogRecordSha256") != digest(watchdog_path)
            or outer.get("watchdogReadySha256") != digest(ready_path)):
        fail("outer success does not bind terminal validation")
    raw = load(output / "raw-success.json")
    if (session.get("schema") != "R3-G-05-outer-session-v1"
            or session.get("wallTimeoutSeconds") != EXACT_FINAL_WALL_TIMEOUT_SECONDS
            or session.get("wallTimeoutSeconds") != raw.get("wallTimeoutSeconds")
            or session.get("innerStatus") != 0
            or session.get("reason") != "inner-success"
            or session.get("targetSessionEmpty") is not True
            or session.get("watchdogStatus") != 0
            or session.get("watchdogDisarmedAfterEmpty") is not True
            or session.get("watchdogDisposition") != "disarmed-after-successful-empty"
            or session.get("watchdogReadinessValidated") is not True
            or session.get("privateWatchdogReadinessValidated") is not True
            or session.get("watchdogReadySha256") != digest(ready_path)
            or session.get("rawCommandReleased") is not True
            or session.get("watchdogOnlyGateReleaseAcknowledged") is not True
            or session.get("targetGateReleaseAcknowledged") is not True
            or session.get("doubleBracketedSessionSelection") is not True
            or session.get("nonInferentialExitClassification") is not True
            or session.get("descriptorOwnerGenerationValidated") is not True
            or session.get("descriptorOwnerFdExcludedFromTarget") is not True
            or session.get("nestedBoundaryPrePostChecks") is not True
            or session.get("provisionalResultsRejectedOnPostcheckFailure") is not True
            or session.get("watchdogDoneSha256") != WATCHDOG_DONE_SHA256
            or not watchdog_done.is_file() or watchdog_done.is_symlink()
            or digest(watchdog_done) != WATCHDOG_DONE_SHA256):
        fail("outer session record is not a successful empty-session proof")
    session_id = session.get("sessionId")
    session_start = session.get("sessionStartTimeTicks")
    if (not isinstance(session_id, int) or session_id <= 0
            or not isinstance(session_start, int) or session_start <= 0
            or session_members(session_id, session_start)):
        fail("target raw session is not currently empty")
    output_identity = output.stat()
    if ((session.get("outputDevice"), session.get("outputInode"))
            != (output_identity.st_dev, output_identity.st_ino)
            or (raw.get("outputDevice"), raw.get("outputInode"))
            != (output_identity.st_dev, output_identity.st_ino)):
        fail("reserved output identity changed after terminal completion")
    descriptor_pid = session.get("descriptorOwnerPid")
    descriptor_start = session.get("descriptorOwnerStartTimeTicks")
    if (not isinstance(descriptor_pid, int) or descriptor_pid <= 0
            or not isinstance(descriptor_start, int) or descriptor_start <= 0
            or descriptor_pid == session.get("ownerPid")
            or session.get("descriptorOwnerFd") != 198
            or session.get("descriptorOwnerPath") != f"/proc/{descriptor_pid}/fd/198"):
        fail("outer session does not bind the distinct fixed descriptor owner")
    if (watchdog.get("schema") != "R3-G-05-session-watchdog-v1"
            or watchdog.get("fired") is not False
            or watchdog.get("completed") is not True
            or watchdog.get("sessionTerminationProven") is not True
            or watchdog.get("sessionStartTimeTicks") != session_start
            or watchdog.get("readinessPublished") is not True
            or watchdog.get("privateReadinessAuthenticated") is not True
            or watchdog.get("supervisorApprovalValidated") is not True
            or watchdog.get("watchdogOnlyGateRelease") is not True
            or watchdog.get("pidfdGenerationBound") is not True
            or watchdog.get("descriptorOwnerPidfdGenerationBound") is not True
            or watchdog.get("launcherOwnerPidfdGenerationBound") is not True
            or watchdog.get("descriptorOwnerBindingsRetainedThroughTeardown") is not True
            or watchdog.get("ownerPid") != session.get("ownerPid")
            or watchdog.get("ownerStartTimeTicks") != session.get("ownerStartTimeTicks")
            or watchdog.get("descriptorOwnerPid") != session.get("descriptorOwnerPid")
            or watchdog.get("descriptorOwnerStartTimeTicks")
            != session.get("descriptorOwnerStartTimeTicks")
            or watchdog.get("descriptorOwnerFd") != session.get("descriptorOwnerFd")
            or watchdog.get("descriptorOwnerPath") != session.get("descriptorOwnerPath")
            or watchdog.get("rssLimitMiB") != 6144
            or watchdog.get("availableMemoryFloorMiB") != 4096
            or watchdog.get("swapFreeFloorMiB") != 1024
            or not isinstance(watchdog.get("peakSessionRssKiB"), int)):
        fail("watchdog record is invalid")
    if (ready.get("schema") != "R3-G-05-watchdog-ready-v1"
            or ready.get("pidfdGenerationBound") is not True
            or ready.get("target", {}).get("pid") != session_id
            or ready.get("target", {}).get("sessionId") != session_id
            or ready.get("target", {}).get("processGroupId") != session_id
            or ready.get("target", {}).get("startTimeTicks") != session_start
            or ready.get("owner", {}).get("pid") != session.get("ownerPid")
            or ready.get("owner", {}).get("startTimeTicks")
            != session.get("ownerStartTimeTicks")
            or ready.get("descriptorOwner", {}).get("pid")
            != session.get("descriptorOwnerPid")
            or ready.get("descriptorOwner", {}).get("startTimeTicks")
            != session.get("descriptorOwnerStartTimeTicks")
            or ready.get("outputDescriptor") != {
                "fd": session.get("descriptorOwnerFd"),
                "device": session.get("outputDevice"),
                "inode": session.get("outputInode"),
                "ownerPath": session.get("descriptorOwnerPath"),
            }
            or ready.get("watchdog", {}).get("pid") != watchdog.get("watchdogPid")
            or ready.get("watchdog", {}).get("startTimeTicks")
            != watchdog.get("watchdogStartTimeTicks")):
        fail("watchdog readiness record is invalid")
    if outer.get("sessionId") != session_id:
        fail("outer success target session identity mismatch")
    return outer


def validate_manifest(root: Path, output: Path, *, allow_provisional_refresh: bool = False) -> dict:
    if (output / "raw-failure.json").exists() or (output / "raw-failure.json").is_symlink():
        fail("raw cache contains a terminal failure marker")
    if (output / "raw-stage.json").exists() or (output / "raw-stage.json").is_symlink():
        fail("raw cache contains an unterminated stage record")
    if not (output / "raw-success.json").is_file() or (output / "raw-success.json").is_symlink():
        fail("raw cache lacks a terminal success record")
    if (output / "integrity-manifest.json").is_symlink():
        fail("raw integrity manifest may not be a symlink")
    manifest = load(output / "integrity-manifest.json")
    if manifest.get("schema") != SCHEMA:
        fail("raw integrity manifest schema mismatch")
    require_exact_wall_timeout(manifest, "raw integrity manifest")
    implementation_head = validate_accepted_pins(manifest.get("acceptedPins"))
    validate_implementation_commit(root, implementation_head)
    if manifest.get("semanticInputs") != semantic_hashes(root):
        fail("a semantic input changed after the raw run")
    current = regular_files(output)
    expected_files = manifest.get("files")
    if allow_provisional_refresh and isinstance(expected_files, dict):
        expected_files = {name: value for name, value in expected_files.items()
                          if name not in PROVISIONAL}
        current = {name: value for name, value in current.items() if name not in PROVISIONAL}
    if expected_files != current:
        expected = expected_files if isinstance(expected_files, dict) else {}
        changed = sorted(set(expected) ^ set(current) | {
            name for name in set(expected) & set(current) if expected[name] != current[name]
        })
        fail("raw integrity manifest mismatch: " + ", ".join(changed[:8]))
    if validate_raw_claims(output) != implementation_head:
        fail("manifest and raw success implementation heads differ")
    return manifest


def refresh_manifest(root: Path, output: Path) -> None:
    fail("terminal manifest refresh is forbidden; cached finalization must be byte-identical")


def complete_outer(root: Path, output: Path) -> None:
    if (output / "raw-stage.json").is_symlink():
        fail("active outer journal may not be a symlink")
    if not (output / "raw-stage.json").is_file():
        fail("outer completion lacks its active journal")
    stage = load(output / "raw-stage.json")
    if (stage.get("schema") != "R3-G-05-raw-stage-v1"
            or stage.get("active") is not True
            or stage.get("stage") != "integrity-manifest"):
        fail("outer completion has a malformed active journal")
    if (output / "raw-failure.json").exists() or (output / "raw-failure.json").is_symlink():
        fail("outer completion refuses a failure marker")
    for path, label in (
        (output / "integrity-manifest.json", "integrity manifest"),
        (output / "outer-session.json", "outer session"),
        (output / "records/watchdog.json", "watchdog"),
        (output / "records/watchdog.ready.json", "watchdog readiness"),
    ):
        if not path.is_file() or path.is_symlink():
            fail(f"outer completion lacks a regular {label} record")
    manifest = load(output / "integrity-manifest.json")
    if manifest.get("schema") != SCHEMA:
        fail("raw integrity manifest schema mismatch")
    require_exact_wall_timeout(manifest, "raw integrity manifest")
    if manifest.get("semanticInputs") != semantic_hashes(root):
        fail("a semantic input changed before outer completion")
    implementation_head = validate_accepted_pins(manifest.get("acceptedPins"))
    validate_implementation_commit(root, implementation_head)
    # Validate the manifest-bound inner cache while the journal is deliberately active.
    if validate_raw_claims(
            output, allow_active_stage=True, require_outer=False) != implementation_head:
        fail("manifest and raw success implementation heads differ")
    expected = manifest.get("files")
    if expected != regular_files(output):
        fail("raw integrity manifest changed before outer completion")
    session = load(output / "outer-session.json")
    watchdog = load(output / "records/watchdog.json")
    raw = load(output / "raw-success.json")
    ready_path = output / "records/watchdog.ready.json"
    ready = load(ready_path)
    watchdog_done = output / "records/watchdog.done"
    output_identity = output.stat()
    if ((session.get("outputDevice"), session.get("outputInode"))
            != (output_identity.st_dev, output_identity.st_ino)
            or (raw.get("outputDevice"), raw.get("outputInode"))
            != (output_identity.st_dev, output_identity.st_ino)):
        fail("reserved output descriptor identity changed before outer completion")
    session_id = session.get("sessionId")
    session_start = session.get("sessionStartTimeTicks")
    descriptor_pid = session.get("descriptorOwnerPid")
    descriptor_start = session.get("descriptorOwnerStartTimeTicks")
    if (session.get("schema") != "R3-G-05-outer-session-v1"
            or session.get("wallTimeoutSeconds") != EXACT_FINAL_WALL_TIMEOUT_SECONDS
            or session.get("wallTimeoutSeconds") != raw.get("wallTimeoutSeconds")
            or not isinstance(session_id, int) or session_id <= 0
            or not isinstance(session_start, int) or session_start <= 0
            or session.get("innerStatus") != 0 or session.get("reason") != "inner-success"
            or session.get("targetSessionEmpty") is not True
            or session.get("watchdogStatus") != 0
            or session.get("watchdogDisarmedAfterEmpty") is not True
            or session.get("watchdogDisposition") != "disarmed-after-successful-empty"
            or session.get("watchdogReadinessValidated") is not True
            or session.get("privateWatchdogReadinessValidated") is not True
            or session.get("watchdogReadySha256") != digest(ready_path)
            or session.get("rawCommandReleased") is not True
            or session.get("watchdogOnlyGateReleaseAcknowledged") is not True
            or session.get("targetGateReleaseAcknowledged") is not True
            or session.get("doubleBracketedSessionSelection") is not True
            or session.get("nonInferentialExitClassification") is not True
            or session.get("descriptorOwnerGenerationValidated") is not True
            or session.get("descriptorOwnerFdExcludedFromTarget") is not True
            or session.get("nestedBoundaryPrePostChecks") is not True
            or session.get("provisionalResultsRejectedOnPostcheckFailure") is not True
            or not isinstance(descriptor_pid, int) or descriptor_pid <= 0
            or not isinstance(descriptor_start, int) or descriptor_start <= 0
            or descriptor_pid == session.get("ownerPid")
            or session.get("descriptorOwnerFd") != 198
            or session.get("descriptorOwnerPath") != f"/proc/{descriptor_pid}/fd/198"
            or session.get("watchdogDoneSha256") != WATCHDOG_DONE_SHA256
            or not watchdog_done.is_file() or watchdog_done.is_symlink()
            or digest(watchdog_done) != WATCHDOG_DONE_SHA256
            or session_members(session_id, session_start)):
        fail("outer completion lacks successful empty-session verification")
    if (watchdog.get("schema") != "R3-G-05-session-watchdog-v1"
            or watchdog.get("completed") is not True or watchdog.get("fired") is not False
            or watchdog.get("sessionTerminationProven") is not True
            or watchdog.get("sessionStartTimeTicks") != session_start
            or watchdog.get("readinessPublished") is not True
            or watchdog.get("privateReadinessAuthenticated") is not True
            or watchdog.get("supervisorApprovalValidated") is not True
            or watchdog.get("watchdogOnlyGateRelease") is not True
            or watchdog.get("pidfdGenerationBound") is not True
            or watchdog.get("descriptorOwnerPidfdGenerationBound") is not True
            or watchdog.get("launcherOwnerPidfdGenerationBound") is not True
            or watchdog.get("descriptorOwnerBindingsRetainedThroughTeardown") is not True
            or watchdog.get("ownerPid") != session.get("ownerPid")
            or watchdog.get("ownerStartTimeTicks") != session.get("ownerStartTimeTicks")
            or watchdog.get("descriptorOwnerPid") != descriptor_pid
            or watchdog.get("descriptorOwnerStartTimeTicks") != descriptor_start
            or watchdog.get("descriptorOwnerFd") != 198
            or watchdog.get("descriptorOwnerPath") != f"/proc/{descriptor_pid}/fd/198"
            or watchdog.get("rssLimitMiB") != 6144
            or watchdog.get("availableMemoryFloorMiB") != 4096
            or watchdog.get("swapFreeFloorMiB") != 1024
            or not isinstance(watchdog.get("peakSessionRssKiB"), int)):
        fail("outer completion lacks successful watchdog termination")
    if (ready.get("schema") != "R3-G-05-watchdog-ready-v1"
            or ready.get("pidfdGenerationBound") is not True
            or ready.get("target", {}).get("pid") != session_id
            or ready.get("target", {}).get("sessionId") != session_id
            or ready.get("target", {}).get("processGroupId") != session_id
            or ready.get("target", {}).get("startTimeTicks") != session_start
            or ready.get("owner", {}).get("pid") != session.get("ownerPid")
            or ready.get("owner", {}).get("startTimeTicks")
            != session.get("ownerStartTimeTicks")
            or ready.get("descriptorOwner", {}).get("pid") != descriptor_pid
            or ready.get("descriptorOwner", {}).get("startTimeTicks") != descriptor_start
            or ready.get("outputDescriptor") != {
                "fd": 198,
                "device": output_identity.st_dev,
                "inode": output_identity.st_ino,
                "ownerPath": f"/proc/{descriptor_pid}/fd/198",
            }
            or ready.get("watchdog", {}).get("pid") != watchdog.get("watchdogPid")
            or ready.get("watchdog", {}).get("startTimeTicks")
            != watchdog.get("watchdogStartTimeTicks")):
        fail("outer completion lacks validated watchdog readiness")
    publish_outer_success(output, {
        "schema": "R3-G-05-outer-success-v1",
        "terminal": True,
        "innerStatus": 0,
        "sessionId": session_id,
        "integrityManifestSha256": digest(output / "integrity-manifest.json"),
        "sessionRecordSha256": digest(output / "outer-session.json"),
        "watchdogRecordSha256": digest(output / "records/watchdog.json"),
        "watchdogReadySha256": digest(ready_path),
    })
    durable_unlink(output / "raw-stage.json")


def publish(root: Path, output: Path) -> None:
    validate_manifest(root, output)
    evidence_parent = (root / "evidence").resolve(strict=True)
    evidence = evidence_parent / "r3-g-05-atomic-rule-applied-allowlist"
    if evidence.exists() and evidence.is_symlink():
        fail("committed evidence directory may not be a symlink")
    evidence.mkdir(parents=True, exist_ok=True)
    physical_child(evidence, evidence_parent, must_exist=True)
    extras = {item.name for item in evidence.iterdir()} - {"results.json", "report.md"}
    if extras:
        fail("committed evidence directory contains unexpected paths")
    stage = Path(tempfile.mkdtemp(prefix=".r3-g-05-publish-", dir=evidence_parent))
    for relative in PROVISIONAL:
        source = output / relative
        shutil.copyfile(source, stage / Path(relative).name)
        if digest(source) != digest(stage / Path(relative).name):
            fail("provisional evidence changed while staging publication")
    validate_manifest(root, output)
    try:
        for name in ("results.json", "report.md"):
            atomic_write(evidence / name, (stage / name).read_bytes())
    finally:
        shutil.rmtree(stage, ignore_errors=True)


def self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="r3-g-05-cache-test-") as directory:
        base = Path(directory)
        root = base / "repo"
        output = root / "spine/rule-applied-allowlist/build/cache"
        output.mkdir(parents=True)
        # Exercise path confinement independently of repository-specific inputs.
        good = physical_child(output, root / "spine/rule-applied-allowlist/build", must_exist=True)
        assert good == output.resolve()
        for bad in (root / "spine/rule-applied-allowlist/build/../escape", base / "escape"):
            try:
                physical_child(bad, root / "spine/rule-applied-allowlist/build", must_exist=False)
            except SystemExit:
                pass
            else:
                raise AssertionError("path escape was accepted")
        symlink = root / "spine/rule-applied-allowlist/build/link"
        symlink.symlink_to(base)
        try:
            physical_child(symlink / "escape", root / "spine/rule-applied-allowlist/build", must_exist=False)
        except SystemExit:
            pass
        else:
            raise AssertionError("symlink escape was accepted")

        # Atomic leaf reservation has one winner and never follows a precreated
        # symlink into the outside sentinel directory.
        task_build = root / "spine/rule-applied-allowlist/build"
        raced = task_build / "reservation-race"
        outcomes: list[str] = []
        barrier = threading.Barrier(2)
        def reserve_racer() -> None:
            barrier.wait()
            try:
                reserve_output(task_build, raced)
                outcomes.append("reserved")
            except (FileExistsError, OSError, SecureIOError):
                outcomes.append("refused")
        racers = [threading.Thread(target=reserve_racer) for _ in range(2)]
        for racer in racers:
            racer.start()
        for racer in racers:
            racer.join()
        assert sorted(outcomes) == ["refused", "reserved"]
        outside = base / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel"
        sentinel.write_text("unchanged\n", encoding="utf-8")
        linked_leaf = task_build / "linked-output"
        linked_leaf.symlink_to(outside, target_is_directory=True)
        try:
            reserve_output(task_build, linked_leaf)
        except (FileExistsError, OSError, SecureIOError):
            pass
        else:
            raise AssertionError("precreated symlink output leaf was reserved")
        assert sentinel.read_text(encoding="utf-8") == "unchanged\n"

        # Old predictable temporaries and target symlinks cannot redirect a
        # secure marker write. A target-swap race may reject or replace only the
        # owned directory entry, never the outside sentinel.
        marker_dir = task_build / "marker-adversary"
        marker_dir.mkdir()
        predictable = marker_dir / ".raw-stage.json.tmp"
        predictable.symlink_to(sentinel)
        atomic_write(marker_dir / "raw-stage.json", b"safe\n")
        assert sentinel.read_text(encoding="utf-8") == "unchanged\n"
        target = marker_dir / "raw-failure.json"
        target.symlink_to(sentinel)
        try:
            atomic_write(target, b"refused\n")
        except SecureIOError:
            pass
        else:
            raise AssertionError("marker target symlink was followed or replaced")
        assert sentinel.read_text(encoding="utf-8") == "unchanged\n"
        target.unlink()
        stop_swap = threading.Event()
        def swap_target() -> None:
            while not stop_swap.is_set():
                try:
                    target.unlink()
                except FileNotFoundError:
                    pass
                try:
                    target.symlink_to(sentinel)
                except FileExistsError:
                    pass
        swapper = threading.Thread(target=swap_target)
        swapper.start()
        try:
            for _ in range(50):
                try:
                    atomic_write(target, b"race-safe\n")
                except (FileNotFoundError, SecureIOError):
                    pass
        finally:
            stop_swap.set()
            swapper.join()
        assert sentinel.read_text(encoding="utf-8") == "unchanged\n"

        # Every absent-only terminal name has a deterministic first-writer
        # adversary. Pause after its initial target check, create attacker bytes,
        # then prove the kernel no-replace commit refuses without changing them.
        publisher_cases = (
            ("raw-stage.json", lambda base: secure_io_module.publish_initial_journal(
                base, {"writer": "legitimate"})),
            ("raw-success.json", lambda base: secure_io_module.publish_raw_success(
                base, {"writer": "legitimate"})),
            ("raw-failure.json", lambda base: secure_io_module.publish_raw_failure(
                base, {"schema": "R3-G-05-raw-failure-v1", "stage": "legitimate",
                       "exitStatus": 1})),
            ("integrity-manifest.json", lambda base: secure_io_module.publish_integrity_manifest(
                base, {"writer": "legitimate"})),
            ("outer-session.json", lambda base: secure_io_module.publish_outer_session(
                base, {"writer": "legitimate"})),
            ("outer-success.json", lambda base: secure_io_module.publish_outer_success(
                base, {"writer": "legitimate"})),
            ("watchdog.ready.json", lambda base: secure_io_module.publish_watchdog_ready(
                base, {"writer": "legitimate"})),
            ("watchdog.done", lambda base: secure_io_module.publish_watchdog_done(
                base, b"legitimate\n")),
        )
        first_writer_dir = marker_dir / "first-writer"
        first_writer_dir.mkdir()
        original_target_state = secure_io_module._target_state
        attacker = b"attacker-first-writer\n"
        for marker_name, production_publisher in publisher_cases:
            marker = first_writer_dir / marker_name
            checked = threading.Event()
            resume = threading.Event()
            paused = [False]
            errors: list[BaseException] = []

            def pause_after_check(directory_fd: int, name: str) -> os.stat_result | None:
                state = original_target_state(directory_fd, name)
                if name == marker_name and state is None and not paused[0]:
                    paused[0] = True
                    checked.set()
                    if not resume.wait(timeout=2):
                        raise AssertionError("first-writer adversary did not resume")
                return state

            def absent_writer() -> None:
                try:
                    production_publisher(first_writer_dir)
                except BaseException as error:
                    errors.append(error)

            secure_io_module._target_state = pause_after_check
            writer = threading.Thread(target=absent_writer)
            try:
                writer.start()
                if not checked.wait(timeout=2):
                    raise AssertionError(f"{marker_name} did not pause after its absence check")
                marker.write_bytes(attacker)
                resume.set()
                writer.join(timeout=2)
                if writer.is_alive():
                    raise AssertionError(f"{marker_name} first-writer adversary did not finish")
                if (len(errors) != 1 or not isinstance(errors[0], SecureIOError)
                        or marker.read_bytes() != attacker):
                    raise AssertionError(
                        f"{marker_name} absent-only write replaced the first writer")
                leftovers = list(first_writer_dir.glob(f".{marker_name}.*.tmp"))
                if leftovers:
                    raise AssertionError(f"{marker_name} left temporary names: {leftovers}")
            finally:
                resume.set()
                writer.join(timeout=2)
                secure_io_module._target_state = original_target_state
            marker.unlink()

        # Failure recovery alone is idempotent for a valid regular first writer.
        # Later recovery stages cannot change its authoritative bytes. Malformed,
        # symlink, and non-regular first writers remain closed and unchanged.
        recovery_dir = marker_dir / "failure-recovery"
        recovery_dir.mkdir()
        valid_failure = {
            "schema": "R3-G-05-raw-failure-v1",
            "stage": "first-recovery",
            "exitStatus": 37,
        }
        secure_io_module.publish_raw_failure(recovery_dir, valid_failure)
        failure_marker = recovery_dir / "raw-failure.json"
        first_bytes = failure_marker.read_bytes()
        secure_io_module.publish_raw_failure(recovery_dir, {
            "schema": "R3-G-05-raw-failure-v1",
            "stage": "second-recovery",
            "exitStatus": 99,
        })
        if failure_marker.read_bytes() != first_bytes:
            raise AssertionError("repeated recovery changed the valid first-writer bytes")

        valid_race_dir = marker_dir / "valid-failure-race"
        valid_race_dir.mkdir()
        valid_race_marker = valid_race_dir / "raw-failure.json"
        racing_value = {
            "schema": "R3-G-05-raw-failure-v1",
            "stage": "racing-first-writer",
            "exitStatus": 71,
        }
        racing_bytes = (json.dumps(racing_value, sort_keys=True, indent=2) + "\n").encode()
        race_checked = threading.Event()
        race_resume = threading.Event()
        race_paused = [False]
        race_errors: list[BaseException] = []

        def pause_failure_absence(directory_fd: int, name: str) -> os.stat_result | None:
            state = original_target_state(directory_fd, name)
            if name == "raw-failure.json" and state is None and not race_paused[0]:
                race_paused[0] = True
                race_checked.set()
                if not race_resume.wait(timeout=2):
                    raise AssertionError("valid failure race did not resume")
            return state

        def recovery_racer() -> None:
            try:
                secure_io_module.publish_raw_failure(valid_race_dir, valid_failure)
            except BaseException as error:
                race_errors.append(error)

        secure_io_module._target_state = pause_failure_absence
        recovery_writer = threading.Thread(target=recovery_racer)
        try:
            recovery_writer.start()
            if not race_checked.wait(timeout=2):
                raise AssertionError("valid failure recovery did not pause after absence check")
            valid_race_marker.write_bytes(racing_bytes)
            race_resume.set()
            recovery_writer.join(timeout=2)
            if recovery_writer.is_alive() or race_errors:
                raise AssertionError(f"valid failure recovery race failed: {race_errors!r}")
            if valid_race_marker.read_bytes() != racing_bytes:
                raise AssertionError("valid racing first writer was changed")
            leftovers = list(valid_race_dir.glob(".raw-failure.json.*.tmp"))
            if leftovers:
                raise AssertionError(f"valid failure race left temporary names: {leftovers}")
        finally:
            race_resume.set()
            recovery_writer.join(timeout=2)
            secure_io_module._target_state = original_target_state

        invalid_failures = {
            "invalid-json": b"malformed-first-writer\n",
            "nonobject": b"[]\n",
            "wrong-schema": (json.dumps({
                "schema": "wrong-schema", "stage": "first", "exitStatus": 1,
            }) + "\n").encode(),
            "empty-stage": (json.dumps({
                "schema": "R3-G-05-raw-failure-v1", "stage": "", "exitStatus": 1,
            }) + "\n").encode(),
            "nonstring-stage": (json.dumps({
                "schema": "R3-G-05-raw-failure-v1", "stage": 7, "exitStatus": 1,
            }) + "\n").encode(),
            "boolean-status": (json.dumps({
                "schema": "R3-G-05-raw-failure-v1", "stage": "first", "exitStatus": True,
            }) + "\n").encode(),
            "noninteger-status": (json.dumps({
                "schema": "R3-G-05-raw-failure-v1", "stage": "first", "exitStatus": 1.5,
            }) + "\n").encode(),
            "extra-field": (json.dumps({
                "schema": "R3-G-05-raw-failure-v1", "stage": "first", "exitStatus": 1,
                "extra": True,
            }) + "\n").encode(),
        }
        for description, invalid_bytes in invalid_failures.items():
            failure_marker.write_bytes(invalid_bytes)
            try:
                secure_io_module.publish_raw_failure(recovery_dir, valid_failure)
            except SecureIOError:
                pass
            else:
                raise AssertionError(f"{description} failure first writer was accepted")
            if failure_marker.read_bytes() != invalid_bytes:
                raise AssertionError(f"{description} failure first writer was changed")
        failure_marker.unlink()
        failure_marker.symlink_to(sentinel)
        try:
            secure_io_module.publish_raw_failure(recovery_dir, valid_failure)
        except SecureIOError:
            pass
        else:
            raise AssertionError("symlink failure first writer was accepted")
        if not failure_marker.is_symlink() or sentinel.read_text(encoding="utf-8") != "unchanged\n":
            raise AssertionError("symlink failure first writer or target was changed")
        failure_marker.unlink()
        failure_marker.mkdir()
        try:
            secure_io_module.publish_raw_failure(recovery_dir, valid_failure)
        except SecureIOError:
            pass
        else:
            raise AssertionError("non-regular failure first writer was accepted")
        if not failure_marker.is_dir():
            raise AssertionError("non-regular failure first writer was changed")

        # Nonterminal stage progress deliberately retains atomic replace mode.
        progress = first_writer_dir / "raw-stage.json"
        progress.write_bytes(attacker)
        atomic_write_json(progress, {"stage": "next", "active": True})
        if load(progress) != {"stage": "next", "active": True}:
            raise AssertionError("replace-mode progress marker did not advance")

        # Mutation coverage is deliberately over every manifest-bound cache file.
        (output / "a").write_text("a\n", encoding="utf-8")
        (output / "b").write_text("b\n", encoding="utf-8")
        files = regular_files(output)
        manifest = {"schema": SCHEMA, "semanticInputs": {}, "acceptedPins": {"pin": "x"}, "files": files}
        manifest_path = output / "integrity-manifest.json"
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        for name in files:
            target = output / name
            original = target.read_bytes()
            target.write_bytes(original + b"mutation")
            try:
                if regular_files(output) != files:
                    fail("synthetic single-file manifest mutation rejected")
            except SystemExit:
                pass
            else:
                raise AssertionError("single-file manifest mutation was accepted")
            target.write_bytes(original)
        missing = output / next(iter(files))
        saved = missing.read_bytes()
        missing.unlink()
        try:
            if regular_files(output) != files:
                fail("synthetic missing manifest file rejected")
        except SystemExit:
            pass
        else:
            raise AssertionError("missing manifest file was accepted")
        missing.write_bytes(saved)
        # Validator-facing malformed record tests, not log-existence tests.
        records = output / "records"
        records.mkdir()
        bad_failure = records / "negative-one.json"
        bad_failure.write_text(json.dumps({**FAILURE_FIELDS, "ruleApplicationCount": 1,
                                           "classification": "fixture"}), encoding="utf-8")
        try:
            validate_failure_records(output)
        except SystemExit:
            pass
        else:
            raise AssertionError("nonzero failure counter was accepted")
        parser = records / "parser-canonicality-selftest.json"
        parser.write_text(json.dumps({"schema": "R3-G-05-parser-canonicality-v1",
                                      "cases": []}), encoding="utf-8")
        try:
            validate_parser_record(output)
        except SystemExit:
            pass
        else:
            raise AssertionError("malformed parser record was accepted")
        terminal = base / "terminal-state"
        terminal.mkdir()
        (terminal / "raw-failure.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-failure-v1", "stage": "synthetic",
                        "exitStatus": 37}), encoding="utf-8")
        try:
            validate_raw_claims(terminal)
        except SystemExit as error:
            assert "terminal failure marker" in str(error)
        else:
            raise AssertionError("raw failure marker was accepted")
        (terminal / "raw-failure.json").unlink()
        try:
            validate_raw_claims(terminal)
        except SystemExit as error:
            assert "terminal success record" in str(error)
        else:
            raise AssertionError("absent terminal raw success was accepted")
        (terminal / "raw-success.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-success-v1", "terminal": False}),
            encoding="utf-8")
        try:
            validate_raw_claims(terminal)
        except SystemExit as error:
            assert "not terminal" in str(error)
        else:
            raise AssertionError("nonterminal raw success was accepted")
        (terminal / "raw-success.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-success-v1", "terminal": True}),
            encoding="utf-8")
        (terminal / "raw-stage.json").write_text(
            json.dumps({"schema": "R3-G-05-raw-stage-v1", "stage": "synthetic"}),
            encoding="utf-8")
        try:
            validate_raw_claims(terminal)
        except SystemExit as error:
            assert "unterminated stage record" in str(error)
        else:
            raise AssertionError("unterminated raw stage was accepted")
        (terminal / "raw-stage.json").unlink()
        (terminal / "raw-stage.json").symlink_to(terminal / "missing-stage-target")
        try:
            validate_raw_claims(terminal)
        except SystemExit as error:
            assert "unterminated stage record" in str(error)
        else:
            raise AssertionError("dangling raw stage symlink was accepted")

        # Hard kill immediately before terminal creation leaves no outer success;
        # immediately after creation but before journal removal leaves active state.
        boundary = base / "terminal-boundaries"
        (boundary / "records").mkdir(parents=True)
        (boundary / "integrity-manifest.json").write_text("{}\n", encoding="utf-8")
        (boundary / "raw-stage.json").write_text("{}\n", encoding="utf-8")
        try:
            validate_outer_terminal(boundary)
        except SystemExit as error:
            assert "outer success" in str(error)
        else:
            raise AssertionError("pre-terminal hard-kill state was accepted")
        for name in ("outer-success.json", "outer-session.json", "records/watchdog.json",
                     "records/watchdog.ready.json"):
            path = boundary / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("{}\n", encoding="utf-8")
        try:
            validate_outer_terminal(boundary)
        except SystemExit as error:
            assert "active outer journal" in str(error)
        else:
            raise AssertionError("post-terminal/pre-journal-removal hard-kill state was accepted")
        (boundary / "raw-stage.json").unlink()
        try:
            validate_outer_terminal(boundary)
        except SystemExit as error:
            assert "does not bind terminal validation" in str(error)
        else:
            raise AssertionError("mismatched outer-success manifest binding was accepted")
        mutation_sensitivity.cached_validator_self_test(base / "mutation-records")
    print("R3-G-05 cache/path adversarial self-test: pass")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("validate-output", "reserve-output", "create",
                                           "complete-outer", "refresh", "validate", "publish",
                                           "snapshot", "semantic-digest", "self-test"))
    parser.add_argument("root", nargs="?", type=Path)
    parser.add_argument("output", nargs="?", type=Path)
    parser.add_argument("--must-exist", action="store_true")
    args = parser.parse_args()
    if args.action == "self-test":
        self_test()
        return
    if args.action == "semantic-digest":
        if args.root is None:
            fail("root is required")
        encoded = json.dumps(semantic_hashes(args.root.resolve(strict=True)), sort_keys=True)
        print(hashlib.sha256(encoded.encode()).hexdigest())
        return
    if args.root is None or args.output is None:
        fail("root and output are required")
    root = args.root.resolve(strict=True)
    if args.action == "snapshot":
        write_snapshot(root, args.output)
        return
    inherited_output_fd = os.environ.get("R3_G_05_OUTPUT_FD")
    if inherited_output_fd and args.action in ("create", "complete-outer"):
        try:
            descriptor = verify_directory(Path(f"/proc/self/fd/{int(inherited_output_fd)}"))
            os.close(descriptor)
        except (OSError, ValueError, SecureIOError) as error:
            fail(f"inherited reserved output descriptor is invalid: {error}")
        output = Path(f"/proc/self/fd/{int(inherited_output_fd)}")
    else:
        output = output_path(root, args.output, must_exist=args.must_exist)
    if args.action == "validate-output":
        print(output)
    elif args.action == "reserve-output":
        task_build = root / "spine/rule-applied-allowlist/build"
        try:
            canonical, device, inode = reserve_output(task_build, output, initial_journal=True)
        except (FileExistsError, OSError, SecureIOError) as error:
            fail(f"raw output reservation failed: {error}")
        print(f"{canonical}\t{device}\t{inode}")
    elif args.action == "create":
        create_manifest(root, output)
    elif args.action == "complete-outer":
        complete_outer(root, output)
    elif args.action == "refresh":
        refresh_manifest(root, output)
    elif args.action == "validate":
        validate_manifest(root, output)
    elif args.action == "publish":
        publish(root, output)


if __name__ == "__main__":
    main()
