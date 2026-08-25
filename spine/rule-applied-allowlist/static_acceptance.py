#!/usr/bin/env python3
"""Zero-backend static authority witnesses for the repaired R3-G-05 spine."""

from __future__ import annotations

import ast
import json
import re
import subprocess
from pathlib import Path

import mutation_sensitivity


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def java_brace_depth(source: str, offset: int) -> int:
    depth = 0
    state = "code"
    index = 0
    while index < offset:
        char = source[index]
        following = source[index + 1] if index + 1 < offset else ""
        if state == "code":
            if char == '"':
                state = "string"
            elif char == "'":
                state = "character"
            elif char == "/" and following == "/":
                state = "line-comment"
                index += 1
            elif char == "/" and following == "*":
                state = "block-comment"
                index += 1
            elif char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
        elif state in ("string", "character"):
            if char == "\\":
                index += 1
            elif (state == "string" and char == '"') or (state == "character" and char == "'"):
                state = "code"
        elif state == "line-comment" and char == "\n":
            state = "code"
        elif state == "block-comment" and char == "*" and following == "/":
            state = "code"
            index += 1
        index += 1
    return depth


def main() -> None:
    task = Path(__file__).resolve().parent
    root = task.parent.parent
    k = (task / "src/rule-applied-allowlist.k").read_text(encoding="utf-8")
    java = (task / "src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java").read_text(
        encoding="utf-8")
    config_java = (
        task / "src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java"
    ).read_text(encoding="utf-8")
    selector = k[k.index("syntax OCandidates ::= #oSelectRule"):k.index("syntax OCandidates ::= #oCandidate")]

    for witness in (
        "oOperationAuthority", "OTermMetadataAuthority", "oResultIdentity",
        "#oParentProductionCount", "#oCellProductionCount", "#oMarkerProductionCount",
        "#oExpectedTrace", "#oProductionMeta", "#oOperationRootMeta",
        "#oCellDescriptorExact", "#oTermMetadataExact",
        "cPathCons(cApplicationArgument(0), cPathNil)",
    ):
        require(witness in k, f"K authority witness missing: {witness}")
    require("#oMetaComplete" not in k,
            "nonempty metadata remains an exact existing-graph authority")
    exact = k[k.index("syntax Bool ::= #oIsExactTrace"):k.index("syntax Bool ::= #oIsTraceCell")]
    require("#oSameTerm(ACTUAL, #oExpectedTrace(OPERATION))" in exact,
            "K does not structurally compare the complete expected graph")
    for node_witness in (
        "#oProductionMeta(CELL_PRODUCTION)",
        "#oProductionMeta(LEFT_MARKER)", "#oProductionMeta(RIGHT_MARKER)",
        "#oProductionMeta(APPEND)", "#oProductionMeta(SINGLETON)",
        "#oProductionMeta(EVENT)", "#oProductionMeta(ORIGIN)",
        "REWRITE_META", "VARIABLE_META", "TOKEN_META",
        "LINEAGE", "LABEL", "MODULE", "SOURCE", "LOCATION",
    ):
        require(node_witness in exact, f"exact metadata/payload witness missing: {node_witness}")
    require("cMeta(RESULT_SORT, PRODUCTION, METADATA)" in k,
            "production metadata does not bind the complete OSort descriptor")
    require("cSequence(" not in selector, "root cSequence positive selector remains")
    require("#oIsAnyExactTrace" not in k, "broad any-exact trace suppression remains")
    make_operation = k[k.index("syntax OOperation ::= #oMakeOperation"):k.index("syntax CPath ::= \"#oOriginPath\"")]
    require("cPathNil, NAME" not in make_operation, "operation still emits a root parent path")

    for witness in (
        "record OperationAuthority", "record GeneratedCellSpec", "record ResultIdentity",
        "record TermMetadataAuthority", "record MetaSpec",
        "executePairTransaction(input, before, result, 1)",
        "executePairTransaction(output, after, already, 2)",
        "returned == input", "countExactGeneratedUpdates",
        "Att.PRODUCTION()", "K-authored canonical result identity",
        "outputDefinitionConstructed", "R3_G_05_PARSER_RECORD",
        "mutationStructuralField", "mutationBeforeFingerprint",
        "mutationAfterFingerprint", "mutationFingerprint",
        "mutationKConflictBeforePairTransaction",
        "mutationHostIndependentRejection", "mutationChangedFieldPaths",
        "mutationFieldBeforeFingerprint", "mutationFieldAfterFingerprint",
        "mutationBeforeProjectionFingerprintMap",
        "mutationAfterProjectionFingerprintMap",
        "mutationStructuralOperation", "mutationReferenceFragmentFingerprint",
        "resolveOperationPath(item.located.rule.body(), item.parentPath)",
        "both parent layers do not equal independently declared production authority",
        "mutationProductionMutatorBound", "record ExistingGraphSnapshot",
        "construction.before.delta(construction.after)",
        "validatePreparedAlreadyPresent(List.of(malformedPrepared))",
        "rewrite.att().equals(KRewrite(before, after).att())",
    ):
        require(witness in java, f"Java authority/idempotence witness missing: {witness}")
    require("resolveMarkerEnvelope" not in java, "Java still infers marker constructors")
    require("item.name.equals(result.name)" not in java, "Java still selects the cell by name")
    require("ruleSecondSameReference = true" not in java, "same-reference fact is hard-coded")
    for base, field in mutation_sensitivity.FIELDS.items():
        require(f'Map.entry("{base}", "{field}")' in java,
                f"distinct Java mutation implementation missing: {base}")
        require(java.count(f'"{base}"') >= 2,
                f"defect argument is not consumed by a distinct mutation branch: {base}")
    mutation_sensitivity.static_binding_check()

    helper_declaration = "private static String productionStructure(Production production)"
    require(java.count(helper_declaration) == 1,
            "productionStructure must have exactly one canonical declaration")
    require('canonical.replace(",\\\"lineage-a\\\","' not in java,
            "missing-delimiter parser adversary remains a no-op replacement")
    require(java.count("requireParserMutationRejection(") == 8,
            "all seven parser mutations are not routed through the bound helper")
    parser_helper = java[java.index("private static void requireParserMutationRejection"):
                         java.index("static TraceOutcome parse", java.index(
                             "private static void requireParserMutationRejection"))]
    require("mutated.equals(canonical)" in parser_helper and "parse(mutated)" in parser_helper,
            "parser mutation helper does not bind changed bytes before rejection")
    helper_offset = java.index(helper_declaration)
    trace_adapter_offset = java.index("private static final class TraceAdapter")
    require(helper_offset < trace_adapter_offset,
            "productionStructure is not in outer driver scope before TraceAdapter")
    require(java_brace_depth(java, helper_offset) == 1
            and java_brace_depth(java, trace_adapter_offset) == 1,
            "productionStructure is not lexically in outer RuleAppliedTraceDriver scope")
    projection = java[java.index("private static final class Projection"):
                      java.index("private static final class TraceProjection")]
    production_descriptor = java[java.index("private record ProductionDescriptor"):
                                 java.index("private record SortDescriptor")]
    generated_descriptor_offset = java.index("private record GeneratedCellDescriptor")
    generated_descriptor = java[generated_descriptor_offset:
                                java.index("private static final class Trace", generated_descriptor_offset)]
    for description, consumer_source in (
        ("Projection.encodeMeta", projection),
        ("ProductionDescriptor.capture", production_descriptor),
        ("GeneratedCellDescriptor.capture", generated_descriptor),
    ):
        require("productionStructure(" in consumer_source,
                f"productionStructure consumer witness missing: {description}")

    replay = (task / "replay.sh").read_text(encoding="utf-8")
    for witness in (
        "raw-inner|finalize|publish", "EXPECTED_AUTHORIZATION_SHA256",
        "resource_watchdog.py", "cache_integrity.py", "repository-snapshot-before.json",
        "raw-provisional", "manifest-validated evidence publication", "session_supervisor.py",
        "launcherRepairActivation", "raw-failure.json", "CURRENT_RAW_STAGE",
        "securePublicationRepairActivation", "complete-outer",
        "raw inner session lacks an integrity manifest", "reserve-output",
        "WATCHDOG_IDENTITY_REPAIR_ACTIVATION", "publish_raw_success",
        "R3-G-05G-watchdog-readiness-and-process-identity-repair.md",
        "PRIVATE_GATE_REPAIR_ACTIVATION",
        "R3-G-05H-private-watchdog-gate-and-session-selection-repair.md",
        "STOPPED_PROCESS_REPAIR_ACTIVATION",
        "R3-G-05I-stopped-process-and-exit-boundary-repair.md",
        "DRIVER_FAILURE_RECOVERY_REPAIR_ACTIVATION",
        "R3-G-05J-driver-compilation-and-failure-recovery-repair.md",
        "PARSER_ADVERSARY_REPAIR_ACTIVATION",
        "R3-G-05K-parser-adversary-binding-repair.md",
        "NESTED_DESCRIPTOR_REPAIR_ACTIVATION",
        "dfadc62bb090580a32f2b0f2a95e74eaefdd7e4d",
        "NESTED_DESCRIPTOR_REPAIR_PACKET_SHA",
        "004b6f5cc4f6f9d05de75c38c4c9994d822f0a11ec35f01e85d20dfca64bd3af",
        "R3-G-05L-nested-child-descriptor-path-repair.md",
        "CLEAN_HEAD_JAVA_SCRATCH_REPAIR_ACTIVATION",
        "f5e07a4f47929ebbe76f9c5eb22f73ff39e65745",
        "CLEAN_HEAD_JAVA_SCRATCH_REPAIR_PACKET_SHA",
        "595f9948d5006e1e0d80f112df14caa4c25ce71dd5177a01e2d832d457f019c8",
        "R3-G-05M-clean-head-and-java-scratch-repair.md",
        "FINAL_2048_HEAP_CYCLE_ACTIVATION",
        "d995a8cc93462a43260bdadba256a90d61b0ffe2",
        "FINAL_2048_HEAP_CYCLE_PACKET_SHA",
        "e1446bc64e1da6bd6a325b51d2face3984aa87701ee784b0bd06d6d71feab3ec",
        "R3-G-05N-final-2048-heap-cycle.md",
        "EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION",
        "b67605c7228f8459173fceba527fb6d364e0e069",
        "EXACT_FINAL_TIMEOUT_BINDING_PACKET_SHA",
        "f904d79ca5589b883831eaf508b130bbb33d9888698a671bb6702f6735770b37",
        "R3-G-05O-exact-final-timeout-binding.md",
        "EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION",
        "7a072969a09260a1e3263de94b84dc3d54fac5d2",
        "EXACT_TIMEOUT_REPORT_VERIFICATION_PACKET_SHA",
        "f5a6bef098b90c0bb6e3a4100fa3a937ad708222364ef6e0e506dbbe0df05400",
        "R3-G-05P-exact-timeout-report-verification.md",
        "R3_G_05_IMPLEMENTATION_HEAD", "implementationHead=${IMPLEMENTATION_HEAD}",
        "checkout_integrity.py",
        'readonly CYCLE_5_OUTPUT="${TASK}/build/cycle-5-r3-g-05n"',
        '[[ "${CYCLE_COUNT}" == "5" ]]',
        '[[ "${CANONICAL_OUTPUT}" == "${CYCLE_5_OUTPUT}" ]]',
        "descriptor_owner.py", "descriptor_owner_selftest.py",
        '"separateLauncherAndDescriptorOwnerPidfds": True',
        '"outputDevice": int(os.environ["R3_G_05_OUTPUT_DEVICE"])',
        '"outputInode": int(os.environ["R3_G_05_OUTPUT_INODE"])',
    ):
        require(witness in replay, f"resource/cache witness missing: {witness}")
    require('readonly CYCLE_COUNT="${R3_G_05_CYCLE_COUNT:-5}"' in replay
            and 'CYCLE_COUNT:-4' not in replay and 'CYCLE_COUNT:-6' not in replay,
            "R3-G-05N cycle policy is not exactly total cycle 5")
    require('readonly HEAP_MIB="${R3_G_05_JAVA_MAX_HEAP_MIB:-2048}"' in replay
            and '[[ "${HEAP_MIB}" == "2048" ]]' in replay
            and '[[ "${CPU_COUNT}" == "2" ]]' in replay,
            "R3-G-05N non-test heap/CPU policy is not exact")
    require('readonly WALL_TIMEOUT_SECONDS="${R3_G_05_WALL_TIMEOUT_SECONDS:-7200}"' in replay
            and '[[ "${WALL_TIMEOUT_SECONDS}" == "7200" ]]' in replay
            and "timeoutSeconds=${WALL_TIMEOUT_SECONDS}" in replay,
            "R3-G-05O non-test timeout/authorization policy is not exact")
    production_gate = 'python3 "${CHECKOUT_INTEGRITY_TOOL}" verify "${REPO_ROOT}"'
    require(production_gate in replay
            and replay.index(production_gate) < replay.index('reserve-output "${REPO_ROOT}"'),
            "clean implementation checkout is not verified before output reservation")
    require('"${IMPLEMENTATION_HEAD}" "${EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION}"' in replay,
            "checkout gate is not bound to exact implementation head and P activation")
    require(replay.count("run_guarded") == 2,
            "a production command bypasses or duplicates the nested guard")
    nested_guard = replay[replay.index("run_nested_guarded() {"):
                          replay.index('\n}\n\nexec 9>', replay.index("run_nested_guarded() {"))]
    guard_order = (
        'before="$(verify_nested_output)"',
        'run_guarded "$@"',
        'after="$(verify_nested_output)"',
        'if (( post_status != 0 )) || [[ "${after}" != "${before}" ]]',
    )
    offsets = [nested_guard.index(witness) for witness in guard_order]
    post_failure_return = nested_guard.index("return 125", offsets[-1])
    status_return = nested_guard.index('return "${status}"', post_failure_return)
    require(offsets == sorted(offsets) and offsets[-1] < post_failure_return < status_return
            and nested_guard.count("verify_nested_output") == 2,
            "nested command does not have ordered pre/post identity checks")
    for call in (
        'run_nested_guarded kompile-version "${KOMPILE_BIN}" --version',
        "run_nested_guarded overlay-javac javac",
        "run_nested_guarded driver-javac javac",
        "run_nested_guarded parser-self-test java",
        "run_nested_guarded jdk-option-probe java",
        'run_nested_guarded configuration-compile "${KOMPILE_BIN}"',
        'run_nested_guarded allowlist-compile "${KOMPILE_BIN}"',
        'run_nested_guarded "baseline-${suffix}" "${KOMPILE_BIN}"',
        'run_nested_guarded "driver-${name}" "${TASK}/run-driver.sh"',
        'run_nested_guarded ordinary-compile "${KOMPILE_BIN}"',
        'run_nested_guarded "runtime-${name}" "${KRUN_BIN}"',
        'run_nested_guarded "runtime-baseline-${suffix}-${program}" "${KRUN_BIN}"',
    ):
        require(call in replay, f"compiler/backend boundary bypasses nested guard: {call}")
    nested_lines = [line.strip() for line in replay.splitlines() if "NESTED_OUTPUT" in line]
    expected_nested_lines = [
        'readonly NESTED_OUTPUT="$(verify_nested_output)"',
        '[[ "${before}" == "${NESTED_OUTPUT}" ]] || return 125',
        '--output-definition "${NESTED_OUTPUT}/configuration-k-kompiled" \\',
        '--output-definition "${NESTED_OUTPUT}/allowlist-k-kompiled" \\',
        '--output-definition "${NESTED_OUTPUT}/baseline-${suffix}" \\',
        'R3_G_05_BUILD_ROOT="${NESTED_OUTPUT}/host" R3_G_05_MODE="${mode}" \\',
        'R3_G_05_JAVA_SCRATCH="${NESTED_OUTPUT}/java-scratch" \\',
        'R3_G_05_TRACE_K_DEFINITION="${NESTED_OUTPUT}/allowlist-k-kompiled" \\',
        'R3_G_05_CONFIGURATION_K_DEFINITION="${NESTED_OUTPUT}/configuration-k-kompiled" \\',
        '--output-definition "${NESTED_OUTPUT}/${name}" \\',
        'run_nested_guarded ordinary-compile "${KOMPILE_BIN}" "${NESTED_OUTPUT}/generated/ordinary.k" --backend haskell --emit-json \\',
        '--output-definition "${NESTED_OUTPUT}/ordinary" \\',
        'run_runtime "${NESTED_OUTPUT}/instrumented-${suffix}" "${program}" "instrumented-${suffix}-${program}" "${count}"',
        'run_nested_guarded "runtime-baseline-${suffix}-${program}" "${KRUN_BIN}" "${TASK}/fixtures/${program}.exp" --definition "${NESTED_OUTPUT}/baseline-${suffix}" \\',
        'run_runtime "${NESTED_OUTPUT}/ordinary" "${program}" "ordinary-${program}" "${count}"',
    ]
    require(nested_lines == expected_nested_lines,
            "stable owner-qualified path escaped its exact nested compiler/backend uses")
    require('"${OUTPUT}/java-scratch" \\' in replay
            and 'R3_G_05_RECORD="${OUTPUT}/records/${name}.json" \\' in replay,
            "immediate scratch creation or immediate record publication mapping is missing")
    require('private static final String JAVA_SCRATCH_ENV = "R3_G_05_JAVA_SCRATCH"' in java
            and "Path.of(required(JAVA_SCRATCH_ENV))" in java,
            "driver does not require the separate stable Java scratch environment")
    trace_run_k = java[java.index("private static String runK("):
                       java.index("private static String required(")]
    configuration_run_k = config_java[config_java.index("private static String runK("):
                                      config_java.index("private static String replaceSource(")]
    require('Files.createTempFile(javaScratch, "trace-", ".kink")' in trace_run_k
            and 'Files.createTempFile(javaScratch, "configuration-", ".kink")'
            in configuration_run_k,
            "both Java helpers do not create temporary programs through stable scratch")
    require("recordPath.getParent()" not in trace_run_k + configuration_run_k
            and "Files.deleteIfExists(file)" in trace_run_k
            and "Files.deleteIfExists(file)" in configuration_run_k,
            "a Java helper derives scratch from records or does not delete through scratch")
    negative_block = replay[replay.index('for mode in "${negative_modes[@]}"'):
                            replay.index('python3 "${TASK}/mutation_sensitivity.py"')]
    require(negative_block.index("code != 125") < negative_block.index("jq -e"),
            "descriptor post-check failure can consume a provisional negative result")

    outer = replay[replay.index('if [[ "${ACTION}" == "raw" ]]; then'):
                   replay.index('\nfi\n\n[[ "${R3_G_05_RAW_INNER',
                                replay.index('if [[ "${ACTION}" == "raw" ]]; then'))]
    for witness in (
        "readonly DESCRIPTOR_OWNER_FD=198", 'exec 198<"${CANONICAL_OUTPUT}"',
        'readonly OUTER_SECURE_OUTPUT="/proc/self/fd/${DESCRIPTOR_OWNER_FD}"',
        'DESCRIPTOR_OWNER_PID="$$"', 'bash "${TASK}/replay.sh" raw-inner',
        "198<&- &", 'exec 198<&-', 'owner_post_status=0',
        '"raw-inner-session" "${inner_status}" 1 "${OUTER_SECURE_OUTPUT}"',
        'R3_G_05_OUTPUT_FD="${DESCRIPTOR_OWNER_FD}"',
        'complete-outer "${REPO_ROOT}" "${OUTER_SECURE_OUTPUT}"',
    ):
        require(witness in outer, f"outer fixed descriptor lifetime witness missing: {witness}")
    owner_post = outer.index("owner_post_status=0")
    complete_outer = outer.index('complete-outer "${REPO_ROOT}"')
    close_offsets = [match.start() for match in re.finditer(r"exec 198<&-", outer)]
    require(outer.index('wait "${SUPERVISOR_PID}"') < owner_post
            and close_offsets and all(offset > owner_post for offset in close_offsets)
            and outer.rindex('exec 198<&-') > complete_outer
            and "${CANONICAL_OUTPUT}" not in outer[owner_post:],
            "outer descriptor is not retained through synchronous supervisor teardown proof")

    descriptor_source = (task / "descriptor_owner.py").read_text(encoding="utf-8")
    for witness in (
        "def owner_descriptor_path", 'Path(f"/proc/{owner_pid}/fd/{owner_fd}")',
        "def immediate_descriptor_path", 'Path(f"/proc/self/fd/{immediate_fd}")',
        "def verify_owner_descriptor", "owner_before = os.stat(owner_path",
        "owner_after = os.stat(owner_path", "opened = os.fstat(immediate_fd)",
        "after.start_time != before.start_time", "len(identities) != 1",
    ):
        require(witness in descriptor_source,
                f"descriptor constructor/identity witness missing: {witness}")
    require("timeout --foreground" not in replay,
            "foreground timeout remains in the whole-session launcher")
    supervisor = (task / "session_supervisor.py").read_text(encoding="utf-8")
    for witness in ("terminate_whole_session", "SessionGeneration",
                    "watchdogDisarmedAfterEmpty", "start_new_session=True",
                    "wall-timeout", "watchdog-failure", "reap_session_children",
                    "successful_empty", "reapedSessionChildPids", "GATE_PROGRAM",
                    "wait_for_readiness", "publish_outer_session",
                    "publish_watchdog_done", "exitTimeDescendantPids",
                    "approve_watchdog", "privateWatchdogReadinessValidated",
                    "watchdogOnlyGateReleaseAcknowledged",
                    "nonInferentialExitClassification", "member_snapshot",
                    "descriptor_is_open(args.descriptor_owner_fd)",
                    "verify_owner_descriptor", "output_fd == args.descriptor_owner_fd",
                    'Path(f"/proc/{child.pid}/fd/{args.descriptor_owner_fd}").exists()',
                    'pass_fds=(output_fd, gate_read, target_ack_write)',
                    "descriptorOwnerFdExcludedFromTarget"):
        require(witness in supervisor, f"whole-session supervisor witness missing: {witness}")
    require("def release_gate" not in supervisor,
            "supervisor retains a direct gate-release code path")
    secure_io = (task / "secure_io.py").read_text(encoding="utf-8")
    for witness in ("os.O_NOFOLLOW", "os.O_EXCL", "secrets.token_hex",
                    "src_dir_fd=directory_fd", "reserve_output", "os.fsync",
                    "os.link", "require_absent", "_existing_valid_raw_failure"):
        require(witness in secure_io, f"secure publication witness missing: {witness}")
    for publisher in (
        "publish_initial_journal", "publish_raw_success", "publish_raw_failure",
        "publish_integrity_manifest", "publish_outer_session", "publish_outer_success",
        "publish_watchdog_ready", "publish_watchdog_done", "replace_progress_json",
    ):
        require(f"def {publisher}" in secure_io,
                f"dedicated publication operation missing: {publisher}")
    watchdog_source = (task / "resource_watchdog.py").read_text(encoding="utf-8")
    for witness in ("os.pidfd_open", "signal.pidfd_send_signal", "start_time",
                    "SessionGeneration", "owner_start_time", "owner_generation_alive",
                    "publish_watchdog_ready", "private_send", "private_receive",
                    "select_session_generation", "_leader_bracket",
                    "watchdogOnlyGateRelease", "bound_process_generation_current",
                    "descriptor_owner_handle = bind_process",
                    "owner_handle = bind_process", "close_bound(owner_handle)",
                    "close_bound(descriptor_owner_handle)",
                    "descriptor-owner-failure", "descriptorOwnerPidfdGenerationBound"):
        require(witness in watchdog_source,
                f"generation-safe watchdog witness missing: {witness}")
    terminal_state = (task / "terminal_state.py").read_text(encoding="utf-8")
    cache_source = (task / "cache_integrity.py").read_text(encoding="utf-8")
    require('args.action in ("create", "complete-outer")' in cache_source,
            "outer completion is not routed through its inherited immediate descriptor")
    for witness in (
        'FINAL_2048_HEAP_CYCLE_ACTIVATION = "d995a8cc93462a43260bdadba256a90d61b0ffe2"',
        '"tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md"',
        '"final2048HeapCycleActivation": FINAL_2048_HEAP_CYCLE_ACTIVATION',
        'FINAL_2048_HEAP_CYCLE_ACTIVATION, implementation_head',
        'raw.get("javaMaxHeapMiB") != 2048',
        'raw.get("substantiveFullOracleCycleCount") != 5',
    ):
        require(witness in cache_source,
                f"N cache-validation binding witness missing: {witness}")
    for witness in (
        'EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION = "b67605c7228f8459173fceba527fb6d364e0e069"',
        '"tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md"',
        '"exactFinalTimeoutBindingActivation": EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION',
        'EXACT_FINAL_WALL_TIMEOUT_SECONDS = 7200',
        'require_exact_wall_timeout(raw, "raw success record")',
        '"wallTimeoutSeconds": EXACT_FINAL_WALL_TIMEOUT_SECONDS',
        'require_exact_wall_timeout(manifest, "raw integrity manifest")',
        'session.get("wallTimeoutSeconds") != EXACT_FINAL_WALL_TIMEOUT_SECONDS',
    ):
        require(witness in cache_source,
                f"O cache/manifest timeout binding witness missing: {witness}")
    for witness in (
        'EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION = "7a072969a09260a1e3263de94b84dc3d54fac5d2"',
        '"tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md"',
        '"exactTimeoutReportVerificationActivation": EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION',
        'EXACT_FINAL_TIMEOUT_REPORT_WITNESS = "Cycle 5 used the exact 7200-second wall timeout."',
        'def require_exact_timeout_report(report: object)',
    ):
        require(witness in cache_source,
                f"P cache/report binding witness missing: {witness}")
    for source, calls in (
        (replay, ("publish_raw_success",)),
        (terminal_state, ("publish_raw_failure", "replace_progress_json")),
        (cache_source, ("publish_integrity_manifest", "publish_outer_success")),
        (supervisor, ("publish_outer_session", "publish_watchdog_done")),
        (watchdog_source, ("publish_watchdog_ready", "replace_progress_json")),
    ):
        for call in calls:
            require(call in source, f"production publication call site missing: {call}")
    launcher_test = (task / "launcher_selftest.py").read_text(encoding="utf-8")
    for witness in ("expected_status", "elapsed < 0.20", "synthetic-launcher-stdout",
                    "synthetic-launcher-stderr", "observedProcessGroupCount",
                    "watchdog_crash", "session_members", "run_launcher_hard_kill_case",
                    "launcher-owner-failure", "run_adopted_zombie_case",
                    "run_launcher_failure_case", "require_watchdog_shape",
                    "run_immediate_success_stress", "run_preexecution_refusal_cases",
                    "run_historically_reaped_case", "run_watchdog_pressure_case",
                    "run_stopped_tree_case", "run_stopped_hard_kill_case",
                    "DESCRIPTOR_OWNER_FDS", "descriptorOwnerFdExcludedFromTarget"):
        require(witness in launcher_test, f"waiting-launcher self-test witness missing: {witness}")
    for witness in ("public-readiness-precreation", "private-readiness-eof",
                    "watchdog-stop-after-ready", "watchdog-kill-after-approval",
                    "target-ack-failure", "private-approval-corruption",
                    "run_outer_session_rollback_case"):
        require(witness in launcher_test, f"private-gate adversary missing: {witness}")

    descriptor_test = (task / "descriptor_owner_selftest.py").read_text(encoding="utf-8")
    descriptor_tree = ast.parse(descriptor_test)
    adversaries = None
    for node in descriptor_tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and node.targets[0].id == "ACCEPTANCE_ADVERSARIES"):
            adversaries = ast.literal_eval(node.value)
    require(isinstance(adversaries, tuple) and len(adversaries) == 12
            and len(set(adversaries)) == 12,
            "nested descriptor adversary ledger is not exact")
    for witness in (
        "outer_pidfd = os.pidfd_open", "supervisor_pidfd = os.pidfd_open",
        'os.chdir(f"/proc/self/fd/{args.owner_fd}")',
        "os.chdir(owner_descriptor_path(args.owner_pid, args.owner_fd))",
        "canonical.rename(held)", "grandchildOwnerFdAbsent", "childOwnerFdAbsent",
        "supervisorOwnerFdAbsent", "ownerQualifiedPathRejectedAfterExit",
        "injected descriptor owner replacement was trusted",
        "same-number owner FD rebinding was accepted",
        "failed post-check consumed a provisional compiler result",
        "signal.pidfd_send_signal(target_pidfd, signal.SIGKILL)",
        "replacement.poll() is not None", "checked_synchronous_boundary",
        "stableScratchAndImmediateRecordSameTree", "recordPathImmediateOnly",
        'record_path).startswith("/proc/self/fd/")',
        'scratch_stable).startswith(f"/proc/{args.owner_pid}/fd/")',
    ):
        require(witness in descriptor_test,
                f"nested descriptor process/path adversary missing: {witness}")
    require("publisher_cases" in cache_source and "attacker-first-writer" in cache_source,
            "secure first-writer publication adversary is no longer bound")
    checkout_source = (task / "checkout_integrity.py").read_text(encoding="utf-8")
    for witness in (
        '"rev-parse", "HEAD"', '"cat-file", "-e"',
        '"merge-base", "--is-ancestor"', '"diff", "--cached", "--quiet"',
        '"diff", "--quiet"', '"ls-files", "-z", "--others", "--exclude-standard"',
        "does not equal checkout HEAD", "tracked worktree changes", "staged changes",
        "untracked non-ignored path", "ignored raw/build output made the checkout dirty",
        "cycle-5-r3-g-05n",
    ):
        require(witness in checkout_source,
                f"clean implementation checkout witness missing: {witness}")
    adversarial_source = (task / "adversarial_tests.py").read_text(encoding="utf-8")
    for witness in (
        'for cycle in ("4", "6")', '"R3_G_05_JAVA_MAX_HEAP_MIB": "1536"',
        '"R3_G_05_JAVA_ACTIVE_PROCESSORS": "1"', 'build / "cycle-4-r3-g-05l"',
        '"R3_G_05_WALL_TIMEOUT_SECONDS": "3600"',
        'build / "non-exact-final-cycle"', "fresh exact cycle-5 path",
        'for label in ("raw integrity manifest", "final evidence resource policy")',
        'for record in ({}, {"wallTimeoutSeconds": 3600})',
        'EXACT_FINAL_TIMEOUT_REPORT_WITNESS * 2',
        'require_exact_timeout_report(altered_report)',
    ):
        require(witness in adversarial_source,
                f"final cycle zero-backend refusal witness missing: {witness}")
    finalizer_source = (task / "finalize_evidence.py").read_text(encoding="utf-8")
    for witness in (
        'FINAL_2048_HEAP_CYCLE_ACTIVATION = "d995a8cc93462a43260bdadba256a90d61b0ffe2"',
        'get("final2048HeapCycleActivation")',
        '"tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md"',
        '"final2048HeapCycleActivationRevision": FINAL_2048_HEAP_CYCLE_ACTIVATION',
        '"final2048HeapCyclePacketSha256": sha(',
        'raw.get("javaMaxHeapMiB") != 2048',
        'raw.get("javaActiveProcessorCount") != 2',
        '"cycle": 4, "verdict": "failed", "stage": "positive-pair-transactions"',
        '"step": "nested-krun-java-heap-oom-1536", "exitStatus": 113',
        '"cycle": 5, "verdict": "pass", "finalEvidence": True',
    ):
        require(witness in finalizer_source,
                f"N final-evidence binding witness missing: {witness}")
    for witness in (
        'EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION',
        'get("exactFinalTimeoutBindingActivation")',
        '"tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md"',
        '"exactFinalTimeoutBindingActivationRevision":',
        '"exactFinalTimeoutBindingPacketSha256": sha(',
        'require_exact_wall_timeout(raw, "raw success record")',
        '"wallTimeoutSeconds": EXACT_FINAL_WALL_TIMEOUT_SECONDS',
    ):
        require(witness in finalizer_source,
                f"O final-evidence timeout binding witness missing: {witness}")
    for witness in (
        'EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION',
        'get("exactTimeoutReportVerificationActivation")',
        '"tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md"',
        '"exactTimeoutReportVerificationActivationRevision":',
        '"exactTimeoutReportVerificationPacketSha256": sha(',
        '{EXACT_FINAL_TIMEOUT_REPORT_WITNESS}',
    ):
        require(witness in finalizer_source,
                f"P final-evidence report binding witness missing: {witness}")
    verifier_source = (task / "verify.py").read_text(encoding="utf-8")
    for witness in (
        'FINAL_2048_HEAP_CYCLE_ACTIVATION = "d995a8cc93462a43260bdadba256a90d61b0ffe2"',
        'result["final2048HeapCycleActivationRevision"]',
        'FINAL_2048_HEAP_CYCLE_ACTIVATION, implementation_head',
        '"tasks/wave-3/R3-G-05N-final-2048-heap-cycle.md"',
        'result["pins"]["contracts"]["final2048HeapCyclePacketSha256"]',
        'result["resourcePolicy"]["javaMaxHeapMiB"] == 2048',
        'result["resourcePolicy"]["javaActiveProcessorCount"] == 2',
        'result["substantiveFullOracleCycleCount"] == 5',
    ):
        require(witness in verifier_source,
                f"N final-verification binding witness missing: {witness}")
    for witness in (
        'EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION',
        'result["exactFinalTimeoutBindingActivationRevision"]',
        'EXACT_FINAL_TIMEOUT_BINDING_ACTIVATION, implementation_head',
        '"tasks/wave-3/R3-G-05O-exact-final-timeout-binding.md"',
        'result["pins"]["contracts"]["exactFinalTimeoutBindingPacketSha256"]',
        'require_exact_wall_timeout(result["resourcePolicy"], "final evidence resource policy")',
    ):
        require(witness in verifier_source,
                f"O final-verification timeout binding witness missing: {witness}")
    for witness in (
        'EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION',
        'result["exactTimeoutReportVerificationActivationRevision"]',
        'EXACT_TIMEOUT_REPORT_VERIFICATION_ACTIVATION, implementation_head',
        '"tasks/wave-3/R3-G-05P-exact-timeout-report-verification.md"',
        'result["pins"]["contracts"]["exactTimeoutReportVerificationPacketSha256"]',
        'require_exact_timeout_report(report)',
    ):
        require(witness in verifier_source,
                f"P final-verification report binding witness missing: {witness}")

    for path in task.glob("*.py"):
        ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    subprocess.run(
        ["bash", "-n", str(task / "replay.sh"), str(task / "run-driver.sh"),
         str(task / "verify.sh")], check=True)
    package = json.loads((root / "package.json").read_text(encoding="utf-8"))
    require(package["scripts"]["r3:g:rule-applied-allowlist"]
            == "bash spine/rule-applied-allowlist/verify.sh", "package entry changed")
    forbidden = re.compile(
        r'"[^"\n]*(?:bump-state|drop-state|<trace>|\\.List)[^"\n]*"')
    require(not forbidden.search(java), "Java fixture selection literal detected")
    print("R3-G-05 static authority/resource/cache acceptance: pass")


if __name__ == "__main__":
    main()
