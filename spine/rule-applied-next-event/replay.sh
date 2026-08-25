#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="68c95e7f336eb07be4c5bf05246e99c1c64bef18"
readonly ACTIVATION_TREE="0e23b0308c8eec93c3bdd1c03e77b8b908cae7b5"
readonly PACKET_REPAIR="84ec8a95221f877c4ca810a96b8126477577d2fa"
readonly PACKET_REPAIR_TREE="1cdf31c2063b1522698a2b5ce7471971ba7cb59e"
readonly ACCEPTED_INTEGRATION="6c88e2c97b1e851c74b03dd5afb11b48eb170ac3"
readonly ACCEPTED_TREE="e6c478dea4204c08bbd89d16e90c3b911e26e1bc"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly PACKET_SHA="f970d1ec48dc9ebc80543338806656ec72d244166896352cb5e1e89bd808daff"
readonly CHECKPOINT_SHA="1c42ec0b012764ff50d1a4a15e2f4a13d535d67335b1a30cfe43039cb6b3fd4c"
readonly GOAL_SHA="ce6a40f0667d09f9c79a17f0f51857e561f95bbcc28592f0b177c45253ed2f43"
readonly PATH_PLAN_SHA="57ec8fd012fb8a115fb1eae3e153e7c0e92213b5b77fb669e3d8389b729ba253"
readonly ACCEPTED_PACKAGE_SHA="fc2157a57283595390dea7b1436eb8f37b9ae494b706916d83c374362c27a8da"
readonly ACCEPTED_REPLAY_SHA="5bcd3cba489bbe2b192a0c861d8976f8b5cb41d7d2b27985750209c69dc55908"
readonly ACCEPTED_VERIFY_SHA="c7cdbf2c3549e58843b01615e4eb966de39d1f01f309db229b1fe268d208895c"
readonly ACCEPTED_SPINE_TREE="1b6b4de985eebba250af02b17b2d6bb251687b36"
readonly ACCEPTED_EVIDENCE_TREE="f250584e8b3aff37145555bdd3c41424510fd457"
readonly ACCEPTED_RESULTS_SHA="f80886548d4373cdff8ee73d182c89aab2856a6ae7d1059e08978f75d821595d"
readonly ACCEPTED_REPORT_SHA="5bba00094746b226f33cd92d7164c88e12899b8319a629c60d319842df19d9ef"
readonly ONE_BUMP_SHA="46210dddc66714c3d8d226711510cf8421774214016c508c72a833a05370f6b5"
readonly TWO_BUMP_SHA="9e2439bacf107a74303680e75d5bb1c91657aa2ea183fd4bbf60bb1416a6db1c"
readonly THREE_BUMP_SHA="982ae8b05f1b6141c09b901fd78ff5a3b55d09db8cacba43358fbd475d5d977d"
readonly EXACT_PATTERN_SHA="ed110403e09578d282d335a4c1e9fb50edc92d1a433b8ba44f07a8676035e807"
readonly WRONG_PATTERN_SHA="e8f90357e3b8ff16a2f5c53c75772c2cbb1dcbad00288032fb67b9a4002ab57d"
readonly PROJECTOR_SHA="1fa2ca1906c2d815e9e28c563aa9a1881677a043720c3e779d4c3e344ab3c0f9"
readonly TRUSTED_SHA="dac3a859494443cd49208599e236450eac26b3fba5165b8933f0c1d2f2e871c7"
readonly SELFTEST_SHA="b87a48c0c3cfa71f67dd14d0e666421859b5152d05ab8b39d4d65c3ce182636a"
readonly RUNTIME_SHA="4d800215fba75a300105b14ccb4ca07f818d7933331dc059cf54eedaf8fb42f5"
readonly RUNTIME_SELFTEST_SHA="3006dc941643b67cbcfe277e29d6fbcb4c8ed20772e180b0e3a906b1c0961035"
readonly RUNTIME_FIXTURE_SHA="6c143294cf35807c7d4fdc3eb2bb5a3f900ae006de779ab3b1eb324bea8234da"
readonly VERIFY_SHA="73a85d5e19210ca184d1782636ba0239bb23dd402c6e49674fbe5aaa7258477f"
readonly PACKAGE_SHA="534a5bd9ff18e8012f5d59c483587837d1f9e1b17dad12664e27c55daa587478"
readonly CYCLE_COUNT="${R3_G_04_CYCLE_COUNT:-3}"
readonly JAVA_HEAP_MB="${KINK_JAVA_MAX_HEAP_MB:-2048}"
readonly JAVA_CPUS="${KINK_JAVA_CPUS:-2}"

[[ "${JAVA_HEAP_MB}" =~ ^[0-9]+$ && "${JAVA_HEAP_MB}" -ge 512 && "${JAVA_HEAP_MB}" -le 4096 ]]
[[ "${JAVA_CPUS}" =~ ^[0-9]+$ && "${JAVA_CPUS}" -ge 1 && "${JAVA_CPUS}" -le 4 ]]
export _JAVA_OPTIONS="${_JAVA_OPTIONS:+${_JAVA_OPTIONS} }-Xmx${JAVA_HEAP_MB}m -XX:ActiveProcessorCount=${JAVA_CPUS}"
renice 10 -p $$ >/dev/null 2>&1 || true

readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/rule-applied-next-event"
readonly EVIDENCE="${REPO_ROOT}/evidence/r3-g-04-k-native-rule-applied-next-event"
readonly OUTPUT_INPUT="${1:-${TASK}/build/acceptance}"
readonly OUTPUT="$(readlink -m "${OUTPUT_INPUT}")"
readonly REUSE_FULL_OUTPUT="${R3_G_04_REUSE_FULL_OUTPUT:-}"
readonly ACCEPTED_SOURCE="${OUTPUT}/accepted-source"
readonly INHERITED="${OUTPUT}/inherited-r3-g-03"
readonly COMPOSITION="${INHERITED}/composition"
readonly ONE_BUMP="${REPO_ROOT}/p3/fixtures/program.exp"
readonly TWO_BUMP="${TASK}/fixtures/two-bump.exp"
readonly THREE_BUMP="${TASK}/fixtures/three-bump.exp"
readonly EXACT_PATTERN_FILE="${TASK}/patterns/exact-pair.k"
readonly WRONG_PATTERN_FILE="${TASK}/patterns/wrong-second-label.k"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly KRUN_BIN="$(readlink -f "$(command -v krun)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly FRONTEND_JAR="${K_ROOT}/lib/kframework/java/k-frontend-1.0-SNAPSHOT.jar"

check_sha() { [[ "$(sha256sum "$2" | awk '{print $1}')" == "$1" ]]; }
for tool in bun cmp git jq kompile krun python3 rg sha256sum; do
  command -v "${tool}" >/dev/null
done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
[[ "$(git rev-parse "${ACTIVATION}^{tree}")" == "${ACTIVATION_TREE}" ]]
[[ "$(git rev-parse "${PACKET_REPAIR}^{tree}")" == "${PACKET_REPAIR_TREE}" ]]
git diff --quiet "${PACKET_REPAIR}" HEAD -- \
  tasks/wave-3/R3-G-04-k-native-rule-applied-next-event.md
[[ "$(git rev-parse "${ACCEPTED_INTEGRATION}^{tree}")" == "${ACCEPTED_TREE}" ]]
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
[[ "${KRUN_BIN}" == "${K_ROOT}/bin/krun" && "${KRUN_BIN}" == *"${K_COMMIT}"* ]]
"${KOMPILE_BIN}" --version | grep -F "${K_RELEASE}" >/dev/null
check_sha "${FRONTEND_SHA}" "${FRONTEND_JAR}"
check_sha "${PACKET_SHA}" "${REPO_ROOT}/tasks/wave-3/R3-G-04-k-native-rule-applied-next-event.md"
check_sha "${CHECKPOINT_SHA}" "${REPO_ROOT}/draft/k-in-k-r3-g-03-acceptance-checkpoint-2026-08-20.md"
check_sha "${GOAL_SHA}" "${REPO_ROOT}/draft/goal/execution-pattern-matching.md"
check_sha "${PATH_PLAN_SHA}" "${REPO_ROOT}/draft/k-in-k-r4-d1-path-plan-2026-08-20.md"
check_sha "${ONE_BUMP_SHA}" "${ONE_BUMP}"
check_sha "${TWO_BUMP_SHA}" "${TWO_BUMP}"
check_sha "${THREE_BUMP_SHA}" "${THREE_BUMP}"
check_sha "${EXACT_PATTERN_SHA}" "${EXACT_PATTERN_FILE}"
check_sha "${WRONG_PATTERN_SHA}" "${WRONG_PATTERN_FILE}"
check_sha "${PROJECTOR_SHA}" "${TASK}/project_match.py"
check_sha "${TRUSTED_SHA}" "${TASK}/trusted_oracle.py"
check_sha "${SELFTEST_SHA}" "${TASK}/selftest_projector.py"
check_sha "${RUNTIME_SHA}" "${TASK}/project_runtime.py"
check_sha "${RUNTIME_SELFTEST_SHA}" "${TASK}/selftest_runtime.py"
check_sha "${RUNTIME_FIXTURE_SHA}" "${TASK}/fixtures/runtime-two-event.pretty"
check_sha "${VERIFY_SHA}" "${TASK}/verify.sh"
check_sha "${PACKAGE_SHA}" "${REPO_ROOT}/package.json"
[[ "${CYCLE_COUNT}" == "3" ]]
[[ "$(git rev-parse "${ACCEPTED_INTEGRATION}:spine/rule-applied-head-match")" == "${ACCEPTED_SPINE_TREE}" ]]
[[ "$(git rev-parse "${ACCEPTED_INTEGRATION}:evidence/r3-g-03-k-native-rule-applied-head-match")" == "${ACCEPTED_EVIDENCE_TREE}" ]]
[[ "$(git show "${ACCEPTED_INTEGRATION}:spine/rule-applied-head-match/replay.sh" | sha256sum | awk '{print $1}')" == "${ACCEPTED_REPLAY_SHA}" ]]
[[ "$(git show "${ACCEPTED_INTEGRATION}:spine/rule-applied-head-match/verify.sh" | sha256sum | awk '{print $1}')" == "${ACCEPTED_VERIFY_SHA}" ]]
[[ "$(git show "${ACCEPTED_INTEGRATION}:package.json" | sha256sum | awk '{print $1}')" == "${ACCEPTED_PACKAGE_SHA}" ]]

python3 - "${REPO_ROOT}" "${ACTIVATION}" <<'PY'
import json
import subprocess
import sys
from pathlib import Path
root, activation = sys.argv[1:]
baseline = json.loads(subprocess.check_output(
    ["git", "show", f"{activation}:package.json"], cwd=root, text=True))
current = json.loads((Path(root) / "package.json").read_text(encoding="utf-8"))
expected = dict(baseline)
expected["scripts"] = dict(baseline["scripts"])
expected["scripts"]["r3:g:rule-applied-next-event"] = \
    "bash spine/rule-applied-next-event/verify.sh"
if current != expected:
    raise SystemExit("package.json changed beyond the one owned script entry")
PY

while IFS= read -r path; do
  [[ -z "${path}" ]] && continue
  case "${path}" in
    package.json|tasks/wave-3/R3-G-04-k-native-rule-applied-next-event.md|draft/k-in-k-r4-d1-path-plan-2026-08-20.md|spine/rule-applied-next-event/*|evidence/r3-g-04-k-native-rule-applied-next-event/*) ;;
    *) printf 'path outside packet ownership: %s\n' "${path}" >&2; exit 1 ;;
  esac
done < <({ git diff --name-only "${ACTIVATION}" --; git ls-files --others --exclude-standard; } | LC_ALL=C sort -u)

[[ "${OUTPUT}" == "${TASK}/build/"* && "${OUTPUT}" != "${TASK}/build/" ]]
export LC_ALL=C LANG=C TZ=UTC
if [[ -n "${REUSE_FULL_OUTPUT}" ]]; then
  [[ "$(readlink -m "${REUSE_FULL_OUTPUT}")" == "${OUTPUT}" ]]
  [[ -d "${OUTPUT}" && ! -e "${ACCEPTED_SOURCE}" ]]
  [[ -f "${OUTPUT}/queries/composition-a-positive.json" ]]
  [[ -f "${OUTPUT}/queries/composition-b-positive.json" ]]
  [[ -f "${OUTPUT}/runtime/composition-a-positive.out" ]]
  [[ -f "${OUTPUT}/runtime/composition-b-positive.out" ]]
else
  [[ ! -e "${OUTPUT}" ]]
  mkdir -p "${OUTPUT}"/{logs,queries,projected,runtime}
  cleanup() {
    if [[ -e "${ACCEPTED_SOURCE}/.git" ]]; then
      git worktree remove --force "${ACCEPTED_SOURCE}" >/dev/null 2>&1 || true
    fi
  }
  trap cleanup EXIT
  git worktree add --detach "${ACCEPTED_SOURCE}" "${ACCEPTED_INTEGRATION}" \
    >"${OUTPUT}/logs/accepted-worktree.stdout" 2>"${OUTPUT}/logs/accepted-worktree.stderr"
  (
    cd "${ACCEPTED_SOURCE}"
    bash spine/rule-applied-head-match/replay.sh "${INHERITED}"
  ) >"${OUTPUT}/logs/inherited-replay.stdout" 2>"${OUTPUT}/logs/inherited-replay.stderr"
  git worktree remove "${ACCEPTED_SOURCE}"
  trap - EXIT
  [[ ! -e "${ACCEPTED_SOURCE}" ]]
fi
check_sha "${ACCEPTED_RESULTS_SHA}" "${INHERITED}/results.json"
check_sha "${ACCEPTED_REPORT_SHA}" "${INHERITED}/report.md"

readonly EXACT_PATTERN="$(<"${EXACT_PATTERN_FILE}")"
readonly WRONG_PATTERN="$(<"${WRONG_PATTERN_FILE}")"
for repeat in a b; do
  definition="${COMPOSITION}/composition-${repeat}"
  driver="${COMPOSITION}/records/composition-${repeat}.json"
  [[ -f "${definition}/definition.kore" && -f "${driver}" ]]
  jq -e '.status=="accepted" and .ruleTargetLabel=="bump-state"
    and .ruleTargetLabel!="known-unequal-label"' "${driver}" >/dev/null

  if [[ -z "${REUSE_FULL_OUTPUT}" ]]; then
    "${KRUN_BIN}" "${TWO_BUMP}" --definition "${definition}" \
      --pattern "${EXACT_PATTERN}" --output json \
      >"${OUTPUT}/queries/composition-${repeat}-positive.json" \
      2>"${OUTPUT}/queries/composition-${repeat}-positive.stderr"
    "${KRUN_BIN}" "${ONE_BUMP}" --definition "${definition}" \
      --pattern "${EXACT_PATTERN}" --output json \
      >"${OUTPUT}/queries/composition-${repeat}-too-short.json" \
      2>"${OUTPUT}/queries/composition-${repeat}-too-short.stderr"
    "${KRUN_BIN}" "${THREE_BUMP}" --definition "${definition}" \
      --pattern "${EXACT_PATTERN}" --output json \
      >"${OUTPUT}/queries/composition-${repeat}-non-exhausted.json" \
      2>"${OUTPUT}/queries/composition-${repeat}-non-exhausted.stderr"
    "${KRUN_BIN}" "${TWO_BUMP}" --definition "${definition}" \
      --pattern "${WRONG_PATTERN}" --output json \
      >"${OUTPUT}/queries/composition-${repeat}-wrong-second-label.json" \
      2>"${OUTPUT}/queries/composition-${repeat}-wrong-second-label.stderr"
    printf '0\n' >"${OUTPUT}/queries/composition-${repeat}-exit-codes.txt"

    "${KRUN_BIN}" "${TWO_BUMP}" --definition "${definition}" \
      >"${OUTPUT}/runtime/composition-${repeat}-positive.out" \
      2>"${OUTPUT}/runtime/composition-${repeat}-positive.stderr"
    "${KRUN_BIN}" "${TWO_BUMP}" --definition "${COMPOSITION}/baseline" \
      >"${OUTPUT}/runtime/baseline-${repeat}-positive.out" \
      2>"${OUTPUT}/runtime/baseline-${repeat}-positive.stderr"
  fi
  python3 "${TASK}/project_runtime.py" --event-count 2 \
    "${OUTPUT}/runtime/composition-${repeat}-positive.out" \
    "${OUTPUT}/projected/composition-${repeat}-runtime.json"
  python3 "${TASK}/project_runtime.py" --event-count 2 --erase-trace \
    "${OUTPUT}/runtime/composition-${repeat}-positive.out" \
    "${OUTPUT}/projected/composition-${repeat}-erased.json"
  python3 "${TASK}/project_runtime.py" --event-count 0 --erase-trace \
    "${OUTPUT}/runtime/baseline-${repeat}-positive.out" \
    "${OUTPUT}/projected/baseline-${repeat}-erased.json"
  cmp "${OUTPUT}/projected/composition-${repeat}-erased.json" \
    "${OUTPUT}/projected/baseline-${repeat}-erased.json"

  python3 "${TASK}/project_match.py" --expect match \
    --input "${OUTPUT}/queries/composition-${repeat}-positive.json" \
    --driver "${driver}" \
    --runtime "${OUTPUT}/projected/composition-${repeat}-runtime.json" \
    --output "${OUTPUT}/projected/composition-${repeat}-positive.json"
  for query in too-short non-exhausted wrong-second-label; do
    python3 "${TASK}/project_match.py" --expect no-match \
      --input "${OUTPUT}/queries/composition-${repeat}-${query}.json" \
      --output "${OUTPUT}/projected/composition-${repeat}-${query}.json"
  done
  python3 "${TASK}/trusted_oracle.py" \
    "${OUTPUT}/queries/composition-${repeat}-positive.json" "${driver}" \
    "${OUTPUT}/projected/composition-${repeat}-trusted.json"
done

for query in positive too-short non-exhausted wrong-second-label; do
  cmp "${OUTPUT}/queries/composition-a-${query}.json" \
    "${OUTPUT}/queries/composition-b-${query}.json"
  cmp "${OUTPUT}/projected/composition-a-${query}.json" \
    "${OUTPUT}/projected/composition-b-${query}.json"
done
cmp "${OUTPUT}/projected/composition-a-trusted.json" \
  "${OUTPUT}/projected/composition-b-trusted.json"
cmp "${OUTPUT}/projected/composition-a-runtime.json" \
  "${OUTPUT}/projected/composition-b-runtime.json"
cmp "${OUTPUT}/projected/composition-a-erased.json" \
  "${OUTPUT}/projected/composition-b-erased.json"

python3 "${TASK}/selftest_projector.py" \
  "${OUTPUT}/queries/composition-a-positive.json" \
  "${COMPOSITION}/records/composition-a.json" \
  "${OUTPUT}/projected/composition-a-runtime.json" \
  "${OUTPUT}/projected/selftests.json"
jq -e '.verdict=="pass" and .compilerBackendInvocations==0 and .caseCount==26
  and all(.cases[]; .classification=="error" and .rejected)' \
  "${OUTPUT}/projected/selftests.json" >/dev/null
python3 "${TASK}/selftest_runtime.py" \
  "${OUTPUT}/runtime/composition-a-positive.out" \
  "${OUTPUT}/projected/runtime-selftests.json"
jq -e '.verdict=="pass" and .compilerBackendInvocations==0 and .caseCount==4
  and .validExactEventCount==2
  and all(.cases[]; .classification=="error" and .rejected)' \
  "${OUTPUT}/projected/runtime-selftests.json" >/dev/null

jq -n \
  --arg activation "${ACTIVATION}" --arg packetRepair "${PACKET_REPAIR}" \
  --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kStatus "$(git -C "${K_SOURCE}" status --short)" --arg krun "${KRUN_BIN}" \
  --arg frontendSha "${FRONTEND_SHA}" --arg packetSha "${PACKET_SHA}" \
  --arg checkpointSha "${CHECKPOINT_SHA}" --arg goalSha "${GOAL_SHA}" \
  --arg pathPlanSha "${PATH_PLAN_SHA}" \
  --arg packageSha "${PACKAGE_SHA}" --arg oneSha "${ONE_BUMP_SHA}" \
  --arg twoSha "${TWO_BUMP_SHA}" --arg threeSha "${THREE_BUMP_SHA}" \
  --arg exactText "${EXACT_PATTERN}" --arg exactSha "${EXACT_PATTERN_SHA}" \
  --arg wrongText "${WRONG_PATTERN}" --arg wrongSha "${WRONG_PATTERN_SHA}" \
  --arg projectorSha "${PROJECTOR_SHA}" --arg trustedSha "${TRUSTED_SHA}" \
  --arg selftestSha "${SELFTEST_SHA}" --arg runtimeSha "${RUNTIME_SHA}" \
  --arg runtimeSelftestSha "${RUNTIME_SELFTEST_SHA}" \
  --arg runtimeFixtureSha "${RUNTIME_FIXTURE_SHA}" \
  --arg replaySha "$(sha256sum "${TASK}/replay.sh" | awk '{print $1}')" \
  --arg verifySha "${VERIFY_SHA}" --arg accepted "${ACCEPTED_INTEGRATION}" \
  --arg acceptedTree "${ACCEPTED_TREE}" --arg acceptedSpineTree "${ACCEPTED_SPINE_TREE}" \
  --arg acceptedEvidenceTree "${ACCEPTED_EVIDENCE_TREE}" \
  --arg acceptedResultsSha "${ACCEPTED_RESULTS_SHA}" --arg acceptedReportSha "${ACCEPTED_REPORT_SHA}" \
  --argjson cycles "${CYCLE_COUNT}" \
  --slurpfile positive "${OUTPUT}/projected/composition-a-positive.json" \
  --slurpfile short "${OUTPUT}/projected/composition-a-too-short.json" \
  --slurpfile residual "${OUTPUT}/projected/composition-a-non-exhausted.json" \
  --slurpfile wrong "${OUTPUT}/projected/composition-a-wrong-second-label.json" \
  --slurpfile trusted "${OUTPUT}/projected/composition-a-trusted.json" \
  --slurpfile selftests "${OUTPUT}/projected/selftests.json" \
  --slurpfile runtimeSelftests "${OUTPUT}/projected/runtime-selftests.json" '
  {
    schemaVersion:1,
    task:"R3-G-04-k-native-rule-applied-next-event",
    verdict:"pass",
    activationRevision:$activation,
    startingRevision:$activation,
    packetRepairRevision:$packetRepair,
    substantiveFullOracleCycleCount:$cycles,
    cycleHistory:[
      {cycle:1,verdict:"packet ambiguity discovered",finalEvidence:false,
        finding:"the originally mandated bump + bump + bump input had two parses in the accepted non-associative syntax",
        resolution:"root packet repair 84ec8a9 replaced it with hold(bump + bump) + bump"},
      {cycle:2,verdict:"pass",finalEvidence:false,
        purpose:"validate repaired fixture and complete all inherited, matcher, erasure, repeat and failure oracles"},
      {cycle:3,verdict:"pass",finalEvidence:true,
        purpose:"regenerate committed evidence from the final reporting and assertion sources"}
    ],
    pin:{
      k:{release:$kRelease,commit:$kCommit,externalStatus:$kStatus,
        frontendJarSha256:$frontendSha,resolvedKrun:$krun,backend:"haskell"},
      contracts:{packetSha256:$packetSha,acceptanceCheckpointSha256:$checkpointSha,
        executionPatternGoalSha256:$goalSha,dependencyPathPlanSha256:$pathPlanSha,
        packageManifestSha256:$packageSha},
      acceptedR3G03:{integrationRevision:$accepted,integrationTree:$acceptedTree,
        spineTree:$acceptedSpineTree,evidenceTree:$acceptedEvidenceTree,
        resultsSha256:$acceptedResultsSha,reportSha256:$acceptedReportSha},
      inputs:{oneBumpSha256:$oneSha,twoBumpSha256:$twoSha,threeBumpSha256:$threeSha},
      matcherSources:{exactPairPatternSha256:$exactSha,wrongSecondLabelPatternSha256:$wrongSha,
        projectorSha256:$projectorSha,trustedOracleSha256:$trustedSha,
        selftestSha256:$selftestSha,runtimeProjectorSha256:$runtimeSha,
        runtimeSelftestSha256:$runtimeSelftestSha,
        runtimeSelftestFixtureSha256:$runtimeFixtureSha,
        replaySha256:$replaySha,verifierSha256:$verifySha}
    },
    resourcePolicy:{routineVerification:{backendInvocations:0},
      explicitFullReplay:{javaMaxHeapMiB:2048,javaActiveProcessorCount:2,
        overrideBounds:{javaMaxHeapMiB:[512,4096],javaActiveProcessorCount:[1,4]},
        routineEntryPointDisabled:true,directCommandRequired:true,
        installedJdkOptionPrecedenceProbe:true},
      reason:"avoid workstation exhaustion from the K launcher defaulting each Java process to an 8 GiB heap"},
    acceptanceFinalization:{rootFullReplayCompleted:true,
      finalEvidenceRegeneratedFromRootReplayOutput:true,
      backendInvocationsDuringFinalization:0},
    patterns:[
      {name:"exact-pair",text:$exactText,sha256:$exactSha,
        sharedVariables:["ID","LABEL","MODULE","SOURCE","LOCATION"],literalTail:".List"},
      {name:"wrong-second-label",text:$wrongText,sha256:$wrongSha,
        constrainedSecondLabel:"known-unequal-label",literalTail:".List"}
    ],
    ownership:{
      k:["match two adjacent ListItem/ruleApplied/ruleOrigin constructor graphs",
        "enforce five shared typed origin variables across both positions",
        "enforce literal .List exact exhaustion","enforce unequal second-label constraint",
        "return official substitution or exact Bottom"],
      host:["validate pinned KAST v4 envelope and nodes","flatten And/Equals substitution",
        "require five named bindings once and exact three generated completion shapes",
        "decode canonical tokens and compare raw origin with independent driver and runtime",
        "project ordered portable witnesses only after raw validation"]
    },
    invocations:{mode:"absolute krun --pattern --output json",backend:"haskell",
      total:8,normalSuccessfulExitCount:8,search:false,symbolic:false,
      repeats:["composition-a","composition-b"],
      perRepeat:["two-bump exact pair","one-bump exact pair","three-bump exact pair",
        "two-bump wrong second label"]},
    positiveMatch:$positive[0],
    noMatch:{
      tooShort:($short[0]+{query:"one event against exact pair"}),
      nonExhausted:($residual[0]+{query:"three events against literal .List exact pair"}),
      wrongSecondLabel:($wrong[0]+{query:"two events with unequal literal at position one"})
    },
    validation:{officialFormat:"KAST",officialVersion:4,
      exactBottomShape:"#Bottom{GeneratedTopCell}()",
      resolvedKrunIsPinnedKompileSibling:true,rawFiveFieldValuesValidatedAndOmitted:true,
      bothRawOccurrencesValidatedBeforePortableProjection:true,noPrettyMatcherOutputConsumed:true,
      noHostTraceSearchOrPairMatching:true,trustedSmallStructuralOracle:$trusted[0]},
    repeatInvariants:{allFourRawKastByteIdentical:true,allFourProjectionsByteIdentical:true,
      rawRuntimeProjectionByteIdentical:true,portableWitnessByteIdentical:true,
      bothFreshDefinitionsConsumed:true,noDefinitionTransformationByMatcher:true,
      noRuntimeTransitionAddedByMatcher:true},
    conservativity:{twoBumpInstrumentedAndBaselineKStateEqualAfterTraceErasure:true,
      bothFreshInstrumentedRepeatsChecked:true,
      invocations:{mode:"absolute krun concrete runtime",total:4,normalSuccessfulExitCount:4,
        perRepeat:["fresh instrumented two-bump execution","baseline two-bump execution"],
        repeats:["composition-a/baseline-a","composition-b/baseline-b"]}},
    inheritedOracles:{acceptedR3G03ReplayFromDetachedIntegration:true,
      acceptedEvidenceRegeneratedAndByteCompared:true,freshCompositionDefinitionsConsumed:true,
      packagePinPreserved:true,acceptedBuildDirectoriesUntouched:true},
    projectorFailures:$selftests[0],
    runtimeProjectorFailures:$runtimeSelftests[0],
    limitations:["exactly two concrete adjacent occurrences of one RuleApplied origin",
      "observed-event clock only","no distinct-event order, gap, subsequence scan or eventually-after",
      "no reusable temporal contract, symbolic execution, search, solver, monitor, corpus or domain event"],
    ambiguity:"none requiring a split",
    ambiguityHistory:{cycleOneParseAmbiguityRecorded:true,
      resolvedByRootPacketRepair:$packetRepair,remainingAmbiguityRequiringSplit:false},
    recommendedNextLeaf:"atomic multi-rule producer/allowlist packet",
    multiRuleProducerDependencyUnblocked:true
  }' >"${OUTPUT}/results.json"

cat >"${OUTPUT}/report.md" <<'EOF'
# R3-G-04 K-native exact `RuleApplied` next-event pair

Verdict: pass in three substantive full-oracle cycles.

Activation `68c95e7` was followed by packet repair `84ec8a9`, which replaced an
ambiguous three-bump input discovered in cycle one with the pinned unambiguous
`hold(bump + bump) + bump` input. Cycle two validated the repaired fixture and
all oracles. Cycle three regenerated worker evidence after tightening the
committed invocation history and exact 26-case assertion. Root acceptance
repair then made clean replay reproduce that three-cycle history and replaced
loose runtime token counting with exact event-structure validation. The final
root replay regenerated this evidence without adding a substantive worker
cycle; no ambiguity remains that requires a split.

The accepted R3-G-03 replay ran unchanged from a temporary detached checkout at
integration `6c88e2c`. It preserved that checkout's historical package pin,
regenerated and byte-compared accepted evidence, and produced two fresh
composition definitions under this task's ignored output. No accepted build
directory or external-K source was changed.

Pinned absolute `krun --pattern --output json` applied the committed exact-pair
pattern to `hold(bump) + bump` on both definitions. K returned each of the five
typed shared variables exactly once and no `REST` binding. The raw substitution
origin equaled the independent driver target and both concrete runtime event
origins before projection. The ordered portable result is indices `[0,1]`, two
`RuleApplied` constructors, and two equal origins: ID
`54a064c17f3eca9ce1b5619a3534d7898d572a42b209f9f17bb552dd266756e0`,
label `bump-state`, module `R3-G-01-P3-TRACE`, source
`repo://spine/trace-configuration-composition/fixtures/p3-trace.k`, and location
`Location(36,8,39,28)`. Raw source and source-derived ID stay in ignored output.

K returned exact zero-argument `#Bottom{GeneratedTopCell}` for all three
negative classes: the accepted one-bump program was too short, the three-bump
program left a residual event against literal `.List`, and the two-bump program
failed the unequal second-label pattern. All eight pattern invocations exited
normally and repeated byte-for-byte across the independently regenerated
definitions. The positive instrumented and baseline executions also had equal
`k`/`state` projections after trace erasure. These conservativity checks were
four separate absolute-`krun` executions: instrumented and baseline for each
of the two fresh-definition repeats, in addition to the eight matcher queries.

The host validated only the official KAST v4 envelope, exact substitution and
completion shapes, canonical tokens, raw equality, and portable projection. It
did not search a trace, infer adjacency or exhaustion, parse pretty matcher
output, or classify malformed KAST as no-match. An independent trusted-small
walker confirmed the five witness terms occur once and that no synthetic
`REST` exists. Twenty-six focused malformed-envelope cases failed with zero
compiler/backend invocations. Four additional zero-backend runtime-projector
cases rejected detached event/origin terms, malformed wrappers, residual trace
syntax, and the wrong exact event count.

This establishes only two adjacent same-origin observations on the
observed-event clock. It does not establish distinct-event order, gaps,
arbitrary subsequences, eventually-after, a temporal API, symbolic claims,
search, a monitor, corpus aggregation, or domain events. No ambiguity required
a split. The separate atomic multi-rule producer/allowlist leaf is now
dependency-unblocked.

Routine `bun run r3:g:rule-applied-next-event` verification is deliberately
zero-backend: it checks all committed pins, evidence invariants, Python source,
and adversarial runtime projection. The already completed root full replay is
the backend provenance for this evidence; finalization reprojected its raw
outputs after the reporting-only repair. The routine entry point cannot launch
a full replay. A deliberate direct `replay.sh` command caps every Java child at
2 GiB and two active processors by default, with hard override ceilings of 4
GiB and four CPUs. The installed JDK was probed to confirm `_JAVA_OPTIONS`
wins over the inherited launchers' explicit 8 GiB heap arguments. Do not run
that direct command while the workstation is under memory or swap pressure.
EOF

! rg -F "${REPO_ROOT}" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
! rg -F "accepted-source" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
if [[ "${R3_G_04_FREEZE_EVIDENCE:-0}" == "1" ]]; then
  mkdir -p "${EVIDENCE}"
  cp "${OUTPUT}/results.json" "${EVIDENCE}/results.json"
  cp "${OUTPUT}/report.md" "${EVIDENCE}/report.md"
else
  [[ -f "${EVIDENCE}/results.json" && -f "${EVIDENCE}/report.md" ]]
  cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"
  cmp "${EVIDENCE}/report.md" "${OUTPUT}/report.md"
fi
printf 'R3-G-04 K-native RuleApplied next-event replay: pass\n'
