#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="5cd72045cdc25a22ccf3b0ce08b3b3113d2e421d"
readonly ACCEPTED_WORKER="1a3100f"
readonly ACCEPTED_INTEGRATION="e5b5234"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly PACKET_SHA="a640cbf3d0aa44ee6358c16b086e5320980c81c8a576f6965208028ad6306dfb"
readonly CHECKPOINT_SHA="154402ad71465854a4897d88271a8c070cdb914d384267051161563dac7b0379"
readonly GOAL_SHA="ce6a40f0667d09f9c79a17f0f51857e561f95bbcc28592f0b177c45253ed2f43"
readonly COMPOSITION_REPLAY_SHA="2940bb97ab29b5ba2d7da82ff1d31b6371e0223cec90001061dab2138e5720e0"
readonly COMPOSITION_VERIFY_SHA="179202b0553011b000d91cac760720d35264e9b97685f839fbd95f81218f229c"
readonly COMPOSITION_RUNNER_SHA="03ab39fc12857635824f0a202264b87aa3a948d81bfc2d5139622af3853acfaa"
readonly COMPOSITION_TRACE_K_SHA="7f0ca5a574a38c206b2a681c5427324616a0dcace4a58b06f0cbc9c48ac6953b"
readonly COMPOSITION_CONFIG_K_SHA="b778344d7ccf46e8eaa13df97179a09eef0eaf8f99752956d210492a2df63da5"
readonly COMPOSITION_DRIVER_SHA="a42da3bf892215d11e2e23181388998b7d6ace7a9ef806c2907221c17bb94c9b"
readonly COMPOSITION_CONFIG_DRIVER_SHA="765651b4c8c9542a223d6f2b6bb5363e9c94539812d403fef4e295cc92e1d5c5"
readonly COMPOSITION_RUNTIME_PROJECTOR_SHA="db4883cc622c0fa2d177467ede498211b8478045734a8d0577ddb0f8b77841ca"
readonly COMPOSITION_RESULTS_SHA="de653bc22adfff3fd9158155a2ae385a9019bf8231f98e5570a5cf126bbfb960"
readonly COMPOSITION_REPORT_SHA="88c678b029071d630b5b1205efdc695e5cc014bcadd55aa4b1c23a3537bebde0"
readonly COMPOSITION_SPINE_TREE="420e936b6ce2c43dae99c4c6a017c72fb6a5e7f6"
readonly COMPOSITION_EVIDENCE_TREE="d32b12bd380f37196f16483359023726a1a65200"
readonly ACCEPTED_WORKER_TREE="2767cdcfab8c4e711bb652cf269a601329da3019"
readonly ACCEPTED_INTEGRATION_TREE="2767cdcfab8c4e711bb652cf269a601329da3019"
readonly FIRST_WORKER_TREE="9d98aae67e18cf2cedb0c6fc1c2abe2f74fb1ee3"
readonly FIRST_INTEGRATION_TREE="9d98aae67e18cf2cedb0c6fc1c2abe2f74fb1ee3"
readonly REPAIR_WORKER_TREE="108c5a0e58b827abcdb0a9f16c360c92cc9c4164"
readonly REPAIR_INTEGRATION_TREE="108c5a0e58b827abcdb0a9f16c360c92cc9c4164"
readonly FIRING_SHA="46210dddc66714c3d8d226711510cf8421774214016c508c72a833a05370f6b5"
readonly NONFIRING_SHA="4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865"
readonly HEAD_PATTERN_SHA="bc936fbc35bd844fe08a18462c4fc0ed42e5cb846e209cc42b2b5d1f5df25c5b"
readonly WRONG_PATTERN_SHA="33cfae1aa869ab2194ed4961da54f9dddf9cf1531bd266983ab0f43f0ca9da4a"
readonly PROJECTOR_SHA="c3c1121bd7426e98cace655e15e374310ff2a6b663b60df1b6802a99e836afba"
readonly TRUSTED_ORACLE_SHA="5769b9a36e2463accc35997e47b75ce09e0122055db0a622e5ba3d5fe9f3906e"
readonly SELFTEST_SHA="f1367628548852f079bcecc0b8ae517739e97a7ff134f29df339bb06fbb275ec"
readonly PACKAGE_SHA="fc2157a57283595390dea7b1436eb8f37b9ae494b706916d83c374362c27a8da"
readonly INHERITED_ORACLES_SHA="1436c1fcb98161ba5a90640ac7fa7d8c7cc9f622f853a68199d737977b0132c0"
readonly INHERITED_PROVENANCE_SHA="1ca0700900ace3ccb42cf9d2886cdad7c8dbca31f55a2fb2ec673e6ddb72536d"
readonly INHERITED_APPLICATIONS_SHA="032f8a3002340dafdde79ed1d5aae6c19a0c68db166fea910675f52473288900"

readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/rule-applied-head-match"
readonly EVIDENCE="${REPO_ROOT}/evidence/r3-g-03-k-native-rule-applied-head-match"
readonly OUTPUT="${1:-${TASK}/build/acceptance}"
readonly COMPOSITION="${OUTPUT}/composition"
readonly ACCEPTED_SOURCE="${OUTPUT}/accepted-source"
readonly HEAD_PATTERN_FILE="${TASK}/patterns/head.k"
readonly WRONG_PATTERN_FILE="${TASK}/patterns/wrong-label.k"
readonly FIRING="${REPO_ROOT}/p3/fixtures/program.exp"
readonly NONFIRING="${REPO_ROOT}/spine/trace-configuration-composition/fixtures/nonfiring.exp"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly KRUN_BIN="$(readlink -f "$(command -v krun)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly FRONTEND_JAR="${K_ROOT}/lib/kframework/java/k-frontend-1.0-SNAPSHOT.jar"

check_sha() { [[ "$(sha256sum "$2" | awk '{print $1}')" == "$1" ]]; }
for tool in bun cmp git jq kompile krun python3 rg sha256sum; do command -v "${tool}" >/dev/null; done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
[[ "${KRUN_BIN}" == "${K_ROOT}/bin/krun" ]]
[[ "${KRUN_BIN}" == *"${K_COMMIT}"* ]]
"${KOMPILE_BIN}" --version | grep -F "${K_RELEASE}" >/dev/null
toolchain_pair_valid() {
  local resolved_kompile="$1" resolved_krun="$2" expected_commit="$3"
  local pinned_root
  pinned_root="$(dirname "$(dirname "${resolved_kompile}")")"
  [[ "${resolved_krun}" == "${pinned_root}/bin/krun"
    && "${resolved_kompile}" == *"${expected_commit}"*
    && "${resolved_krun}" == *"${expected_commit}"* ]]
}
toolchain_pair_valid "${KOMPILE_BIN}" "${KRUN_BIN}" "${K_COMMIT}"
! toolchain_pair_valid "${KOMPILE_BIN}" "/tmp/path-prepended-fake-krun" "${K_COMMIT}"
check_sha "${FRONTEND_SHA}" "${FRONTEND_JAR}"
check_sha "${PACKET_SHA}" "${REPO_ROOT}/tasks/wave-3/R3-G-03-k-native-rule-applied-head-match.md"
check_sha "${CHECKPOINT_SHA}" "${REPO_ROOT}/draft/k-in-k-r3-g-02a-acceptance-checkpoint-2026-08-20.md"
check_sha "${GOAL_SHA}" "${REPO_ROOT}/draft/goal/execution-pattern-matching.md"
check_sha "${COMPOSITION_REPLAY_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/replay.sh"
check_sha "${COMPOSITION_VERIFY_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/verify.sh"
check_sha "${COMPOSITION_RUNNER_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/run-driver.sh"
check_sha "${COMPOSITION_TRACE_K_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/src/rule-applied-trace.k"
check_sha "${COMPOSITION_CONFIG_K_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/src/trace-configuration-augmentation.k"
check_sha "${COMPOSITION_DRIVER_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java"
check_sha "${COMPOSITION_CONFIG_DRIVER_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java"
check_sha "${COMPOSITION_RUNTIME_PROJECTOR_SHA}" "${REPO_ROOT}/spine/trace-configuration-composition/project_runtime.py"
check_sha "${COMPOSITION_RESULTS_SHA}" "${REPO_ROOT}/evidence/r3-g-02-k-authored-trace-configuration/results.json"
check_sha "${COMPOSITION_REPORT_SHA}" "${REPO_ROOT}/evidence/r3-g-02-k-authored-trace-configuration/report.md"
check_sha "${FIRING_SHA}" "${FIRING}"
check_sha "${NONFIRING_SHA}" "${NONFIRING}"
check_sha "${HEAD_PATTERN_SHA}" "${HEAD_PATTERN_FILE}"
check_sha "${WRONG_PATTERN_SHA}" "${WRONG_PATTERN_FILE}"
check_sha "${PROJECTOR_SHA}" "${TASK}/project_match.py"
check_sha "${TRUSTED_ORACLE_SHA}" "${TASK}/trusted_oracle.py"
check_sha "${SELFTEST_SHA}" "${TASK}/selftest_projector.py"
check_sha "${PACKAGE_SHA}" "${REPO_ROOT}/package.json"
[[ "$(git rev-parse HEAD:spine/trace-configuration-composition)" == "${COMPOSITION_SPINE_TREE}" ]]
[[ "$(git rev-parse HEAD:evidence/r3-g-02-k-authored-trace-configuration)" == "${COMPOSITION_EVIDENCE_TREE}" ]]
[[ "$(git rev-parse 1a3100f^{tree})" == "${ACCEPTED_WORKER_TREE}" ]]
[[ "$(git rev-parse e5b5234^{tree})" == "${ACCEPTED_INTEGRATION_TREE}" ]]
[[ "$(git rev-parse 596b026^{tree})" == "${FIRST_WORKER_TREE}" ]]
[[ "$(git rev-parse 8d657e5^{tree})" == "${FIRST_INTEGRATION_TREE}" ]]
[[ "$(git rev-parse bba487b^{tree})" == "${REPAIR_WORKER_TREE}" ]]
[[ "$(git rev-parse daf4d60^{tree})" == "${REPAIR_INTEGRATION_TREE}" ]]

# Validate the package delta without a temporary tracked file.
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
expected["scripts"]["r3:g:rule-applied-head-match"] = \
    "bash spine/rule-applied-head-match/verify.sh"
if current != expected:
    raise SystemExit("package.json changed beyond the one owned script entry")
PY

while IFS= read -r path; do
  [[ -z "${path}" ]] && continue
  case "${path}" in
    package.json|spine/rule-applied-head-match/*|evidence/r3-g-03-k-native-rule-applied-head-match/*) ;;
    *) printf 'path outside packet ownership: %s\n' "${path}" >&2; exit 1 ;;
  esac
done < <({ git diff --name-only "${ACTIVATION}" --; git ls-files --others --exclude-standard; } | LC_ALL=C sort -u)

[[ ! -e "${OUTPUT}" ]]
export LC_ALL=C LANG=C TZ=UTC
mkdir -p "${OUTPUT}"/{logs,queries,projected}

cleanup() {
  if [[ -e "${ACCEPTED_SOURCE}/.git" ]]; then
    git worktree remove --force "${ACCEPTED_SOURCE}" >/dev/null 2>&1 || true
  fi
}
trap cleanup EXIT
git worktree add --detach "${ACCEPTED_SOURCE}" "${ACCEPTED_WORKER}" \
  >"${OUTPUT}/logs/accepted-worktree.stdout" 2>"${OUTPUT}/logs/accepted-worktree.stderr"
(
  cd "${ACCEPTED_SOURCE}"
  R3_G_02A_REPAIR_CYCLE_COUNT=2 \
    bash spine/trace-configuration-composition/replay.sh "${COMPOSITION}"
) >"${OUTPUT}/logs/composition-replay.stdout" 2>"${OUTPUT}/logs/composition-replay.stderr"
git worktree remove "${ACCEPTED_SOURCE}"
trap - EXIT
[[ ! -e "${ACCEPTED_SOURCE}" ]]
check_sha "${COMPOSITION_RESULTS_SHA}" "${COMPOSITION}/results.json"
check_sha "${COMPOSITION_REPORT_SHA}" "${COMPOSITION}/report.md"
for repeat in a b; do
  jq -e '.ruleTargetLabel=="bump-state"
    and .ruleTargetLabel!="known-unequal-label"' \
    "${COMPOSITION}/records/composition-${repeat}.json" >/dev/null
done

readonly HEAD_PATTERN="$(<"${HEAD_PATTERN_FILE}")"
readonly WRONG_PATTERN="$(<"${WRONG_PATTERN_FILE}")"
for repeat in a b; do
  definition="${COMPOSITION}/composition-${repeat}"
  "${KRUN_BIN}" "${FIRING}" --definition "${definition}" --pattern "${HEAD_PATTERN}" --output json \
    >"${OUTPUT}/queries/composition-${repeat}-head.json" \
    2>"${OUTPUT}/queries/composition-${repeat}-head.stderr"
  "${KRUN_BIN}" "${NONFIRING}" --definition "${definition}" --pattern "${HEAD_PATTERN}" --output json \
    >"${OUTPUT}/queries/composition-${repeat}-empty.json" \
    2>"${OUTPUT}/queries/composition-${repeat}-empty.stderr"
  "${KRUN_BIN}" "${FIRING}" --definition "${definition}" --pattern "${WRONG_PATTERN}" --output json \
    >"${OUTPUT}/queries/composition-${repeat}-wrong-label.json" \
    2>"${OUTPUT}/queries/composition-${repeat}-wrong-label.stderr"
  printf '0\n' >"${OUTPUT}/queries/composition-${repeat}-exit-codes.txt"

  python3 "${TASK}/project_match.py" --expect match \
    --input "${OUTPUT}/queries/composition-${repeat}-head.json" \
    --driver "${COMPOSITION}/records/composition-${repeat}.json" \
    --runtime "${COMPOSITION}/projections/composition-${repeat}-firing.json" \
    --portable-runtime "${COMPOSITION}/projections/portable-firing.json" \
    --output "${OUTPUT}/projected/composition-${repeat}-head.json"
  python3 "${TASK}/project_match.py" --expect no-match \
    --input "${OUTPUT}/queries/composition-${repeat}-empty.json" \
    --output "${OUTPUT}/projected/composition-${repeat}-empty.json"
  python3 "${TASK}/project_match.py" --expect no-match \
    --input "${OUTPUT}/queries/composition-${repeat}-wrong-label.json" \
    --output "${OUTPUT}/projected/composition-${repeat}-wrong-label.json"
  python3 "${TASK}/trusted_oracle.py" \
    "${OUTPUT}/queries/composition-${repeat}-head.json" \
    "${COMPOSITION}/records/composition-${repeat}.json" \
    "${OUTPUT}/projected/composition-${repeat}-trusted.json"
done

for query in head empty wrong-label; do
  cmp "${OUTPUT}/queries/composition-a-${query}.json" \
    "${OUTPUT}/queries/composition-b-${query}.json"
  cmp "${OUTPUT}/projected/composition-a-${query}.json" \
    "${OUTPUT}/projected/composition-b-${query}.json"
done
cmp "${OUTPUT}/projected/composition-a-trusted.json" \
  "${OUTPUT}/projected/composition-b-trusted.json"

python3 "${TASK}/selftest_projector.py" \
  "${OUTPUT}/queries/composition-a-head.json" \
  "${COMPOSITION}/records/composition-a.json" \
  "${COMPOSITION}/projections/composition-a-firing.json" \
  "${COMPOSITION}/projections/portable-firing.json" \
  "${OUTPUT}/projected/selftests.json"
jq -e '.verdict=="pass" and .compilerBackendInvocations==0 and .caseCount>=22
  and all(.cases[]; .classification=="error" and .rejected)' \
  "${OUTPUT}/projected/selftests.json" >/dev/null

check_section_sha() {
  local filter="$1" expected="$2"
  [[ "$(jq -cS "${filter}" "${COMPOSITION}/results.json" | sha256sum | awk '{print $1}')" == "${expected}" ]]
}
check_section_sha '.oracles' "${INHERITED_ORACLES_SHA}"
check_section_sha '.provenanceInvariant' "${INHERITED_PROVENANCE_SHA}"
check_section_sha '.configurationApplication,.ruleApplication' "${INHERITED_APPLICATIONS_SHA}"

jq -n \
  --arg activation "${ACTIVATION}" --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg krun "${KRUN_BIN}" --arg frontendSha "${FRONTEND_SHA}" \
  --arg packetSha "${PACKET_SHA}" --arg checkpointSha "${CHECKPOINT_SHA}" \
  --arg goalSha "${GOAL_SHA}" --arg packageSha "${PACKAGE_SHA}" \
  --arg headText "${HEAD_PATTERN}" --arg headSha "${HEAD_PATTERN_SHA}" \
  --arg wrongText "${WRONG_PATTERN}" --arg wrongSha "${WRONG_PATTERN_SHA}" \
  --arg projectorSha "${PROJECTOR_SHA}" --arg trustedSha "${TRUSTED_ORACLE_SHA}" \
  --arg selftestSha "${SELFTEST_SHA}" --arg firingSha "${FIRING_SHA}" \
  --arg taskReplaySha "$(sha256sum "${TASK}/replay.sh" | awk '{print $1}')" \
  --arg taskVerifySha "$(sha256sum "${TASK}/verify.sh" | awk '{print $1}')" \
  --arg nonfiringSha "${NONFIRING_SHA}" \
  --arg compositionReplaySha "${COMPOSITION_REPLAY_SHA}" \
  --arg compositionResultsSha "${COMPOSITION_RESULTS_SHA}" \
  --arg compositionReportSha "${COMPOSITION_REPORT_SHA}" \
  --arg compositionSpineTree "${COMPOSITION_SPINE_TREE}" \
  --arg compositionEvidenceTree "${COMPOSITION_EVIDENCE_TREE}" \
  --arg acceptedWorker "${ACCEPTED_WORKER}" --arg acceptedIntegration "${ACCEPTED_INTEGRATION}" \
  --arg inheritedOraclesSha "${INHERITED_ORACLES_SHA}" \
  --arg inheritedProvenanceSha "${INHERITED_PROVENANCE_SHA}" \
  --arg inheritedApplicationsSha "${INHERITED_APPLICATIONS_SHA}" \
  --slurpfile match "${OUTPUT}/projected/composition-a-head.json" \
  --slurpfile empty "${OUTPUT}/projected/composition-a-empty.json" \
  --slurpfile wrong "${OUTPUT}/projected/composition-a-wrong-label.json" \
  --slurpfile trusted "${OUTPUT}/projected/composition-a-trusted.json" \
  --slurpfile selftests "${OUTPUT}/projected/selftests.json" '
  {
    schemaVersion:1,
    task:"R3-G-03-k-native-rule-applied-head-match",
    verdict:"pass",
    activationRevision:$activation,
    startingRevision:$activation,
    substantiveFullOracleCycleCount:1,
    pin:{
      k:{release:$kRelease,commit:$kCommit,externalStatus:$kStatus,
        frontendJarSha256:$frontendSha,resolvedKrun:$krun,backend:"haskell"},
      contracts:{packetSha256:$packetSha,acceptanceCheckpointSha256:$checkpointSha,
        executionPatternGoalSha256:$goalSha,packageManifestSha256:$packageSha},
      acceptedComposition:{workerRevision:$acceptedWorker,integrationRevision:$acceptedIntegration,
        workerAndIntegrationTreesByteIdentical:true,replaySha256:$compositionReplaySha,
        spineTree:$compositionSpineTree,evidenceTree:$compositionEvidenceTree,
        resultsSha256:$compositionResultsSha,reportSha256:$compositionReportSha},
      inputs:{firingSha256:$firingSha,nonfiringSha256:$nonfiringSha},
      matcherSources:{headPatternSha256:$headSha,wrongLabelPatternSha256:$wrongSha,
        projectorSha256:$projectorSha,trustedOracleSha256:$trustedSha,
        selftestSha256:$selftestSha,replaySha256:$taskReplaySha,
        verifierSha256:$taskVerifySha}
    },
    patterns:[
      {name:"head",text:$headText,sha256:$headSha},
      {name:"wrong-label",text:$wrongText,sha256:$wrongSha,
        constrainedLabel:"known-unequal-label"}
    ],
    ownership:{
      k:["match trace cell and head constructor graph","bind five typed String payloads and List tail",
        "enforce wrong-label payload constraint","return substitution or exact Bottom"],
      host:["validate pinned KAST v4 envelope and nodes","flatten And/Equals substitution",
        "require six named typed bindings and exact three typed generated completion shapes",
        "decode canonical String tokens and exact empty List tail",
        "compare raw origin to independent driver/runtime before portable projection"]
    },
    invocations:{mode:"krun --pattern --output json",backend:"haskell",
      total:6,normalSuccessfulExitCount:6,search:false,symbolic:false,
      repeats:["composition-a","composition-b"],
      perRepeat:["firing head","non-firing head","firing wrong-label"]},
    positiveMatch:$match[0],
    noMatch:{
      emptyTrace:($empty[0]+{query:"head pattern over accepted non-firing input"}),
      wrongLabel:($wrong[0]+{query:"K-authored unequal-label pattern over accepted firing input"})
    },
    validation:{officialFormat:"KAST",officialVersion:4,
      exactBottomShape:"#Bottom{GeneratedTopCell}()",
      resolvedKrunIsPinnedKompileSibling:true,
      pathPrependedFakeKrunRejectedBeforeOutput:true,
      rawFiveFieldValuesValidatedAndOmitted:true,portableProjectionAfterRawValidation:true,
      noPrettyOutputConsumed:true,noHostSemanticMatching:true,
      trustedSmallStructuralOracle:$trusted[0]},
    repeatInvariants:{rawHeadKastByteIdentical:true,rawEmptyKastByteIdentical:true,
      rawWrongLabelKastByteIdentical:true,portableProjectionByteIdentical:true,
      bothFreshDefinitionsConsumed:true,noDefinitionTransformationByMatcher:true,
      noRuntimeTransitionAddedByMatcher:true},
    inheritedOracles:{acceptedReplayRegeneratedAndByteCompared:true,
      runtimeErasureRepeatOraclesSha256:$inheritedOraclesSha,
      provenanceInvariantSha256:$inheritedProvenanceSha,
      configurationAndRuleApplicationsSha256:$inheritedApplicationsSha,
      acceptedResultsSha256:$compositionResultsSha,acceptedReportSha256:$compositionReportSha},
    projectorFailures:$selftests[0],
    limitations:["one concrete RuleApplied event at index zero","one exact empty tail",
      "two exhaustive terminating concrete executions","no ordered subsequence or temporal operator",
      "no symbolic execution, search, solver, absence beyond these concrete runs, monitor, corpus or domain event"],
    ambiguity:"none requiring a split; accepted replay runs unchanged from its accepted worker revision because activation contains byte-identical cherry-picks",
    recommendedNextLeaf:"a bounded two-event concrete ordered-subsequence matcher with explicit intervening-event semantics",
    nextOrderedSubsequenceDependencyUnblocked:true
  }' >"${OUTPUT}/results.json"

cat >"${OUTPUT}/report.md" <<'EOF'
# R3-G-03 K-native `RuleApplied` head match

Verdict: pass in one substantive full-oracle cycle.

The unchanged accepted R3-G-02A replay regenerated two fresh composed Haskell
definitions in this task's ignored build tree and byte-compared its accepted
evidence. It ran from the accepted worker revision because activation contains
the corresponding byte-identical cherry-picks; no accepted source was vendored,
modified, or consumed from an accepted build directory.

Pinned `krun --pattern --output json` applied the committed head pattern to
both definitions. K returned the six exact typed bindings `ID:String`,
`LABEL:String`, `MODULE:String`, `SOURCE:String`, `LOCATION:String`, and
`REST:List`. The five raw run-local origin fields equaled both the independently
captured composition driver target and runtime event before projection.
`REST` was exact `.List`, so the portable witness is event index zero,
constructor `RuleApplied`, origin ID
`54a064c17f3eca9ce1b5619a3534d7898d572a42b209f9f17bb552dd266756e0`,
label `bump-state`, module `R3-G-01-P3-TRACE`, source
`repo://spine/trace-configuration-composition/fixtures/p3-trace.k`, and location
`Location(36,8,39,28)`. Raw values remain only in ignored output.

The accepted non-firing input returned exact zero-argument
`#Bottom{GeneratedTopCell}`. A second K-authored pattern constraining the label
to `known-unequal-label` returned the same exact bottom for the firing input.
All six backend invocations terminated normally, and all three raw KAST results
were byte-identical across the two independently compiled repeats.

The host consumed only official KAST v4 JSON. It validated the envelope and
node algebra, flattened official `#And`/`#Equals`, enforced exact binding
cardinality, sorts, and all three generated completion-cell inner shapes,
decoded canonical String and Int tokens, required exact empty List, and
projected only after raw validation. The resolved `krun` was required to be the
commit-bearing sibling of pinned `kompile`; a fake resolved path failed the
static pre-output check. An independent trusted-small walker confirmed the five
actual substitution terms and empty tail. Twenty-two focused malformed-envelope
cases were classified as errors with zero compiler or backend invocations;
none became semantic no-match.

This is one concrete head match and two exhaustive terminating concrete
no-matches. It does not establish a general absence result, ordered
subsequence, temporal operator, symbolic path, solver claim, monitor, corpus,
or domain event. No packet ambiguity required a split. The dependency for a
separate bounded two-event ordered-subsequence leaf is unblocked, but that
future leaf must define its intervening-event semantics explicitly.
EOF

! rg -F "${REPO_ROOT}" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
! rg -F "accepted-source" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
if [[ "${R3_G_03_FREEZE_EVIDENCE:-0}" == "1" ]]; then
  mkdir -p "${EVIDENCE}"
  cp "${OUTPUT}/results.json" "${EVIDENCE}/results.json"
  cp "${OUTPUT}/report.md" "${EVIDENCE}/report.md"
else
  [[ -f "${EVIDENCE}/results.json" && -f "${EVIDENCE}/report.md" ]]
  cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"
  cmp "${EVIDENCE}/report.md" "${OUTPUT}/report.md"
fi
printf 'R3-G-03 K-native RuleApplied head match replay: pass\n'
