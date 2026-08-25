#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="68c95e7f336eb07be4c5bf05246e99c1c64bef18"
readonly PACKET_REPAIR="84ec8a95221f877c4ca810a96b8126477577d2fa"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${ROOT}/spine/rule-applied-next-event"
readonly EVIDENCE="${ROOT}/evidence/r3-g-04-k-native-rule-applied-next-event"
readonly RESULTS="${EVIDENCE}/results.json"
readonly REPORT="${EVIDENCE}/report.md"
readonly JAVA_HEAP_MB="${KINK_JAVA_MAX_HEAP_MB:-2048}"
readonly JAVA_CPUS="${KINK_JAVA_CPUS:-2}"

[[ "${JAVA_HEAP_MB}" =~ ^[0-9]+$ && "${JAVA_HEAP_MB}" -ge 512 && "${JAVA_HEAP_MB}" -le 4096 ]]
[[ "${JAVA_CPUS}" =~ ^[0-9]+$ && "${JAVA_CPUS}" -ge 1 && "${JAVA_CPUS}" -le 4 ]]
export _JAVA_OPTIONS="${_JAVA_OPTIONS:+${_JAVA_OPTIONS} }-Xmx${JAVA_HEAP_MB}m -XX:ActiveProcessorCount=${JAVA_CPUS}"

for tool in git jq python3 rg sha256sum; do command -v "${tool}" >/dev/null; done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
git merge-base --is-ancestor "${PACKET_REPAIR}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ -f "${RESULTS}" && -f "${REPORT}" ]]

[[ "${R3_G_04_FULL_REPLAY:-0}" == "0" ]]

python3 -m py_compile \
  "${TASK}/project_match.py" "${TASK}/project_runtime.py" \
  "${TASK}/selftest_projector.py" "${TASK}/selftest_runtime.py" \
  "${TASK}/trusted_oracle.py"

readonly TEMP_DIR="$(mktemp -d)"
trap 'rm -rf -- "${TEMP_DIR}"' EXIT
python3 "${TASK}/project_runtime.py" --event-count 2 \
  "${TASK}/fixtures/runtime-two-event.pretty" "${TEMP_DIR}/runtime.json"
python3 "${TASK}/selftest_runtime.py" \
  "${TASK}/fixtures/runtime-two-event.pretty" "${TEMP_DIR}/runtime-selftests.json"
jq -e '.trace|length==2' "${TEMP_DIR}/runtime.json" >/dev/null
jq -e '.verdict=="pass" and .caseCount==4 and .compilerBackendInvocations==0
  and all(.cases[]; .classification=="error" and .rejected)' \
  "${TEMP_DIR}/runtime-selftests.json" >/dev/null

check_source_sha() {
  local field="$1" path="$2"
  [[ "$(jq -r "${field}" "${RESULTS}")" == "$(sha256sum "${path}" | awk '{print $1}')" ]]
}
check_source_sha '.pin.matcherSources.exactPairPatternSha256' "${TASK}/patterns/exact-pair.k"
check_source_sha '.pin.matcherSources.wrongSecondLabelPatternSha256' "${TASK}/patterns/wrong-second-label.k"
check_source_sha '.pin.matcherSources.projectorSha256' "${TASK}/project_match.py"
check_source_sha '.pin.matcherSources.trustedOracleSha256' "${TASK}/trusted_oracle.py"
check_source_sha '.pin.matcherSources.selftestSha256' "${TASK}/selftest_projector.py"
check_source_sha '.pin.matcherSources.runtimeProjectorSha256' "${TASK}/project_runtime.py"
check_source_sha '.pin.matcherSources.runtimeSelftestSha256' "${TASK}/selftest_runtime.py"
check_source_sha '.pin.matcherSources.runtimeSelftestFixtureSha256' "${TASK}/fixtures/runtime-two-event.pretty"
check_source_sha '.pin.matcherSources.replaySha256' "${TASK}/replay.sh"
check_source_sha '.pin.matcherSources.verifierSha256' "${TASK}/verify.sh"
check_source_sha '.pin.inputs.twoBumpSha256' "${TASK}/fixtures/two-bump.exp"
check_source_sha '.pin.inputs.threeBumpSha256' "${TASK}/fixtures/three-bump.exp"

jq -e '
  .schemaVersion==1 and .task=="R3-G-04-k-native-rule-applied-next-event"
  and .verdict=="pass" and .substantiveFullOracleCycleCount==3
  and .activationRevision=="68c95e7f336eb07be4c5bf05246e99c1c64bef18"
  and .packetRepairRevision=="84ec8a95221f877c4ca810a96b8126477577d2fa"
  and .invocations.total==8 and .invocations.normalSuccessfulExitCount==8
  and .positiveMatch.status=="match"
  and .positiveMatch.eventIndices==[0,1]
  and .positiveMatch.constructors==["RuleApplied","RuleApplied"]
  and .positiveMatch.witnesses[0].origin==.positiveMatch.witnesses[1].origin
  and .positiveMatch.exactTraceExhaustion=={literal:".List",ownedBy:"K",remainingEventCount:0}
  and all(.noMatch[]; .status=="no-match" and .officialResult=="#Bottom{GeneratedTopCell}()")
  and .validation.resolvedKrunIsPinnedKompileSibling
  and .validation.bothRawOccurrencesValidatedBeforePortableProjection
  and .validation.noHostTraceSearchOrPairMatching
  and .repeatInvariants.allFourRawKastByteIdentical
  and .repeatInvariants.allFourProjectionsByteIdentical
  and .conservativity.invocations.total==4
  and .conservativity.invocations.normalSuccessfulExitCount==4
  and .inheritedOracles.acceptedEvidenceRegeneratedAndByteCompared
  and .projectorFailures.verdict=="pass" and .projectorFailures.caseCount==26
  and .projectorFailures.compilerBackendInvocations==0
  and .runtimeProjectorFailures.verdict=="pass" and .runtimeProjectorFailures.caseCount==4
  and .runtimeProjectorFailures.compilerBackendInvocations==0
  and .resourcePolicy.routineVerification.backendInvocations==0
  and .resourcePolicy.explicitFullReplay.javaMaxHeapMiB==2048
  and .resourcePolicy.explicitFullReplay.javaActiveProcessorCount==2
  and .resourcePolicy.explicitFullReplay.routineEntryPointDisabled
  and .resourcePolicy.explicitFullReplay.directCommandRequired
  and .resourcePolicy.explicitFullReplay.installedJdkOptionPrecedenceProbe
  and .acceptanceFinalization.rootFullReplayCompleted
  and .acceptanceFinalization.finalEvidenceRegeneratedFromRootReplayOutput
  and .acceptanceFinalization.backendInvocationsDuringFinalization==0
  and .ambiguityHistory.resolvedByRootPacketRepair==.packetRepairRevision
  and .ambiguityHistory.remainingAmbiguityRequiringSplit==false
  and .multiRuleProducerDependencyUnblocked
' "${RESULTS}" >/dev/null

rg -F 'root replay regenerated this evidence' "${REPORT}" >/dev/null
rg -F 'Four additional zero-backend runtime-projector' "${REPORT}" >/dev/null
! rg -F "${ROOT}" "${RESULTS}" "${REPORT}"
git diff --check
printf 'R3-G-04 resource-bounded evidence verification: pass (zero backend invocations)\n'
