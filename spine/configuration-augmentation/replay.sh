#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="21be4390f6c7e1f7f0e16b9c574e64404aeeb32a"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly HOOK_PATCH_SHA="bf9c788c89a201e74c9a51df23fe544333c8bf9898a8a9973dc4163d86f3e543"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/configuration-augmentation"
readonly EVIDENCE="${REPO_ROOT}/evidence/r2-g-06-k-configuration-augmentation"
readonly OUTPUT="${1:-${TASK}/build/acceptance}"
readonly CYCLES="${R2_G_06_FULL_CYCLE_COUNT:-1}"
readonly K_FILE="${TASK}/src/configuration-augmentation.k"
readonly DRIVER_SOURCE="${TASK}/src/java/org/kframework/kink/configuration/ConfigurationAugmentationDriver.java"
readonly HOOK_PATCH="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/upstream.patch"
readonly HOOK_DRIVER="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/src/org/kframework/kink/precfhook/PreCfHookDriver.java"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"
readonly BUILD_ROOT="${OUTPUT}/host"

for tool in bun git java javac jq kompile krun patch python3 sha256sum; do command -v "${tool}" >/dev/null; done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
[[ "$(sha256sum "${FRONTEND_JAR}" | awk '{print $1}')" == "${FRONTEND_SHA}" ]]
[[ "$(sha256sum "${HOOK_PATCH}" | awk '{print $1}')" == "${HOOK_PATCH_SHA}" ]]
[[ ! -e "${OUTPUT}" ]]

export LC_ALL=C LANG=C TZ=UTC
mkdir -p "${OUTPUT}"/{logs,records,runtime,projections,api} \
  "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile" \
  "${BUILD_ROOT}/overlay/classes" "${BUILD_ROOT}/driver-classes" \
  "${BUILD_ROOT}/oracle-root/driver-classes"

for file in DefinitionParsing.java Kompile.java; do
  cp "${K_SOURCE}/k-frontend/src/main/java/org/kframework/kompile/${file}" \
    "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile/${file}"
done
patch --fuzz=0 -d "${BUILD_ROOT}/overlay/source" -p1 <"${HOOK_PATCH}" \
  >"${OUTPUT}/logs/hook-patch.stdout" 2>"${OUTPUT}/logs/hook-patch.stderr"
javac -encoding UTF-8 -cp "${K_JAVA}/*" -d "${BUILD_ROOT}/overlay/classes" \
  "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java" \
  "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile/Kompile.java" \
  >"${OUTPUT}/logs/overlay-javac.stdout" 2>"${OUTPUT}/logs/overlay-javac.stderr"
javac -encoding UTF-8 -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  -d "${BUILD_ROOT}/driver-classes" "${DRIVER_SOURCE}" \
  >"${OUTPUT}/logs/driver-javac.stdout" 2>"${OUTPUT}/logs/driver-javac.stderr"
javac -encoding UTF-8 -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  -d "${BUILD_ROOT}/oracle-root/driver-classes" "${HOOK_DRIVER}" \
  >"${OUTPUT}/logs/oracle-driver-javac.stdout" 2>"${OUTPUT}/logs/oracle-driver-javac.stderr"
ln -s ../overlay/classes "${BUILD_ROOT}/oracle-root/classes"

kompile "${K_FILE}" --backend llvm \
  --main-module KINK-CONFIGURATION-AUGMENTATION \
  --syntax-module KINK-CONFIGURATION-AUGMENTATION-SYNTAX \
  --output-definition "${OUTPUT}/k-augmentation-kompiled" \
  >"${OUTPUT}/logs/k-augmentation.stdout" 2>"${OUTPUT}/logs/k-augmentation.stderr"

javap -classpath "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" -p org.kframework.kompile.Kompile >"${OUTPUT}/api/Kompile.signatures"
grep -Fq 'Function<org.kframework.definition.Definition, org.kframework.definition.Definition>, java.util.function.Function<org.kframework.definition.Definition, org.kframework.definition.Definition>' "${OUTPUT}/api/Kompile.signatures"
! rg -n '"(T|k|state|observation|0)"' "${DRIVER_SOURCE}"
for literal in '"T"' '"k"' '"state"' '"observation"' '"0"'; do grep -Fq "${literal}" "${K_FILE}"; done

readonly P3="${REPO_ROOT}/p3/fixtures/coupled.k"
readonly PROGRAM="${REPO_ROOT}/p3/fixtures/program.exp"
readonly FALLBACK="${REPO_ROOT}/investigations/w1-egress/fixtures/p3-observation.k"

kompile "${P3}" --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT}/baseline" >"${OUTPUT}/logs/baseline.stdout" 2>"${OUTPUT}/logs/baseline.stderr"

run_positive() {
  local mode="$1" output="$2"
  R2_G_06_BUILD_ROOT="${BUILD_ROOT}" R2_G_06_K_DEFINITION="${OUTPUT}/k-augmentation-kompiled" \
  R2_G_06_MODE="${mode}" R2_G_06_RECORD="${OUTPUT}/records/${output}.json" \
    "${TASK}/run-driver.sh" "${P3}" --backend haskell --emit-json \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
}
run_positive positive-a augmentation-a
run_positive positive-b augmentation-b

R2_G_05_OVERLAY_ROOT="${BUILD_ROOT}/oracle-root" R2_G_05_MODE=augment-a \
R2_G_05_RECORD="${OUTPUT}/records/r2-g-05-java-oracle.json" \
  "${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/run-driver.sh" \
    "${P3}" --backend haskell --emit-json --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT}/r2-g-05-java-oracle" \
    >"${OUTPUT}/logs/r2-g-05-java-oracle.stdout" 2>"${OUTPUT}/logs/r2-g-05-java-oracle.stderr"

kompile "${FALLBACK}" --backend haskell --emit-json \
  --main-module W1-P3-OBSERVATION --syntax-module W1-P3-OBSERVATION-SYNTAX \
  --output-definition "${OUTPUT}/source-fallback" \
  >"${OUTPUT}/logs/source-fallback.stdout" 2>"${OUTPUT}/logs/source-fallback.stderr"

run_negative() {
  local mode="$1" output="$2"
  set +e
  R2_G_06_BUILD_ROOT="${BUILD_ROOT}" R2_G_06_K_DEFINITION="${OUTPUT}/k-augmentation-kompiled" \
  R2_G_06_MODE="${mode}" R2_G_06_RECORD="${OUTPUT}/records/${output}.json" \
    "${TASK}/run-driver.sh" "${P3}" --backend haskell \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
  local exit_code=$?
  set -e
  [[ ${exit_code} -ne 0 ]]
  printf '%s\n' "${exit_code}" >"${OUTPUT}/logs/${output}.exit"
}
run_negative stale-target-content negative-stale
run_negative zero-target negative-zero
run_negative duplicate-target negative-duplicate
run_negative unsupported-path negative-path
run_negative conflict-existing negative-conflict
run_negative false-already-present negative-false-already

for output in baseline augmentation-a augmentation-b r2-g-05-java-oracle source-fallback; do
  krun "${PROGRAM}" --definition "${OUTPUT}/${output}" >"${OUTPUT}/runtime/${output}.out" 2>"${OUTPUT}/runtime/${output}.err"
  python3 "${TASK}/project_runtime.py" "${OUTPUT}/runtime/${output}.out" "${OUTPUT}/projections/${output}-runtime.json"
done
for output in baseline augmentation-a augmentation-b; do
  python3 "${REPO_ROOT}/investigations/w1-inprocess-adapter/normalize_identity_kore.py" \
    "${OUTPUT}/${output}/definition.kore" "${OUTPUT}/projections/${output}-definition.kore"
done
cmp "${OUTPUT}/projections/augmentation-a-definition.kore" "${OUTPUT}/projections/augmentation-b-definition.kore"
for artifact in syntaxDefinition.kore macros.kore; do cmp "${OUTPUT}/augmentation-a/${artifact}" "${OUTPUT}/augmentation-b/${artifact}"; done
cmp "${OUTPUT}/runtime/augmentation-a.out" "${OUTPUT}/runtime/augmentation-b.out"
python3 "${TASK}/project_runtime.py" --erase-observation "${OUTPUT}/runtime/augmentation-a.out" "${OUTPUT}/projections/augmentation-erased.json"
cmp "${OUTPUT}/projections/baseline-runtime.json" "${OUTPUT}/projections/augmentation-erased.json"
jq -e '.k=="1" and .state=="2" and .observation=="0"' "${OUTPUT}/projections/augmentation-a-runtime.json" >/dev/null

for output in augmentation-a r2-g-05-java-oracle source-fallback; do
  python3 "${TASK}/project_observation_kore.py" "${OUTPUT}/${output}/definition.kore" "${OUTPUT}/projections/${output}-observation.json"
done
jq -e --slurp '.[0].markers == .[1].markers and .[0].markers == .[2].markers and (.[0].markers | all(. > 0))' \
  "${OUTPUT}/projections/augmentation-a-observation.json" \
  "${OUTPUT}/projections/r2-g-05-java-oracle-observation.json" \
  "${OUTPUT}/projections/source-fallback-observation.json" >/dev/null

for record in augmentation-a augmentation-b; do
  jq -e '
    .status=="accepted" and .hookInvocations==1
    and .kInvocationsPass1==1 and .kInvocationsPass2==1
    and .candidateCountPass1==1 and .statusPass1=="apply"
    and .candidateCountPass2==1 and .statusPass2=="already-present"
    and .validatedOperationCount==1 and .applicationCount==1
    and .changedConfigurationCount==1 and .alreadyPresentValidatedCount==1
    and .secondSameReference and .metadataPreserved and .conditionsPreserved and .provenancePreserved
    and .beforeDefinition != .afterDefinition
    and .targetContentBefore != .targetContentAfter and .targetBodyBefore != .targetBodyAfter
    and .transformedDefinitionReturned and .postCfInvocations==1 and .postCfSameReference
    and .cfConstructed and .backendConstructed
  ' "${OUTPUT}/records/${record}.json" >/dev/null
done
jq -e --slurp '
  .[0].requestFingerprintPass1 == .[1].requestFingerprintPass1
  and .[0].responseFingerprintPass1 == .[1].responseFingerprintPass1
  and .[0].requestFingerprintPass2 == .[1].requestFingerprintPass2
  and .[0].responseFingerprintPass2 == .[1].responseFingerprintPass2
  and .[0].operationCanonicalPass1 == .[1].operationCanonicalPass1
  and .[0].operationCanonicalPass2 == .[1].operationCanonicalPass2
' "${OUTPUT}/records/augmentation-a.json" "${OUTPUT}/records/augmentation-b.json" >/dev/null

declare -A classes=(
  [negative-stale]=stale-precondition [negative-zero]=k-selection-failure
  [negative-duplicate]=k-selection-failure [negative-path]=path-operation-validation
  [negative-conflict]=conflicting-existing-state [negative-false-already]=result-envelope-validation
)
for record in "${!classes[@]}"; do
  jq -e --arg class "${classes[$record]}" '
    .status=="rejected" and .classification==$class and .hookInvocations==1
    and .applicationCount==0 and .postCfInvocations==0
    and (.transformedDefinitionReturned|not) and (.cfConstructed|not) and (.backendConstructed|not)
  ' "${OUTPUT}/records/${record}.json" >/dev/null
  [[ ! -e "${OUTPUT}/${record}/definition.kore" && ! -e "${OUTPUT}/${record}/compiled.bin" ]]
done
jq -e '.candidateCountPass1==0' "${OUTPUT}/records/negative-zero.json" >/dev/null
jq -e '.candidateCountPass1==2' "${OUTPUT}/records/negative-duplicate.json" >/dev/null
jq -e '.inputMutationCount==1 and .candidateCountPass2==1' "${OUTPUT}/records/negative-conflict.json" >/dev/null

{
  sha256sum "${K_FILE}" "${DRIVER_SOURCE}" "${HOOK_PATCH}"
  sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/"{DefinitionParsing,Kompile}.class
  sha256sum "${OUTPUT}"/records/*.json "${OUTPUT}"/runtime/*.out "${OUTPUT}"/projections/*.json
} >"${OUTPUT}/SHA256SUMS"

jq -n \
  --arg activation "${ACTIVATION}" --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kSource "${K_SOURCE}" --arg kStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kompile "${KOMPILE_BIN}" --arg frontendSha "${FRONTEND_SHA}" --arg hookPatchSha "${HOOK_PATCH_SHA}" \
  --arg kSourceSha "$(sha256sum "${K_FILE}"|awk '{print $1}')" --arg driverSha "$(sha256sum "${DRIVER_SOURCE}"|awk '{print $1}')" \
  --arg replaySha "$(sha256sum "${TASK}/replay.sh"|awk '{print $1}')" \
  --arg runnerSha "$(sha256sum "${TASK}/run-driver.sh"|awk '{print $1}')" \
  --arg runtimeProjectorSha "$(sha256sum "${TASK}/project_runtime.py"|awk '{print $1}')" \
  --arg observationProjectorSha "$(sha256sum "${TASK}/project_observation_kore.py"|awk '{print $1}')" \
  --arg verifierSha "$(sha256sum "${TASK}/verify.sh"|awk '{print $1}')" \
  --arg dpClass "$(sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/DefinitionParsing.class"|awk '{print $1}')" \
  --arg kompileClass "$(sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/Kompile.class"|awk '{print $1}')" \
  --argjson cycles "${CYCLES}" \
  --slurpfile a "${OUTPUT}/records/augmentation-a.json" --slurpfile b "${OUTPUT}/records/augmentation-b.json" \
  --slurpfile stale "${OUTPUT}/records/negative-stale.json" --slurpfile zero "${OUTPUT}/records/negative-zero.json" \
  --slurpfile duplicate "${OUTPUT}/records/negative-duplicate.json" --slurpfile path "${OUTPUT}/records/negative-path.json" \
  --slurpfile conflict "${OUTPUT}/records/negative-conflict.json" --slurpfile falseAlready "${OUTPUT}/records/negative-false-already.json" \
  --slurpfile runtime "${OUTPUT}/projections/augmentation-a-runtime.json" \
  --slurpfile projection "${OUTPUT}/projections/augmentation-a-observation.json" \
  --slurpfile javaOracle "${OUTPUT}/projections/r2-g-05-java-oracle-observation.json" \
  --slurpfile sourceOracle "${OUTPUT}/projections/source-fallback-observation.json" \
  '{schemaVersion:1,task:"R2-G-06-k-authored-configuration-augmentation",verdict:"pass",contract:"KConfigurationAugmentation-v1",fullCycleCount:$cycles,activationRevision:$activation,
    pin:{kRelease:$kRelease,kCommit:$kCommit,kSource:$kSource,kSourceStatus:$kStatus,resolvedKompile:$kompile,frontendJarSha256:$frontendSha,hookPatchSha256:$hookPatchSha,overlayClassSha256:{definitionParsing:$dpClass,kompile:$kompileClass},environment:{LC_ALL:"C",LANG:"C",TZ:"UTC"}},
    taskSourceSha256:{kSemantics:$kSourceSha,javaHost:$driverSha,replay:$replaySha,runner:$runnerSha,runtimeProjector:$runtimeProjectorSha,observationProjector:$observationProjectorSha,verifier:$verifierSha},
    ownership:{k:["structural target recognition","apply/already/conflict classification","candidate cardinality","target fingerprints","parent/template paths","new name and value","status"],java:["complete typed projection","canonical parsing and fingerprints","generic path validation/navigation","declared leaf clone/application","immutable graph and idempotence validation"]},
    positive:{first:($a[0]|{hookInvocations,kInvocationsPass1,kInvocationsPass2,requestFingerprintPass1,responseFingerprintPass1,candidateCountPass1,statusPass1,operationCanonicalPass1,resultCanonicalFingerprintPass1,requestFingerprintPass2,responseFingerprintPass2,candidateCountPass2,statusPass2,operationCanonicalPass2,resultCanonicalFingerprintPass2,targetLineage,targetContentBefore,targetContentAfter,targetBodyBefore,targetBodyAfter,beforeDefinition,afterDefinition,validatedOperationCount,applicationCount,changedConfigurationCount,alreadyPresentValidatedCount,secondSameReference,metadataPreserved,conditionsPreserved,provenancePreserved,transformedDefinitionReturned,postCfInvocations,postCfSameReference,cfConstructed,backendConstructed}),repeatStable:true,runtime:$runtime[0],erasedRuntimeEqual:true,normalizedArtifactsStable:true},
    oracles:{kAuthored:$projection[0],r2g05Java:$javaOracle[0],ordinarySource:$sourceOracle[0],generationMarkersEqual:true,provenanceDifference:"K-authored and R2-G-05 typed clones reuse P3 state-cell provenance; ordinary source has its own observation line"},
    negatives:{stale:($stale[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false),zero:($zero[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false),duplicate:($duplicate[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false),path:($path[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false),conflict:($conflict[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,candidateCountPass2,inputMutationCount,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false),falseAlready:($falseAlready[0]|{classification,hookInvocations,kInvocationsPass1,kInvocationsPass2,candidateCountPass1,alreadyPresentValidatedCount,applicationCount,transformedDefinitionReturned,postCfInvocations,cfConstructed,backendConstructed}|.backendArtifactsEmitted=false)},
    limitations:["one fixture-specific cloneLeafCellFromInput operation","temporary accepted hook overlay remains source-bound","no events, rule instrumentation, trace, monitor, matcher, C1, or C2"],packetAmbiguity:"none requiring a split",recommendedNextPacket:"conservative single-rule observation using the established branch-local configuration state, with no trace or matcher expansion"}' >"${OUTPUT}/results.json"

if [[ -f "${EVIDENCE}/results.json" ]]; then cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"; fi
printf 'R2-G-06 K-authored configuration augmentation replay: pass\n'
