#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION_REVISION="d16e1aee298b8008f9a33e26b3aaceb056c3ad80"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly K_FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK_DIR="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype"
readonly OUTPUT_ROOT="${1:-${TASK_DIR}/build/acceptance}"
readonly MANIFEST="${TASK_DIR}/source-manifest.json"
readonly UPSTREAM_PATCH="${TASK_DIR}/upstream.patch"
readonly DRIVER_SOURCE="${TASK_DIR}/src/org/kframework/kink/precfhook/PreCfHookDriver.java"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"
readonly OVERLAY_ROOT="${OUTPUT_ROOT}/overlay"
readonly OVERLAY_SOURCE_ROOT="${OVERLAY_ROOT}/source"
readonly FULL_CYCLE_COUNT="${R2_G_05_FULL_CYCLE_COUNT:-1}"

git merge-base --is-ancestor "${ACTIVATION_REVISION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == "$(jq -r .expectedSourceStatus "${MANIFEST}")" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
[[ "$(sha256sum "${FRONTEND_JAR}" | awk '{print $1}')" == "${K_FRONTEND_SHA}" ]]
[[ ! -e "${OUTPUT_ROOT}" ]]

export LC_ALL=C
export LANG=C
export TZ=UTC

mkdir -p \
  "${OVERLAY_SOURCE_ROOT}/k-frontend/src/main/java/org/kframework/kompile" \
  "${OVERLAY_ROOT}/classes" \
  "${OVERLAY_ROOT}/driver-classes" \
  "${OUTPUT_ROOT}/api" \
  "${OUTPUT_ROOT}/logs" \
  "${OUTPUT_ROOT}/records" \
  "${OUTPUT_ROOT}/runtime" \
  "${OUTPUT_ROOT}/projections"

for relative in \
  k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java \
  k-frontend/src/main/java/org/kframework/kompile/Kompile.java; do
  expected="$(jq -r --arg path "${relative}" '.files[$path]' "${MANIFEST}")"
  [[ "${expected}" != "null" ]]
  [[ "$(sha256sum "${K_SOURCE}/${relative}" | awk '{print $1}')" == "${expected}" ]]
  cp "${K_SOURCE}/${relative}" "${OVERLAY_SOURCE_ROOT}/${relative}"
done

patch --fuzz=0 -d "${OVERLAY_SOURCE_ROOT}" -p1 <"${UPSTREAM_PATCH}" \
  >"${OUTPUT_ROOT}/logs/patch.stdout" 2>"${OUTPUT_ROOT}/logs/patch.stderr"

javac -encoding UTF-8 -cp "${K_JAVA}/*" -d "${OVERLAY_ROOT}/classes" \
  "${OVERLAY_SOURCE_ROOT}/k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java" \
  "${OVERLAY_SOURCE_ROOT}/k-frontend/src/main/java/org/kframework/kompile/Kompile.java" \
  >"${OUTPUT_ROOT}/logs/overlay-javac.stdout" 2>"${OUTPUT_ROOT}/logs/overlay-javac.stderr"
javac -encoding UTF-8 -cp "${OVERLAY_ROOT}/classes:${K_JAVA}/*" \
  -d "${OVERLAY_ROOT}/driver-classes" "${DRIVER_SOURCE}" \
  >"${OUTPUT_ROOT}/logs/driver-javac.stdout" 2>"${OUTPUT_ROOT}/logs/driver-javac.stderr"

javap -classpath "${OVERLAY_ROOT}/classes:${K_JAVA}/*" -p \
  org.kframework.kompile.Kompile >"${OUTPUT_ROOT}/api/Kompile.signatures"
javap -classpath "${OVERLAY_ROOT}/classes:${K_JAVA}/*" -p \
  org.kframework.kompile.DefinitionParsing >"${OUTPUT_ROOT}/api/DefinitionParsing.signatures"
javap -classpath "${OVERLAY_ROOT}/classes:${K_JAVA}/*" -c -p \
  org.kframework.kompile.DefinitionParsing >"${OUTPUT_ROOT}/api/DefinitionParsing.bytecode"
grep -Fq 'Function<org.kframework.definition.Definition, org.kframework.definition.Definition>, java.util.function.Function<org.kframework.definition.Definition, org.kframework.definition.Definition>' \
  "${OUTPUT_ROOT}/api/Kompile.signatures"
grep -Fq 'excludedModuleTags, java.util.function.Function' \
  <(sed 's/scala.collection.immutable.Set/java.util.Set/g' "${OUTPUT_ROOT}/api/DefinitionParsing.signatures") || \
  grep -Fq 'java.util.Set<org.kframework.attributes.Att$Key>, java.util.function.Function' \
    "${OUTPUT_ROOT}/api/DefinitionParsing.signatures"
python3 - "${OUTPUT_ROOT}/api/DefinitionParsing.bytecode" <<'PY'
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8")
signature = "private org.kframework.definition.Definition resolveConfigBubbles(org.kframework.definition.Definition, java.util.function.Function"
start = text.index(signature)
end = text.index("\n  private ", start + len(signature))
method = text[start:end]
callback = method.index("java/util/function/Function.apply")
cell_check = method.index("checkConfigCells")
generation_transform = method.rindex("DefinitionTransformer.apply")
assert callback < cell_check < generation_transform
assert "GenerateSentencesFromConfigDecl.gen" in text
PY

readonly DRIVER="${TASK_DIR}/run-driver.sh"
readonly P3="${REPO_ROOT}/p3/fixtures/coupled.k"
readonly P3_PROGRAM="${REPO_ROOT}/p3/fixtures/program.exp"
readonly SOURCE_FALLBACK="${REPO_ROOT}/investigations/w1-egress/fixtures/p3-observation.k"

kompile "${P3}" --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/baseline" \
  >"${OUTPUT_ROOT}/logs/baseline.stdout" 2>"${OUTPUT_ROOT}/logs/baseline.stderr"

run_positive() {
  local mode="$1"
  local output="$2"
  R2_G_05_OVERLAY_ROOT="${OVERLAY_ROOT}" \
  R2_G_05_MODE="${mode}" \
  R2_G_05_RECORD="${OUTPUT_ROOT}/records/${output}.json" \
    "${DRIVER}" "${P3}" --backend haskell --emit-json \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT_ROOT}/${output}" \
      >"${OUTPUT_ROOT}/logs/${output}.stdout" 2>"${OUTPUT_ROOT}/logs/${output}.stderr"
}

run_positive default-identity default-identity
run_positive explicit-identity explicit-identity
run_positive augment-a augmentation-a
run_positive augment-b augmentation-b

kompile "${SOURCE_FALLBACK}" --backend haskell --emit-json \
  --main-module W1-P3-OBSERVATION --syntax-module W1-P3-OBSERVATION-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/source-fallback" \
  >"${OUTPUT_ROOT}/logs/source-fallback.stdout" 2>"${OUTPUT_ROOT}/logs/source-fallback.stderr"

run_negative() {
  local mode="$1"
  local output="$2"
  set +e
  R2_G_05_OVERLAY_ROOT="${OVERLAY_ROOT}" \
  R2_G_05_MODE="${mode}" \
  R2_G_05_RECORD="${OUTPUT_ROOT}/records/${output}.json" \
    "${DRIVER}" "${P3}" --backend haskell \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT_ROOT}/${output}" \
      >"${OUTPUT_ROOT}/logs/${output}.stdout" 2>"${OUTPUT_ROOT}/logs/${output}.stderr"
  local result=$?
  set -e
  [[ "${result}" -ne 0 ]]
  printf '%s\n' "${result}" >"${OUTPUT_ROOT}/logs/${output}.exit"
}

run_negative return-null negative-null
run_negative throw-sentinel negative-throw
run_negative unauthorized-nonconfig negative-nonconfig
run_negative duplicate-k negative-duplicate-k

for output in baseline default-identity explicit-identity augmentation-a augmentation-b source-fallback; do
  krun "${P3_PROGRAM}" --definition "${OUTPUT_ROOT}/${output}" \
    >"${OUTPUT_ROOT}/runtime/${output}.out" 2>"${OUTPUT_ROOT}/runtime/${output}.err"
  python3 "${TASK_DIR}/project_runtime.py" \
    "${OUTPUT_ROOT}/runtime/${output}.out" "${OUTPUT_ROOT}/projections/${output}-runtime.json"
done

for output in baseline default-identity explicit-identity augmentation-a augmentation-b; do
  python3 "${REPO_ROOT}/investigations/w1-inprocess-adapter/normalize_identity_kore.py" \
    "${OUTPUT_ROOT}/${output}/definition.kore" "${OUTPUT_ROOT}/projections/${output}-definition.kore"
done
cmp "${OUTPUT_ROOT}/projections/baseline-definition.kore" "${OUTPUT_ROOT}/projections/default-identity-definition.kore"
cmp "${OUTPUT_ROOT}/projections/baseline-definition.kore" "${OUTPUT_ROOT}/projections/explicit-identity-definition.kore"
for artifact in syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT_ROOT}/baseline/${artifact}" "${OUTPUT_ROOT}/default-identity/${artifact}"
  cmp "${OUTPUT_ROOT}/baseline/${artifact}" "${OUTPUT_ROOT}/explicit-identity/${artifact}"
done
cmp "${OUTPUT_ROOT}/runtime/baseline.out" "${OUTPUT_ROOT}/runtime/default-identity.out"
cmp "${OUTPUT_ROOT}/runtime/baseline.out" "${OUTPUT_ROOT}/runtime/explicit-identity.out"

cmp "${OUTPUT_ROOT}/projections/augmentation-a-definition.kore" "${OUTPUT_ROOT}/projections/augmentation-b-definition.kore"
for artifact in syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT_ROOT}/augmentation-a/${artifact}" "${OUTPUT_ROOT}/augmentation-b/${artifact}"
done
cmp "${OUTPUT_ROOT}/runtime/augmentation-a.out" "${OUTPUT_ROOT}/runtime/augmentation-b.out"

python3 "${TASK_DIR}/project_runtime.py" --erase-observation \
  "${OUTPUT_ROOT}/runtime/augmentation-a.out" "${OUTPUT_ROOT}/projections/augmentation-a-erased-runtime.json"
python3 "${TASK_DIR}/project_runtime.py" --erase-observation \
  "${OUTPUT_ROOT}/runtime/source-fallback.out" "${OUTPUT_ROOT}/projections/source-fallback-erased-runtime.json"
cmp "${OUTPUT_ROOT}/projections/baseline-runtime.json" "${OUTPUT_ROOT}/projections/augmentation-a-erased-runtime.json"
cmp "${OUTPUT_ROOT}/projections/baseline-runtime.json" "${OUTPUT_ROOT}/projections/source-fallback-erased-runtime.json"
jq -e '.observation == "0" and .k == "1" and .state == "2"' \
  "${OUTPUT_ROOT}/projections/augmentation-a-runtime.json" >/dev/null

python3 "${TASK_DIR}/project_observation_kore.py" \
  "${OUTPUT_ROOT}/augmentation-a/definition.kore" "${OUTPUT_ROOT}/projections/augmentation-observation.json"
python3 "${TASK_DIR}/project_observation_kore.py" \
  "${OUTPUT_ROOT}/source-fallback/definition.kore" "${OUTPUT_ROOT}/projections/source-fallback-observation.json"
jq -e '.markers | all(. > 0)' "${OUTPUT_ROOT}/projections/augmentation-observation.json" >/dev/null
jq -e --slurp '.[0].markers == .[1].markers' \
  "${OUTPUT_ROOT}/projections/augmentation-observation.json" \
  "${OUTPUT_ROOT}/projections/source-fallback-observation.json" >/dev/null

jq -e '
  .status == "accepted" and .mode == "default-identity"
  and .hookInvocations == 0 and .postCfAdapterInvocations == 1
  and .postCfSameReference and .cfOutputConstructed and .backendArtifactsConstructed
  and (.kompileCodeSource | contains("/overlay/classes/"))
' "${OUTPUT_ROOT}/records/default-identity.json" >/dev/null
jq -e '
  .status == "accepted" and .mode == "explicit-identity"
  and .hookInvocations == 1 and .hookSameReference
  and .taskValidationAccepted and .preFingerprint == .postFingerprint
  and .preModuleCount == .postModuleCount and .preSentenceCount == .postSentenceCount
  and .preConfigurationCount == .postConfigurationCount
  and .prePrimarySourceCount == .postPrimarySourceCount
  and .postCfAdapterInvocations == 1 and .postCfSameReference
' "${OUTPUT_ROOT}/records/explicit-identity.json" >/dev/null
for output in augmentation-a augmentation-b; do
  jq -e '
    .status == "accepted" and .hookInvocations == 1 and (.hookSameReference | not)
    and .taskValidationAccepted and .targetConfigurations == 1 and .changedConfigurations == 1
    and .sideConditionsPreserved and .exactStructuralDelta
    and .preModuleCount == .postModuleCount and .preSentenceCount == .postSentenceCount
    and .preConfigurationCount == .postConfigurationCount
    and .prePrimarySourceCount == .postPrimarySourceCount
    and .postCfAdapterInvocations == 1 and .postCfSameReference
    and (.postCfContainsConfiguration | not) and .officialObservationSentences
    and .cfOutputConstructed and .backendArtifactsConstructed
  ' "${OUTPUT_ROOT}/records/${output}.json" >/dev/null
done

grep -Fq 'Configuration transformer returned null Definition at' \
  "${OUTPUT_ROOT}/logs/negative-null.stderr"
grep -Fq 'post-config-parse-pre-cell-check' "${OUTPUT_ROOT}/logs/negative-null.stderr"
grep -Fq 'r2-g-05-sentinel-transformer-exception' "${OUTPUT_ROOT}/logs/negative-throw.stderr"
grep -Fq 'unauthorized non-configuration sentence change' "${OUTPUT_ROOT}/logs/negative-nonconfig.stderr"
grep -Fq 'Multiple K cell declarations detected' "${OUTPUT_ROOT}/logs/negative-duplicate-k.stderr"
jq -e '
  .status == "rejected" and .hookInvocations == 1 and (.taskValidationInvoked | not)
  and .postCfAdapterInvocations == 0 and (.cfOutputConstructed | not)
  and (.backendArtifactsConstructed | not)
  and .rejectionBoundary == "post-config-parse-pre-cell-check"
' "${OUTPUT_ROOT}/records/negative-null.json" "${OUTPUT_ROOT}/records/negative-throw.json" >/dev/null
jq -e '
  .status == "rejected" and .hookInvocations == 1 and .taskValidationInvoked
  and (.taskValidationAccepted | not) and .postCfAdapterInvocations == 0
  and (.cfOutputConstructed | not) and (.backendArtifactsConstructed | not)
  and .rejectionBoundary == "task-validation-pre-cell-check"
' "${OUTPUT_ROOT}/records/negative-nonconfig.json" >/dev/null
jq -e '
  .status == "rejected" and .hookInvocations == 1 and .taskValidationAccepted
  and .postCfAdapterInvocations == 0 and (.cfOutputConstructed | not)
  and (.backendArtifactsConstructed | not)
  and .rejectionBoundary == "official-transformed-input-cell-check"
' "${OUTPUT_ROOT}/records/negative-duplicate-k.json" >/dev/null
for output in negative-null negative-throw negative-nonconfig negative-duplicate-k; do
  [[ ! -e "${OUTPUT_ROOT}/${output}/definition.kore" ]]
  [[ ! -e "${OUTPUT_ROOT}/${output}/compiled.bin" ]]
done

{
  sha256sum "${UPSTREAM_PATCH}" "${DRIVER_SOURCE}"
  sha256sum \
    "${OVERLAY_ROOT}/classes/org/kframework/kompile/DefinitionParsing.class" \
    "${OVERLAY_ROOT}/classes/org/kframework/kompile/Kompile.class"
  sha256sum "${OUTPUT_ROOT}"/records/*.json
  sha256sum "${OUTPUT_ROOT}"/runtime/*.out
  sha256sum "${OUTPUT_ROOT}"/projections/*.json
} >"${OUTPUT_ROOT}/SHA256SUMS"

jq -n \
  --arg activationRevision "${ACTIVATION_REVISION}" \
  --arg kRelease "${K_RELEASE}" \
  --arg kCommit "${K_COMMIT}" \
  --arg kSource "${K_SOURCE}" \
  --arg kSourceStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kompile "${KOMPILE_BIN}" \
  --arg frontendJar "${FRONTEND_JAR}" \
  --arg frontendJarSha "${K_FRONTEND_SHA}" \
  --arg patchSha "$(sha256sum "${UPSTREAM_PATCH}" | awk '{print $1}')" \
  --arg driverSha "$(sha256sum "${DRIVER_SOURCE}" | awk '{print $1}')" \
  --arg definitionParsingSourceSha "$(jq -r '.files["k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java"]' "${MANIFEST}")" \
  --arg kompileSourceSha "$(jq -r '.files["k-frontend/src/main/java/org/kframework/kompile/Kompile.java"]' "${MANIFEST}")" \
  --arg definitionParsingClassSha "$(sha256sum "${OVERLAY_ROOT}/classes/org/kframework/kompile/DefinitionParsing.class" | awk '{print $1}')" \
  --arg kompileClassSha "$(sha256sum "${OVERLAY_ROOT}/classes/org/kframework/kompile/Kompile.class" | awk '{print $1}')" \
  --argjson cycles "${FULL_CYCLE_COUNT}" \
  --slurpfile defaultIdentity "${OUTPUT_ROOT}/records/default-identity.json" \
  --slurpfile explicitIdentity "${OUTPUT_ROOT}/records/explicit-identity.json" \
  --slurpfile augmentationA "${OUTPUT_ROOT}/records/augmentation-a.json" \
  --slurpfile augmentationB "${OUTPUT_ROOT}/records/augmentation-b.json" \
  --slurpfile nullNegative "${OUTPUT_ROOT}/records/negative-null.json" \
  --slurpfile throwNegative "${OUTPUT_ROOT}/records/negative-throw.json" \
  --slurpfile nonConfigNegative "${OUTPUT_ROOT}/records/negative-nonconfig.json" \
  --slurpfile duplicateNegative "${OUTPUT_ROOT}/records/negative-duplicate-k.json" \
  --slurpfile runtime "${OUTPUT_ROOT}/projections/augmentation-a-runtime.json" \
  --slurpfile observation "${OUTPUT_ROOT}/projections/augmentation-observation.json" \
  --slurpfile sourceObservation "${OUTPUT_ROOT}/projections/source-fallback-observation.json" \
  '{
    schemaVersion: 1,
    task: "R2-G-05-pre-cf-hook-prototype",
    verdict: "pass",
    contract: "OfficialConfigurationTransformHook-v0",
    fullCycleCount: $cycles,
    activationRevision: $activationRevision,
    pin: {
      kRelease: $kRelease, kCommit: $kCommit, kSource: $kSource,
      kSourceStatus: $kSourceStatus, resolvedKompile: $kompile,
      frontendJar: $frontendJar, frontendJarSha256: $frontendJarSha,
      environment: {LC_ALL:"C", LANG:"C", TZ:"UTC"}
    },
    overlay: {
      patchSha256: $patchSha,
      patchedFiles: [
        {path:"k-frontend/src/main/java/org/kframework/kompile/DefinitionParsing.java", sourceSha256:$definitionParsingSourceSha, classSha256:$definitionParsingClassSha},
        {path:"k-frontend/src/main/java/org/kframework/kompile/Kompile.java", sourceSha256:$kompileSourceSha, classSha256:$kompileClassSha}
      ],
      officialSourceOrInstallModified: false,
      classpathPrecedenceVerified: true,
      bytecodeOrderVerified: ["Function.apply", "checkConfigCells", "GenerateSentencesFromConfigDecl.gen"]
    },
    taskSourceSha256: {driver: $driverSha},
    hook: {
      signature: "Function<Definition,Definition> transformConfigurations",
      boundary: "post-config-parse-pre-cell-check",
      invocation: "exactly once per top-level compilation",
      default: "identity",
      postCfAdapter: "OfficialDefinitionAdapter-v1 unchanged"
    },
    identity: {
      defaultEntry: ($defaultIdentity[0] | {status, hookInvocations, postCfAdapterInvocations, postCfSameReference, cfOutputConstructed, backendArtifactsConstructed}),
      explicit: ($explicitIdentity[0] | {status, callbackBoundary, hookInvocations, hookSameReference, taskValidationAccepted, preModuleCount, postModuleCount, preSentenceCount, postSentenceCount, preConfigurationCount, postConfigurationCount, prePrimarySourceCount, postPrimarySourceCount, preFingerprint, postFingerprint, postCfAdapterInvocations, postCfSameReference}),
      focusedKoreEqualToBaseline: true, syntaxKoreEqual: true, macrosEqual: true, runtimeEqual: true
    },
    augmentation: {
      first: ($augmentationA[0] | {status, callbackBoundary, hookInvocations, hookSameReference, taskValidationAccepted, targetConfigurations, changedConfigurations, sideConditionsPreserved, exactStructuralDelta, preModuleCount, postModuleCount, preSentenceCount, postSentenceCount, preConfigurationCount, postConfigurationCount, prePrimarySourceCount, postPrimarySourceCount, preFingerprint, postFingerprint, postCfAdapterInvocations, postCfSameReference, postCfContainsConfiguration, officialObservationSentences, cfOutputConstructed, backendArtifactsConstructed}),
      repeat: ($augmentationB[0] | {status, hookInvocations, targetConfigurations, changedConfigurations, preFingerprint, postFingerprint, postCfAdapterInvocations, officialObservationSentences, backendArtifactsConstructed}),
      runtime: $runtime[0], stableNormalizedArtifacts: true,
      erasedRuntimeEqualToBaseline: true, observationProjection: $observation[0]
    },
    sourceFallback: {structuralProjection: $sourceObservation[0], structuralMarkersEqual: true, provenanceDifference: "typed clone keeps P3 source and reuses the state-cell Location; ordinary source has its own observation line Location"},
    negatives: {
      nullResult: ($nullNegative[0] | {status, rejectionBoundary, error, hookInvocations, taskValidationInvoked, taskValidationAccepted, postCfAdapterInvocations, cfOutputConstructed, backendArtifactsConstructed}),
      transformerException: ($throwNegative[0] | {status, rejectionBoundary, error, hookInvocations, taskValidationInvoked, taskValidationAccepted, postCfAdapterInvocations, cfOutputConstructed, backendArtifactsConstructed}),
      unauthorizedNonConfiguration: ($nonConfigNegative[0] | {status, rejectionBoundary, error, hookInvocations, taskValidationInvoked, taskValidationAccepted, postCfAdapterInvocations, cfOutputConstructed, backendArtifactsConstructed}),
      duplicateKCell: ($duplicateNegative[0] | {status, rejectionBoundary, error, hookInvocations, taskValidationInvoked, taskValidationAccepted, postCfAdapterInvocations, cfOutputConstructed, backendArtifactsConstructed})
    },
    limitations: [
      "fixture-specific inert typed cell only",
      "prototype overlay, not an accepted public K API",
      "no configuration transport, K-facing patch, event, rule instrumentation, trace, matcher, C1, or C2"
    ],
    packetAmbiguity: "none requiring a split",
    recommendedNextPacket: "a K-authored, branch-local configuration augmentation using this one hook while preserving official CF ownership; still no event or rule instrumentation"
  }' >"${OUTPUT_ROOT}/results.json"

if [[ -f "${TASK_DIR}/results.json" ]]; then
  cmp "${TASK_DIR}/results.json" "${OUTPUT_ROOT}/results.json"
fi

printf 'R2-G-05 pre-CF hook prototype replay: pass\n'
