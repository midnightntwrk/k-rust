#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="a038c5172135676512f1b1f206aa9a79539884d2"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly HOOK_PATCH_SHA="bf9c788c89a201e74c9a51df23fe544333c8bf9898a8a9973dc4163d86f3e543"
readonly CONFIG_K_SHA="8c913e9692b84504d9589cc0ba98d6b32d2bbad104359b591c7f0be858c8cd3e"
readonly CONFIG_JAVA_SHA="dc7f77c8bb615f760dea9946792f6dee8001e0d4a44842787b1c95332e3b942f"
readonly CONFIG_REPLAY_SHA="875a888ec7d7bde6dec54381c55f6b4a4adf7cb33cfa99c2b97ecac4b26bd681"
readonly CONFIG_RUNNER_SHA="23cf22c167f361c099abacb42c4e26d04b19403e6ee8fce64b4513dffdcb4af4"
readonly CONFIG_VERIFY_SHA="142efdd308d53b408f01e530474ed75307517fbbdb22023188093cff2fab21b5"
readonly CONFIG_EVIDENCE_SHA="71f97b6f601eb35c2a56ff68d0c3f5a44e705a7280ea87d93e7f52018a916b72"
readonly P3_SHA="941ae576a67090a88815974648ea1c552bb1bf033ca100fdb3a286c4da66c0f5"
readonly FIRING_SHA="46210dddc66714c3d8d226711510cf8421774214016c508c72a833a05370f6b5"
readonly NORMALIZER_SHA="de87f170a560303571f6bb3711f162a7afa3c3737448376cec87b6aca50129c1"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/rule-observation"
readonly CONFIG_TASK="${REPO_ROOT}/spine/configuration-augmentation"
readonly EVIDENCE="${REPO_ROOT}/evidence/r2-g-07-single-rule-observation"
readonly OUTPUT="${1:-${TASK}/build/acceptance}"
readonly CYCLES="${R2_G_07_FULL_CYCLE_COUNT:-1}"
readonly OBS_K="${TASK}/src/rule-observation.k"
readonly DRIVER="${TASK}/src/java/org/kframework/kink/observation/RuleObservationDriver.java"
readonly P3="${REPO_ROOT}/p3/fixtures/coupled.k"
readonly FIRING="${REPO_ROOT}/p3/fixtures/program.exp"
readonly NORMALIZER="${REPO_ROOT}/investigations/w1-inprocess-adapter/normalize_identity_kore.py"
readonly CONFIG_K="${CONFIG_TASK}/src/configuration-augmentation.k"
readonly CONFIG_DRIVER="${CONFIG_TASK}/src/java/org/kframework/kink/configuration/ConfigurationAugmentationDriver.java"
readonly HOOK_PATCH="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/upstream.patch"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"
readonly BUILD_ROOT="${OUTPUT}/host"

for tool in bun cmp git java javac jq kompile krun patch python3 rg sha256sum; do command -v "${tool}" >/dev/null; done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
[[ "$(sha256sum "${FRONTEND_JAR}" | awk '{print $1}')" == "${FRONTEND_SHA}" ]]
[[ "$(sha256sum "${HOOK_PATCH}" | awk '{print $1}')" == "${HOOK_PATCH_SHA}" ]]
[[ "$(sha256sum "${CONFIG_K}" | awk '{print $1}')" == "${CONFIG_K_SHA}" ]]
[[ "$(sha256sum "${CONFIG_DRIVER}" | awk '{print $1}')" == "${CONFIG_JAVA_SHA}" ]]
[[ "$(sha256sum "${CONFIG_TASK}/replay.sh" | awk '{print $1}')" == "${CONFIG_REPLAY_SHA}" ]]
[[ "$(sha256sum "${CONFIG_TASK}/run-driver.sh" | awk '{print $1}')" == "${CONFIG_RUNNER_SHA}" ]]
[[ "$(sha256sum "${CONFIG_TASK}/verify.sh" | awk '{print $1}')" == "${CONFIG_VERIFY_SHA}" ]]
[[ "$(sha256sum "${REPO_ROOT}/evidence/r2-g-06-k-configuration-augmentation/results.json" | awk '{print $1}')" == "${CONFIG_EVIDENCE_SHA}" ]]
[[ "$(sha256sum "${P3}" | awk '{print $1}')" == "${P3_SHA}" ]]
[[ "$(sha256sum "${FIRING}" | awk '{print $1}')" == "${FIRING_SHA}" ]]
[[ "$(sha256sum "${NORMALIZER}" | awk '{print $1}')" == "${NORMALIZER_SHA}" ]]
[[ ! -e "${OUTPUT}" ]]

export LC_ALL=C LANG=C TZ=UTC
mkdir -p "${OUTPUT}"/{logs,records,runtime,projections,api} \
  "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile" \
  "${BUILD_ROOT}/overlay/classes" "${BUILD_ROOT}/driver-classes" \
  "${BUILD_ROOT}/configuration-oracle/driver-classes" \
  "${BUILD_ROOT}/configuration-oracle/overlay"

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
  -d "${BUILD_ROOT}/driver-classes" "${DRIVER}" \
  >"${OUTPUT}/logs/driver-javac.stdout" 2>"${OUTPUT}/logs/driver-javac.stderr"
java -cp "${BUILD_ROOT}/driver-classes:${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  org.kframework.kink.observation.RuleObservationDriver --parser-self-test \
  >"${OUTPUT}/logs/parser-self-test.stdout" 2>"${OUTPUT}/logs/parser-self-test.stderr"
javac -encoding UTF-8 -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  -d "${BUILD_ROOT}/configuration-oracle/driver-classes" "${CONFIG_DRIVER}" \
  >"${OUTPUT}/logs/configuration-oracle-javac.stdout" 2>"${OUTPUT}/logs/configuration-oracle-javac.stderr"
ln -s ../../overlay/classes "${BUILD_ROOT}/configuration-oracle/overlay/classes"

kompile "${CONFIG_K}" --backend llvm \
  --main-module KINK-CONFIGURATION-AUGMENTATION \
  --syntax-module KINK-CONFIGURATION-AUGMENTATION-SYNTAX \
  --output-definition "${OUTPUT}/configuration-k-kompiled" \
  >"${OUTPUT}/logs/configuration-k.stdout" 2>"${OUTPUT}/logs/configuration-k.stderr"
kompile "${OBS_K}" --backend llvm \
  --main-module KINK-RULE-OBSERVATION \
  --syntax-module KINK-RULE-OBSERVATION-SYNTAX \
  --output-definition "${OUTPUT}/observation-k-kompiled" \
  >"${OUTPUT}/logs/observation-k.stdout" 2>"${OUTPUT}/logs/observation-k.stderr"

javap -classpath "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" -p org.kframework.kompile.Kompile >"${OUTPUT}/api/Kompile.signatures"
grep -Fq 'Function<org.kframework.definition.Definition, org.kframework.definition.Definition>, java.util.function.Function<org.kframework.definition.Definition, org.kframework.definition.Definition>' "${OUTPUT}/api/Kompile.signatures"
! rg -n '"(bump|state|observation|0|1|P3-COUPLED|<observation>)"' "${DRIVER}"
for literal in '"bump"' '"<state>"' '"observation"' '"0"' '"1"'; do grep -Fq "${literal}" "${OBS_K}"; done

readonly NONFIRING="${TASK}/fixtures/nonfiring.exp"

R2_G_06_BUILD_ROOT="${BUILD_ROOT}/configuration-oracle" \
R2_G_06_MODE=positive-a \
R2_G_06_RECORD="${OUTPUT}/records/configuration-only.json" \
R2_G_06_K_DEFINITION="${OUTPUT}/configuration-k-kompiled" \
  "${CONFIG_TASK}/run-driver.sh" "${P3}" --backend haskell --emit-json \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT}/configuration-only" \
    >"${OUTPUT}/logs/configuration-only.stdout" 2>"${OUTPUT}/logs/configuration-only.stderr"

run_positive() {
  local mode="$1" output="$2"
  R2_G_07_BUILD_ROOT="${BUILD_ROOT}" R2_G_07_MODE="${mode}" \
  R2_G_07_RECORD="${OUTPUT}/records/${output}.json" \
  R2_G_07_CONFIGURATION_K_DEFINITION="${OUTPUT}/configuration-k-kompiled" \
  R2_G_07_OBSERVATION_K_DEFINITION="${OUTPUT}/observation-k-kompiled" \
    "${TASK}/run-driver.sh" "${P3}" --backend haskell --emit-json \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
}
run_positive positive-a observation-a
run_positive positive-b observation-b

kompile "${TASK}/fixtures/source-oracle.k" --backend haskell --emit-json \
  --main-module R2-G-07-SOURCE-ORACLE --syntax-module R2-G-07-SOURCE-ORACLE-SYNTAX \
  --output-definition "${OUTPUT}/source-oracle" \
  >"${OUTPUT}/logs/source-oracle.stdout" 2>"${OUTPUT}/logs/source-oracle.stderr"

run_negative() {
  local mode="$1" output="$2"
  set +e
  R2_G_07_BUILD_ROOT="${BUILD_ROOT}" R2_G_07_MODE="${mode}" \
  R2_G_07_RECORD="${OUTPUT}/records/${output}.json" \
  R2_G_07_CONFIGURATION_K_DEFINITION="${OUTPUT}/configuration-k-kompiled" \
  R2_G_07_OBSERVATION_K_DEFINITION="${OUTPUT}/observation-k-kompiled" \
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
run_negative missing-metadata negative-missing-metadata
run_negative ambiguous-metadata negative-ambiguous-metadata
run_negative conflict-existing negative-conflict
run_negative false-already-present negative-false-already
run_negative unsupported-shape negative-unsupported-shape

for output in configuration-only observation-a observation-b source-oracle; do
  for program in firing nonfiring; do
    input="${FIRING}"
    [[ "${program}" == nonfiring ]] && input="${NONFIRING}"
    krun "${input}" --definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/runtime/${output}-${program}.out" 2>"${OUTPUT}/runtime/${output}-${program}.err"
    python3 "${TASK}/project_runtime.py" \
      "${OUTPUT}/runtime/${output}-${program}.out" \
      "${OUTPUT}/projections/${output}-${program}.json"
  done
done

for output in observation-a observation-b; do
  python3 "${NORMALIZER}" \
    "${OUTPUT}/${output}/definition.kore" "${OUTPUT}/projections/${output}-definition.kore"
  python3 "${TASK}/project_rule_kore.py" --label bump-state \
    "${OUTPUT}/${output}/definition.kore" "${OUTPUT}/projections/${output}-bump-state.kore"
done
cmp "${OUTPUT}/projections/observation-a-definition.kore" "${OUTPUT}/projections/observation-b-definition.kore"
cmp "${OUTPUT}/projections/observation-a-bump-state.kore" "${OUTPUT}/projections/observation-b-bump-state.kore"
grep -Fq "Lbl'-LT-'observation'-GT-'" "${OUTPUT}/projections/observation-a-bump-state.kore"
for artifact in syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT}/observation-a/${artifact}" "${OUTPUT}/observation-b/${artifact}"
  cmp "${OUTPUT}/configuration-only/${artifact}" "${OUTPUT}/observation-a/${artifact}"
done

for program in firing nonfiring; do
  cmp "${OUTPUT}/runtime/observation-a-${program}.out" "${OUTPUT}/runtime/observation-b-${program}.out"
  cmp "${OUTPUT}/projections/observation-a-${program}.json" "${OUTPUT}/projections/source-oracle-${program}.json"
  python3 "${TASK}/project_runtime.py" --erase-observation \
    "${OUTPUT}/runtime/observation-a-${program}.out" "${OUTPUT}/projections/observation-a-${program}-erased.json"
  python3 "${TASK}/project_runtime.py" --erase-observation \
    "${OUTPUT}/runtime/configuration-only-${program}.out" "${OUTPUT}/projections/configuration-only-${program}-erased.json"
  cmp "${OUTPUT}/projections/configuration-only-${program}-erased.json" "${OUTPUT}/projections/observation-a-${program}-erased.json"
done
jq -e '. == {k:"1",observation:"1",state:"2"}' "${OUTPUT}/projections/observation-a-firing.json" >/dev/null
jq -e '. == {k:"1",observation:"0",state:"1"}' "${OUTPUT}/projections/observation-a-nonfiring.json" >/dev/null

for record in observation-a observation-b; do
  jq -e '
    .status=="accepted" and .configurationHookInvocations==1
    and .configurationKInvocationsPass1==1 and .configurationKInvocationsPass2==1
    and .configurationCandidateCountPass1==1 and .configurationStatusPass1=="apply"
    and .configurationCandidateCountPass2==1 and .configurationStatusPass2=="already-present"
    and .configurationApplicationCount==1 and .configurationChangedCount==1
    and .configurationAlreadyPresentValidatedCount==1 and .configurationSecondSameReference
    and .postCfAdapterInvocations==1 and .ruleKInvocationsPass1==1 and .ruleKInvocationsPass2==1
    and .ruleCandidateCountPass1==1 and .ruleStatusPass1=="apply"
    and .ruleCandidateCountPass2==1 and .ruleStatusPass2=="already-present"
    and .ruleValidatedOperationCount==1 and .ruleApplicationCount==1 and .ruleChangedRuleCount==1
    and .ruleAlreadyPresentValidatedCount==1 and .ruleSecondSameReference
    and .ruleIdentityPreserved and .ruleProvenancePreserved and .ruleAttributesPreserved
    and .ruleConditionsPreserved and .ruleOriginalNodesPreserved
    and .ruleBeforeDefinition != .ruleAfterDefinition
    and .ruleTargetContentBefore != .ruleTargetContentAfter
    and .ruleTargetBodyBefore != .ruleTargetBodyAfter
    and .ruleTransformedDefinitionReturned and .ruleSecondPassSameReference
    and .configurationCfConstructed and .backendConstructed
  ' "${OUTPUT}/records/${record}.json" >/dev/null
done
jq -e --slurp '
  .[0].configurationRequestFingerprintPass1 == .[1].configurationRequestFingerprintPass1
  and .[0].configurationResponseFingerprintPass1 == .[1].configurationResponseFingerprintPass1
  and .[0].configurationRequestFingerprintPass2 == .[1].configurationRequestFingerprintPass2
  and .[0].configurationResponseFingerprintPass2 == .[1].configurationResponseFingerprintPass2
  and .[0].ruleRequestFingerprintPass1 == .[1].ruleRequestFingerprintPass1
  and .[0].ruleResponseFingerprintPass1 == .[1].ruleResponseFingerprintPass1
  and .[0].ruleRequestFingerprintPass2 == .[1].ruleRequestFingerprintPass2
  and .[0].ruleResponseFingerprintPass2 == .[1].ruleResponseFingerprintPass2
  and .[0].ruleOperationCanonicalPass1 == .[1].ruleOperationCanonicalPass1
  and .[0].ruleOperationCanonicalPass2 == .[1].ruleOperationCanonicalPass2
' "${OUTPUT}/records/observation-a.json" "${OUTPUT}/records/observation-b.json" >/dev/null

declare -A classes=(
  [negative-stale]=stale-precondition [negative-zero]=k-selection
  [negative-duplicate]=k-selection [negative-path]=path-operation
  [negative-missing-metadata]=generated-metadata [negative-ambiguous-metadata]=generated-metadata
  [negative-conflict]=conflict [negative-false-already]=envelope
  [negative-unsupported-shape]=conservative-shape-rejection
)
for record in "${!classes[@]}"; do
  jq -e --arg class "${classes[$record]}" '
    .status=="rejected" and .classification==$class
    and .configurationHookInvocations==1 and .configurationApplicationCount==1
    and .postCfAdapterInvocations==1 and .ruleApplicationCount==0
    and (.ruleTransformedDefinitionReturned|not) and (.backendConstructed|not)
  ' "${OUTPUT}/records/${record}.json" >/dev/null
  for artifact in allRules.txt backend.txt compiled.bin compiled.json compiled.txt \
      definition.kore haskellDefinition.bin macros.kore syntaxDefinition.kore; do
    [[ ! -e "${OUTPUT}/${record}/${artifact}" ]]
  done
done
jq -e '.ruleCandidateCountPass1==0' "${OUTPUT}/records/negative-zero.json" >/dev/null
jq -e '.ruleCandidateCountPass1==2' "${OUTPUT}/records/negative-duplicate.json" >/dev/null
jq -e '.ruleInputMutationCount==1 and .ruleKInvocationsPass2==1' "${OUTPUT}/records/negative-conflict.json" >/dev/null
jq -e '.ruleInputMutationCount==1' "${OUTPUT}/records/negative-missing-metadata.json" "${OUTPUT}/records/negative-ambiguous-metadata.json" >/dev/null
jq -e '.ruleInputMutationCount==1 and .ruleKInvocationsPass2==1 and .ruleCandidateCountPass2==1' "${OUTPUT}/records/negative-unsupported-shape.json" >/dev/null

{
  sha256sum "${OBS_K}" "${DRIVER}" "${TASK}/replay.sh" "${TASK}/run-driver.sh"
  sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/"{DefinitionParsing,Kompile}.class
  sha256sum "${OUTPUT}"/records/*.json "${OUTPUT}"/runtime/*.out "${OUTPUT}"/projections/*.json
} >"${OUTPUT}/SHA256SUMS"

jq -n \
  --arg activation "${ACTIVATION}" --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kSource "${K_SOURCE}" --arg kStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kompile "${KOMPILE_BIN}" --arg frontendSha "${FRONTEND_SHA}" --arg hookPatchSha "${HOOK_PATCH_SHA}" \
  --arg configKSha "${CONFIG_K_SHA}" --arg configJavaSha "${CONFIG_JAVA_SHA}" \
  --arg configReplaySha "${CONFIG_REPLAY_SHA}" --arg configRunnerSha "${CONFIG_RUNNER_SHA}" \
  --arg configVerifySha "${CONFIG_VERIFY_SHA}" --arg configEvidenceSha "${CONFIG_EVIDENCE_SHA}" \
  --arg obsKSha "$(sha256sum "${OBS_K}"|awk '{print $1}')" --arg driverSha "$(sha256sum "${DRIVER}"|awk '{print $1}')" \
  --arg replaySha "$(sha256sum "${TASK}/replay.sh"|awk '{print $1}')" --arg runnerSha "$(sha256sum "${TASK}/run-driver.sh"|awk '{print $1}')" \
  --arg verifierSha "$(sha256sum "${TASK}/verify.sh"|awk '{print $1}')" \
  --arg runtimeSha "$(sha256sum "${TASK}/project_runtime.py"|awk '{print $1}')" \
  --arg ruleProjectorSha "$(sha256sum "${TASK}/project_rule_kore.py"|awk '{print $1}')" \
  --arg sourceOracleSha "$(sha256sum "${TASK}/fixtures/source-oracle.k"|awk '{print $1}')" \
  --arg nonfiringSha "$(sha256sum "${NONFIRING}"|awk '{print $1}')" \
  --arg p3Sha "${P3_SHA}" --arg firingSha "${FIRING_SHA}" --arg normalizerSha "${NORMALIZER_SHA}" \
  --argjson cycles "${CYCLES}" \
  --slurpfile a "${OUTPUT}/records/observation-a.json" --slurpfile b "${OUTPUT}/records/observation-b.json" \
  --slurpfile stale "${OUTPUT}/records/negative-stale.json" --slurpfile zero "${OUTPUT}/records/negative-zero.json" \
  --slurpfile duplicate "${OUTPUT}/records/negative-duplicate.json" --slurpfile path "${OUTPUT}/records/negative-path.json" \
  --slurpfile missing "${OUTPUT}/records/negative-missing-metadata.json" --slurpfile ambiguous "${OUTPUT}/records/negative-ambiguous-metadata.json" \
  --slurpfile conflict "${OUTPUT}/records/negative-conflict.json" --slurpfile falseAlready "${OUTPUT}/records/negative-false-already.json" \
  --slurpfile shape "${OUTPUT}/records/negative-unsupported-shape.json" \
  --slurpfile firing "${OUTPUT}/projections/observation-a-firing.json" \
  --slurpfile nonfiring "${OUTPUT}/projections/observation-a-nonfiring.json" \
  '{schemaVersion:1,task:"R2-G-07-single-rule-observation",verdict:"pass",contract:"KRuleObservation-v1",configurationContract:"KConfigurationAugmentation-v1",fullCycleCount:$cycles,activationRevision:$activation,
    pin:{kRelease:$kRelease,kCommit:$kCommit,kSource:$kSource,kSourceStatus:$kStatus,resolvedKompile:$kompile,frontendJarSha256:$frontendSha,hookPatchSha256:$hookPatchSha,configurationSpine:{kSemantics:$configKSha,javaHost:$configJavaSha,replay:$configReplaySha,runner:$configRunnerSha,verifier:$configVerifySha,evidence:$configEvidenceSha},environment:{LC_ALL:"C",LANG:"C",TZ:"UTC"}},
    taskSourceSha256:{kSemantics:$obsKSha,javaHost:$driverSha,replay:$replaySha,runner:$runnerSha,verifier:$verifierSha,runtimeProjector:$runtimeSha,ruleProjector:$ruleProjectorSha,sourceOracle:$sourceOracleSha,p3Definition:$p3Sha,firingProgram:$firingSha,nonfiringProgram:$nonfiringSha,identityNormalizer:$normalizerSha},
    ownership:{k:["coupled bump/state structural recognition","apply/already/conflict classification","target preconditions and cardinality","parent path","generated cell name","before/after values","status"],java:["complete typed rule/metadata projection","canonical result parsing and fingerprints","generic path and generated-production resolution","typed cell-fragment construction","immutable rule reconstruction and graph validation"]},
    composition:{configuration:($a[0]|{configurationHookInvocations,configurationKInvocationsPass1,configurationKInvocationsPass2,configurationRequestFingerprintPass1,configurationResponseFingerprintPass1,configurationCandidateCountPass1,configurationStatusPass1,configurationRequestFingerprintPass2,configurationResponseFingerprintPass2,configurationCandidateCountPass2,configurationStatusPass2,configurationApplicationCount,configurationChangedCount,configurationAlreadyPresentValidatedCount,configurationSecondSameReference}),rule:($a[0]|{postCfAdapterInvocations,ruleKInvocationsPass1,ruleKInvocationsPass2,ruleRequestFingerprintPass1,ruleResponseFingerprintPass1,ruleCandidateCountPass1,ruleStatusPass1,ruleRequestFingerprintPass2,ruleResponseFingerprintPass2,ruleCandidateCountPass2,ruleStatusPass2,ruleTargetLineage,ruleTargetContentBefore,ruleTargetContentAfter,ruleTargetBodyBefore,ruleTargetBodyAfter,ruleBeforeDefinition,ruleAfterDefinition,ruleOperationCanonicalPass1,ruleOperationCanonicalPass2,ruleResultCanonicalFingerprintPass1,ruleResultCanonicalFingerprintPass2,ruleValidatedOperationCount,ruleApplicationCount,ruleChangedRuleCount,ruleAlreadyPresentValidatedCount,ruleSecondSameReference,ruleIdentityPreserved,ruleProvenancePreserved,ruleAttributesPreserved,ruleConditionsPreserved,ruleOriginalNodesPreserved,generatedCellName,generatedCellLabel,generatedCellSort,generatedCellBodySort,generatedCellProductionFingerprint,generatedCellMetadataFingerprint,backendConstructed}),repeatStable:true},
    oracles:{firingRuntime:$firing[0],nonfiringRuntime:$nonfiring[0],firingErasureEqualsConfigurationOnly:true,nonfiringErasureEqualsConfigurationOnly:true,ordinarySourceRuntimeEqual:true,normalizedDefinitionStable:true,focusedRuleStable:true,syntaxAndMacrosEqualConfigurationOnly:true,noncanonicalAndMalformedResultsRejected:true},
    negatives:{stale:($stale[0]|{classification,ruleCandidateCountPass1,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),zero:($zero[0]|{classification,ruleCandidateCountPass1,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),duplicate:($duplicate[0]|{classification,ruleCandidateCountPass1,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),path:($path[0]|{classification,ruleCandidateCountPass1,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),missingMetadata:($missing[0]|{classification,ruleCandidateCountPass1,ruleInputMutationCount,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),ambiguousMetadata:($ambiguous[0]|{classification,ruleCandidateCountPass1,ruleInputMutationCount,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),conflict:($conflict[0]|{classification,ruleCandidateCountPass1,ruleCandidateCountPass2,ruleInputMutationCount,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),falseAlready:($falseAlready[0]|{classification,ruleCandidateCountPass1,ruleAlreadyPresentValidatedCount,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false),unsupportedShape:($shape[0]|{classification,ruleCandidateCountPass1,ruleCandidateCountPass2,ruleInputMutationCount,ruleApplicationCount,ruleTransformedDefinitionReturned,backendConstructed}|.backendArtifactsEmitted=false)},
    limitations:["one structurally selected source rule","one generated-cell update from 0 to 1","conservativity proven only for the firing and non-firing concrete programs","no event payload, trace, list state, monitor, matcher, multiple rules, symbolic path, C1, or C2"],packetAmbiguity:"none requiring a split",recommendedNextPacket:"first trace-backed RuleApplied packet for this one selected transition, retaining the same conservative erasure oracle and without matcher expansion"}' >"${OUTPUT}/results.json"

cat >"${OUTPUT}/report.md" <<'EOF'
# R2-G-07 accepted evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without pre-existing acceptance output:

```sh
bun run r2:g:observation
```

The replay composes the source-bound accepted pre-CF configuration hook with
`KRuleObservation-v1` at `OfficialDefinitionAdapter v1`, then continues through
unchanged official lowering and the pinned Haskell backend. It pins every
consumed source/normalizer, runs fresh configuration-only and ordinary-source
oracles, a complete repeat, firing and non-firing programs, malformed-result
parser tests, and every semantic negative. Raw compiler outputs remain below
the ignored `spine/rule-observation/build/` tree.

## Result

- The accepted configuration contract retained its `apply` then
  `already-present` result, one application, and same-reference validation.
- At the post-CF seam, K structurally recognized the coupled `bump`/state update
  rather than selecting by label. K authored the sole target and all
  preconditions, cardinality, root cell-bag path, generated cell name, `0 => 1`
  values, and `apply` status.
- The generic host resolved one official generated cell production and body
  sort, reused the official leaf-cell marker envelope, appended one typed cell
  update, and changed exactly one primary-source rule. Rule lineage, label,
  source/location, priority-capable attributes, conditions, and every original
  body node were preserved.
- Reprojection returned `already-present` with candidate count one. Independent
  host validation found exactly one equal update and returned the same
  instrumented definition reference without a second application.
- The exact-result parser rejected noncanonical integers/strings, unknown
  constructors, residual output, and multiple output.
- The firing program ended at `<k> 1`, `<state> 2`, `<observation> 1`; the
  non-firing integer ended at `<k> 1`, `<state> 1`, `<observation> 0`. Both
  erased runtimes equal the accepted configuration-only oracle, and both full
  runtimes equal an independently compiled ordinary-source oracle.
- The fresh repeat had stable request/result fingerprints, focused and full
  normalized definition Kore, syntax, macros, and both runtimes. Syntax and
  macros remained byte-equal to the configuration-only oracle.
- Stale content, zero/duplicate targets, invalid paths, missing/ambiguous
  generated metadata, conflicting updates, false `already-present`, and an
  actually mutated rule body with no safe cell-bag insertion point all rejected
  with zero rule applications and no lowering/backend artifacts.

## Boundary retained

K owns fixture recognition and semantic choices. Java transports complete typed
rules and descriptors, validates K's exact result, resolves only declared
generic metadata/paths, and reconstructs immutable official objects. Java
contains none of the selected fixture name, cell name, module/label, or update
value literals.

This proves conservativity only for the two exercised concrete programs and one
selected rule/update. It introduces no event payload, trace/list state, monitor,
matcher, multi-rule facility, symbolic path, C1, or C2 behavior. There was no
packet ambiguity requiring a split.

The recommended next packet is the first trace-backed `RuleApplied` packet for
this same single transition, retaining the conservative erasure oracle without
expanding into matching.
EOF

if [[ -f "${EVIDENCE}/results.json" ]]; then
  cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"
  cmp "${EVIDENCE}/report.md" "${OUTPUT}/report.md"
fi
printf 'R2-G-07 conservative single-rule observation replay: pass\n'
