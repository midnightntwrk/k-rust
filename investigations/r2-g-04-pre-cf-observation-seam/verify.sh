#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION_REVISION="f4dcd7e6684e491195104145555990dd192c5c8a"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_FRONTEND_JAR_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly WORKSPACE_FAMILY="$(dirname "${REPO_ROOT}")"
readonly K_SOURCE="${WORKSPACE_FAMILY}/inspirations/runtimeverification/k"
readonly TASK_DIR="${REPO_ROOT}/investigations/r2-g-04-pre-cf-observation-seam"
readonly OUTPUT_ROOT="${1:-${TASK_DIR}/build/verify}"
readonly SOURCE_MANIFEST="${TASK_DIR}/evidence/source-manifest.sha256"
readonly POSITIVE_SOURCE="${TASK_DIR}/src/org/kframework/kink/precf/LifecycleSurfaceProbe.java"
readonly NEGATIVE_SOURCE="${TASK_DIR}/src-negative/org/kframework/kink/precf/PrivateMidpointOverrideProbe.java"
readonly PROJECT_RUNTIME="${TASK_DIR}/project_runtime.py"
readonly CANDIDATE_MATRIX="${TASK_DIR}/candidate-matrix.json"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly K_FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"

for tool in bun cmp git grep java javac javap jq kompile krun python3 sha256sum; do
  command -v "${tool}" >/dev/null
done
git merge-base --is-ancestor "${ACTIVATION_REVISION}" HEAD
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ -f "${K_FRONTEND_JAR}" ]]
[[ "$(sha256sum "${K_FRONTEND_JAR}" | awk '{print $1}')" == "${K_FRONTEND_JAR_SHA}" ]]
[[ ! -e "${OUTPUT_ROOT}" ]]

export LC_ALL=C
export LANG=C
export TZ=UTC

mkdir -p \
  "${OUTPUT_ROOT}/api" \
  "${OUTPUT_ROOT}/classes" \
  "${OUTPUT_ROOT}/logs" \
  "${OUTPUT_ROOT}/negative" \
  "${OUTPUT_ROOT}/projections" \
  "${OUTPUT_ROOT}/runtime"

(
  cd "${K_SOURCE}"
  sha256sum -c "${SOURCE_MANIFEST}"
) >"${OUTPUT_ROOT}/logs/source-manifest.stdout"

javap -classpath "${K_JAVA}/*" -p org.kframework.kompile.DefinitionParsing \
  >"${OUTPUT_ROOT}/api/DefinitionParsing.javap"
javap -classpath "${K_JAVA}/*" -p org.kframework.kompile.Kompile \
  >"${OUTPUT_ROOT}/api/Kompile.javap"
javap -classpath "${K_JAVA}/*" -c -p org.kframework.kompile.Kompile \
  >"${OUTPUT_ROOT}/api/Kompile.bytecode"
javap -classpath "${K_JAVA}/*" -p org.kframework.compile.GenerateSentencesFromConfigDecl \
  >"${OUTPUT_ROOT}/api/GenerateSentencesFromConfigDecl.javap"
javap -classpath "${K_JAVA}/*" -p org.kframework.definition.Configuration \
  >"${OUTPUT_ROOT}/api/Configuration.javap"

grep -Fq 'public org.kframework.definition.Definition parseDefinitionAndResolveBubbles(' \
  "${OUTPUT_ROOT}/api/DefinitionParsing.javap"
grep -Fq 'protected org.kframework.definition.Definition resolveConfigBubbles(org.kframework.definition.Definition, org.kframework.definition.Module);' \
  "${OUTPUT_ROOT}/api/DefinitionParsing.javap"
grep -Fq 'private org.kframework.definition.Definition resolveConfigBubbles(org.kframework.definition.Definition);' \
  "${OUTPUT_ROOT}/api/DefinitionParsing.javap"
grep -Fq 'private final org.kframework.kompile.DefinitionParsing definitionParsing;' \
  "${OUTPUT_ROOT}/api/Kompile.javap"
grep -Fq 'public org.kframework.kompile.CompiledDefinition run(' \
  "${OUTPUT_ROOT}/api/Kompile.javap"
grep -Eq 'new +#[0-9]+ +// class org/kframework/kompile/DefinitionParsing' \
  "${OUTPUT_ROOT}/api/Kompile.bytecode"
grep -Fq 'public static scala.collection.Set<org.kframework.definition.Sentence> gen(' \
  "${OUTPUT_ROOT}/api/GenerateSentencesFromConfigDecl.javap"
for accessor in body ensures att location source; do
  grep -Eq "public .* ${accessor}\\(\\);" \
    "${OUTPUT_ROOT}/api/Configuration.javap"
done

javac -encoding UTF-8 -cp "${K_JAVA}/*" \
  -d "${OUTPUT_ROOT}/classes" "${POSITIVE_SOURCE}"
java -cp "${OUTPUT_ROOT}/classes:${K_JAVA}/*" \
  org.kframework.kink.precf.LifecycleSurfaceProbe identity \
  >"${OUTPUT_ROOT}/api/surface-identity.json"
java -cp "${OUTPUT_ROOT}/classes:${K_JAVA}/*" \
  org.kframework.kink.precf.LifecycleSurfaceProbe augmentation \
  >"${OUTPUT_ROOT}/api/surface-augmentation.json"
cmp "${TASK_DIR}/evidence/surface-identity.json" \
  "${OUTPUT_ROOT}/api/surface-identity.json"
cmp "${TASK_DIR}/evidence/surface-augmentation.json" \
  "${OUTPUT_ROOT}/api/surface-augmentation.json"

set +e
javac -encoding UTF-8 -cp "${K_JAVA}/*" \
  -d "${OUTPUT_ROOT}/negative" "${NEGATIVE_SOURCE}" \
  2>"${OUTPUT_ROOT}/negative/private-midpoint-override.raw.stderr"
private_override_exit=$?
set -e
[[ "${private_override_exit}" -eq 1 ]]
sed "s#${REPO_ROOT}/##g" \
  "${OUTPUT_ROOT}/negative/private-midpoint-override.raw.stderr" \
  >"${OUTPUT_ROOT}/negative/private-midpoint-override.stderr"
cmp "${TASK_DIR}/evidence/private-midpoint-override.stderr" \
  "${OUTPUT_ROOT}/negative/private-midpoint-override.stderr"

# Localization control 1: the accepted post-CF identity adapter remains healthy.
bash "${REPO_ROOT}/spine/definition-transport/replay.sh" \
  "${OUTPUT_ROOT}/post-cf" \
  >"${OUTPUT_ROOT}/logs/post-cf.stdout" \
  2>"${OUTPUT_ROOT}/logs/post-cf.stderr"
jq -e '
  .verdict == "pass"
  and .identity.p3.status == "accepted"
  and .identity.p3.sameDefinitionReference
' "${OUTPUT_ROOT}/post-cf/results.json" >/dev/null

# Localization control 2: ordinary source still lets official CF create the inert cell.
kompile "${REPO_ROOT}/investigations/w1-egress/fixtures/p3-observation.k" \
  --backend haskell --emit-json \
  --main-module W1-P3-OBSERVATION \
  --syntax-module W1-P3-OBSERVATION-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/source-observation" \
  >"${OUTPUT_ROOT}/logs/source-observation.stdout" \
  2>"${OUTPUT_ROOT}/logs/source-observation.stderr"
krun "${REPO_ROOT}/investigations/w1-egress/fixtures/program.exp" \
  --definition "${OUTPUT_ROOT}/source-observation" \
  >"${OUTPUT_ROOT}/runtime/source-observation.out" \
  2>"${OUTPUT_ROOT}/runtime/source-observation.err"
python3 "${PROJECT_RUNTIME}" \
  "${OUTPUT_ROOT}/post-cf/runtime/p3-baseline.out" \
  "${OUTPUT_ROOT}/projections/post-cf-baseline-runtime.json"
python3 "${PROJECT_RUNTIME}" \
  "${OUTPUT_ROOT}/runtime/source-observation.out" \
  "${OUTPUT_ROOT}/projections/source-observation-runtime.json"
jq -e '. == {k:"1", state:"2"}' \
  "${OUTPUT_ROOT}/projections/post-cf-baseline-runtime.json" >/dev/null
jq -e '. == {k:"1", observation:"0", state:"2"}' \
  "${OUTPUT_ROOT}/projections/source-observation-runtime.json" >/dev/null
jq -S '{k,state}' "${OUTPUT_ROOT}/projections/post-cf-baseline-runtime.json" \
  >"${OUTPUT_ROOT}/projections/post-cf-erased-runtime.json"
jq -S '{k,state}' "${OUTPUT_ROOT}/projections/source-observation-runtime.json" \
  >"${OUTPUT_ROOT}/projections/source-observation-erased-runtime.json"
cmp "${OUTPUT_ROOT}/projections/post-cf-erased-runtime.json" \
  "${OUTPUT_ROOT}/projections/source-observation-erased-runtime.json"
grep -Fq 'LblinitObservationCell' \
  "${OUTPUT_ROOT}/source-observation/definition.kore"
grep -Fq "Lbl'-LT-'observation'-GT-'" \
  "${OUTPUT_ROOT}/source-observation/definition.kore"

jq -n \
  --arg activationRevision "${ACTIVATION_REVISION}" \
  --arg kCommit "${K_COMMIT}" \
  --arg kRelease "${K_RELEASE}" \
  --arg resolvedKompile "${KOMPILE_BIN}" \
  --arg resolvedKrun "$(readlink -f "$(command -v krun)")" \
  --arg resolvedJava "$(readlink -f "$(command -v java)")" \
  --arg resolvedJavac "$(readlink -f "$(command -v javac)")" \
  --arg resolvedJavap "$(readlink -f "$(command -v javap)")" \
  --arg resolvedBun "$(readlink -f "$(command -v bun)")" \
  --arg kSource "${K_SOURCE}" \
  --arg kSourceStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kFrontendJar "${K_FRONTEND_JAR}" \
  --arg kFrontendJarSha "${K_FRONTEND_JAR_SHA}" \
  --arg definitionParsingSha "$(awk '$2 ~ /DefinitionParsing.java$/ {print $1}' "${SOURCE_MANIFEST}")" \
  --arg generatorSha "$(awk '$2 ~ /GenerateSentencesFromConfigDecl.java$/ {print $1}' "${SOURCE_MANIFEST}")" \
  --arg kompileSourceSha "$(awk '$2 ~ /Kompile.java$/ {print $1}' "${SOURCE_MANIFEST}")" \
  --arg frontendSourceSha "$(awk '$2 ~ /KompileFrontEnd.java$/ {print $1}' "${SOURCE_MANIFEST}")" \
  --arg positiveProbeSha "$(sha256sum "${POSITIVE_SOURCE}" | awk '{print $1}')" \
  --arg negativeProbeSha "$(sha256sum "${NEGATIVE_SOURCE}" | awk '{print $1}')" \
  --arg runtimeProjectorSha "$(sha256sum "${PROJECT_RUNTIME}" | awk '{print $1}')" \
  --arg matrixSha "$(sha256sum "${CANDIDATE_MATRIX}" | awk '{print $1}')" \
  --arg definitionParsingJavapSha "$(sha256sum "${OUTPUT_ROOT}/api/DefinitionParsing.javap" | awk '{print $1}')" \
  --arg kompileJavapSha "$(sha256sum "${OUTPUT_ROOT}/api/Kompile.javap" | awk '{print $1}')" \
  --arg kompileConstructionSha "$(sha256sum "${OUTPUT_ROOT}/api/Kompile.bytecode" | awk '{print $1}')" \
  --arg generatorJavapSha "$(sha256sum "${OUTPUT_ROOT}/api/GenerateSentencesFromConfigDecl.javap" | awk '{print $1}')" \
  --arg configurationJavapSha "$(sha256sum "${OUTPUT_ROOT}/api/Configuration.javap" | awk '{print $1}')" \
  --arg privateOverrideExit "${private_override_exit}" \
  --arg privateFailureSha "$(sha256sum "${OUTPUT_ROOT}/negative/private-midpoint-override.stderr" | awk '{print $1}')" \
  --slurpfile candidates "${CANDIDATE_MATRIX}" \
  --slurpfile identitySurface "${OUTPUT_ROOT}/api/surface-identity.json" \
  --slurpfile augmentationSurface "${OUTPUT_ROOT}/api/surface-augmentation.json" \
  --slurpfile postCf "${OUTPUT_ROOT}/post-cf/results.json" \
  --slurpfile baselineRuntime "${OUTPUT_ROOT}/projections/post-cf-baseline-runtime.json" \
  --slurpfile observationRuntime "${OUTPUT_ROOT}/projections/source-observation-runtime.json" \
  '{
    schemaVersion: 1,
    task: "R2-G-04-pre-cf-observation-seam",
    verdict: "pass",
    classification: "pin-private-seam-needs-hook",
    fullProbeCycleCount: 3,
    activationRevision: $activationRevision,
    pin: {
      kRelease: $kRelease,
      kCommit: $kCommit,
      resolvedKompile: $resolvedKompile,
      resolvedKrun: $resolvedKrun,
      resolvedJava: $resolvedJava,
      resolvedJavac: $resolvedJavac,
      resolvedJavap: $resolvedJavap,
      resolvedBun: $resolvedBun,
      kSource: $kSource,
      kSourceStatus: $kSourceStatus,
      kFrontendJar: $kFrontendJar,
      kFrontendJarSha256: $kFrontendJarSha,
      environment: {LC_ALL:"C", LANG:"C", TZ:"UTC"}
    },
    officialSourceSha256: {
      definitionParsing: $definitionParsingSha,
      generateSentencesFromConfigDecl: $generatorSha,
      kompile: $kompileSourceSha,
      kompileFrontEnd: $frontendSourceSha
    },
    probeSourceSha256: {
      lifecycleSurface: $positiveProbeSha,
      privateMidpointOverride: $negativeProbeSha,
      runtimeProjector: $runtimeProjectorSha,
      candidateMatrix: $matrixSha
    },
    bytecodeProbeSha256: {
      definitionParsing: $definitionParsingJavapSha,
      kompile: $kompileJavapSha,
      kompileConstruction: $kompileConstructionSha,
      generateSentencesFromConfigDecl: $generatorJavapSha,
      configuration: $configurationJavapSha
    },
    lifecycle: {
      outerEntry: "public parseDefinitionAndResolveBubbles",
      publicParseOutput: "post-CF Definition after non-configuration bubble resolution",
      protectedWrapper: "resolveConfigBubbles(Definition,Module): Bubble input -> post-CF output",
      typedConversion: "private resolveConfigBubbles(Definition), lines 433-557 at the pin",
      typedMidpoint: "defWithParsedConfigs after lines 489-493",
      cellChecks: "private checkConfigCells at line 495",
      generation: "public GenerateSentencesFromConfigDecl.gen called at lines 535-540",
      nonConfigParsing: "private resolveNonConfigBubbles called after config resolution",
      kompilePipeline: "public Function<Definition,Definition> runs only after parseDefinition returns",
      construction: "KompileFrontEnd constructs Kompile; Kompile directly constructs private final DefinitionParsing"
    },
    strongestCandidate: {
      id: "definition-parsing-subclass",
      identitySurface: $identitySurface[0],
      augmentationSurface: $augmentationSurface[0],
      privateOverrideCompileExit: ($privateOverrideExit | tonumber),
      privateOverrideFailureSha256: $privateFailureSha,
      exactBlocker: "the only overridable config method encloses the private parse/check/generate operation, so no subclass callback observes typed Configuration before generation"
    },
    candidates: $candidates[0],
    localizationControls: {
      acceptedPostCfIdentity: {
        verdict: $postCf[0].verdict,
        p3Status: $postCf[0].identity.p3.status,
        sameDefinitionReference: $postCf[0].identity.p3.sameDefinitionReference
      },
      ordinarySourceObservation: {
        verdict: "pass-fallback-only",
        baselineRuntime: $baselineRuntime[0],
        observationRuntime: $observationRuntime[0],
        erasedRuntimeEqual: true,
        officialObservationCellGenerated: true
      }
    },
    minimumHook: {
      signature: "UnaryOperator<Configuration> transformConfiguration",
      placement: "after Bubble-to-Configuration conversion and before checkConfigCells and GenerateSentencesFromConfigDecl.gen",
      defaultBehavior: "identity",
      validation: "reject null, wrong sentence kind, lost provenance, and transformer exceptions before CF output is constructed",
      order: [
        "default configuration insertion",
        "MAP import insertion",
        "configuration bubble parsing and sort inference",
        "transformConfiguration",
        "cell checks over transformed Configuration",
        "GenerateSentencesFromConfigDecl.gen",
        "non-configuration bubble parsing",
        "pre-compilation checks",
        "OfficialDefinitionAdapter v1",
        "KoreBackend.steps and backend"
      ]
    },
    forbiddenMechanisms: {
      avoided: [
        "official K modification or rebuild",
        "reflection as a production route",
        "private DefinitionParsing pipeline copy",
        "source or KAST JSON round-trip claimed as typed seam",
        "post-CF sentence reconstruction",
        "new configuration or observation patch contract"
      ],
      diagnosticOnly: ["Java reflection for installed modifier verification"],
      encountered: [
        "private typed parse/generate overload",
        "direct private-final DefinitionParsing construction",
        "source regeneration works only as fallback"
      ]
    },
    executedProbes: [
      "source revision and SHA-256 manifest",
      "installed jar SHA-256 and javap signatures",
      "protected subclass compile/link identity surface",
      "private midpoint override compile failure",
      "accepted post-CF R2-G-01 identity replay",
      "ordinary-source observation fallback compile and execution"
    ],
    limitations: [
      "negative seam classification; no typed augmentation was performed",
      "diagnostic reflection inspects modifiers but is not a proposed route",
      "source fallback regenerates provenance and is not typed identity",
      "no events, instrumentation, matcher, shared patch schema, C1, or C2 work"
    ],
    recommendedNextPacket: "add the minimal pin-local/upstream Configuration callback and replay identity plus one inert observation-cell augmentation before any event or matcher work"
  }' >"${OUTPUT_ROOT}/results.json"

cmp "${TASK_DIR}/results.json" "${OUTPUT_ROOT}/results.json"

printf 'R2-G-04 pre-CF seam verification: pass\n'
