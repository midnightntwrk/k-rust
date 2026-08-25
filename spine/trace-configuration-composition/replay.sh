#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="7c2e9c898bc48f20f5e639e13ab4e4c098a5f02d"
readonly PROTOTYPE="478ea271f7295e8eed4bafd6ea4fd13a5fbe1ffc"
readonly STARTING_REVISION="596b026301dc95c3854a6078f6bb5c99833d5505"
readonly R3_G_02_ACTIVATION="3d7877cf6ba3a5095d2f9b77531cfef90b5236ae"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly HOOK_PATCH_SHA="bf9c788c89a201e74c9a51df23fe544333c8bf9898a8a9973dc4163d86f3e543"
readonly PACKET_SHA="c6d9dd03f66e8c604e45d66f4278b9ddf4fc0f09946fe97447f2da7d866d602a"
readonly REPAIR_PACKET_SHA="a4e10a0711bbf35790cb8568de56f5c66c7e4eb286dc33e9b47dc25e66ff213e"
readonly AUDIT_CHECKPOINT_SHA="0d14ece850ba5c2d1f0a2d0acf7865a55e33835fc8b2279aaa38ee17cfd3a642"
readonly CHECKPOINT_SHA="ec4f920845a492604f0b1f25b6af18774377d19877410cfeff7cba2c89a4f84d"
readonly R2_PACKET_SHA="07ce6b4b3a99727d577272619b329e26c6a99ef254a9e1da4135ca4172989c21"
readonly R3_PACKET_SHA="e33595dad28d20bd473bb308ac99d685426754cd7da08fc2f72d2e02f5f51f95"
readonly ACCEPTED_CONFIG_K_SHA="8c913e9692b84504d9589cc0ba98d6b32d2bbad104359b591c7f0be858c8cd3e"
readonly ACCEPTED_CONFIG_JAVA_SHA="dc7f77c8bb615f760dea9946792f6dee8001e0d4a44842787b1c95332e3b942f"
readonly ACCEPTED_CONFIG_REPLAY_SHA="875a888ec7d7bde6dec54381c55f6b4a4adf7cb33cfa99c2b97ecac4b26bd681"
readonly ACCEPTED_CONFIG_RESULTS_SHA="71f97b6f601eb35c2a56ff68d0c3f5a44e705a7280ea87d93e7f52018a916b72"
readonly ACCEPTED_CONFIG_REPORT_SHA="ac19fb2d9f83d0bf2699daf9e6953b62fbe87c6c0d32c54acee49dc5ebe75295"
readonly ACCEPTED_CONFIG_SPINE_TREE="c47b8e1dd6efd99554cc0d735cdcf2bc0b9e1342"
readonly ACCEPTED_CONFIG_EVIDENCE_TREE="c6b80e45dea14fe70e7f4aafacab0989d81fb77e"
readonly ACCEPTED_TRACE_K_SHA="7f0ca5a574a38c206b2a681c5427324616a0dcace4a58b06f0cbc9c48ac6953b"
readonly ACCEPTED_TRACE_JAVA_SHA="44e21a8e6e5d34d64b8b77abf1dd30df386af2aa5116c32a09661e5cba9a989d"
readonly ACCEPTED_TRACE_REPLAY_SHA="7f0847a90c3751976f072404ecca303405bf14de032a1062aceb463182400e66"
readonly ACCEPTED_TRACE_RUNNER_SHA="b313a0701e05a21a95d2e225eda8ae452ab529a72100715855f49a25b567675f"
readonly ACCEPTED_TRACE_VERIFY_SHA="a0c477259644da9e6a8be09040409c5a76270d564128a7f7ff02094ef9539956"
readonly ACCEPTED_TRACE_RESULTS_SHA="8a007ed2cce00517fcb0462b4f4bf7107abcf935c95e3f8cf861b3e609945519"
readonly ACCEPTED_TRACE_REPORT_SHA="31d1909b1cc16eda0db57a36962189edeea6d2cc56449c3d590bc6baeeab8213"
readonly ACCEPTED_TRACE_SPINE_TREE="c9974719a307ad4ca890f9bd81255b74b4d87047"
readonly ACCEPTED_TRACE_EVIDENCE_TREE="9ff8f487e1e4ba21ff12004ab41d6857c252fe42"
readonly P3_SHA="941ae576a67090a88815974648ea1c552bb1bf033ca100fdb3a286c4da66c0f5"
readonly FIRING_SHA="46210dddc66714c3d8d226711510cf8421774214016c508c72a833a05370f6b5"
readonly NORMALIZER_SHA="de87f170a560303571f6bb3711f162a7afa3c3737448376cec87b6aca50129c1"
readonly FIXTURE_SHA="844ee00f096dbf576f674e0dd5f1eac2f062c6fcf357dd635d58f552379d08df"
readonly CONFIG_ORACLE_SHA="3e862710550a19044f573809275ba7ff2e837b72111e9a3298d3d0763555e2be"
readonly ORACLE_TEMPLATE_SHA="9f2100fc75985d90603c7f785422d39de2127a84a5ccff45db37ba4a7548cfac"
readonly NONFIRING_SHA="4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865"

readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/trace-configuration-composition"
readonly EVIDENCE="${REPO_ROOT}/evidence/r3-g-02-k-authored-trace-configuration"
readonly OUTPUT="${1:-${TASK}/build/acceptance}"
readonly FULL_CYCLES=3
readonly REPAIR_CYCLES="${R3_G_02A_REPAIR_CYCLE_COUNT:-1}"
readonly PORTABLE_SOURCE="repo://spine/trace-configuration-composition/fixtures/p3-trace.k"
readonly CONFIG_K="${TASK}/src/trace-configuration-augmentation.k"
readonly TRACE_K="${TASK}/src/rule-applied-trace.k"
readonly DRIVER="${TASK}/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java"
readonly CONFIG_DRIVER="${TASK}/src/java/org/kframework/kink/trace/TraceConfigurationAugmentation.java"
readonly FIXTURE="${TASK}/fixtures/p3-trace.k"
readonly CONFIG_ORACLE="${TASK}/fixtures/trace-configuration-oracle.k"
readonly ORACLE_TEMPLATE="${TASK}/fixtures/source-oracle-template.k"
readonly NONFIRING="${TASK}/fixtures/nonfiring.exp"
readonly P3="${REPO_ROOT}/p3/fixtures/coupled.k"
readonly FIRING="${REPO_ROOT}/p3/fixtures/program.exp"
readonly NORMALIZER="${REPO_ROOT}/investigations/w1-inprocess-adapter/normalize_identity_kore.py"
readonly HOOK_PATCH="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/upstream.patch"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"
readonly BUILD_ROOT="${OUTPUT}/host"

check_sha() { [[ "$(sha256sum "$2" | awk '{print $1}')" == "$1" ]]; }
for tool in bun cmp git java javac javap jq kompile krun patch python3 rg sha256sum; do command -v "${tool}" >/dev/null; done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
git merge-base --is-ancestor "${STARTING_REVISION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
check_sha "${FRONTEND_SHA}" "${FRONTEND_JAR}"
check_sha "${HOOK_PATCH_SHA}" "${HOOK_PATCH}"
check_sha "${PACKET_SHA}" "${REPO_ROOT}/tasks/wave-3/R3-G-02-k-authored-trace-configuration.md"
check_sha "${REPAIR_PACKET_SHA}" "${REPO_ROOT}/tasks/wave-3/R3-G-02A-exact-shell-and-failure-envelope.md"
check_sha "${AUDIT_CHECKPOINT_SHA}" "${REPO_ROOT}/draft/k-in-k-r3-g-02-audit-checkpoint-2026-08-19.md"
check_sha "${CHECKPOINT_SHA}" "${REPO_ROOT}/draft/k-in-k-r3-g-01a-acceptance-checkpoint-2026-08-19.md"
check_sha "${R2_PACKET_SHA}" "${REPO_ROOT}/tasks/wave-2/R2-G-06-k-authored-configuration-augmentation.md"
check_sha "${R3_PACKET_SHA}" "${REPO_ROOT}/tasks/wave-3/R3-G-01A-checkout-stable-source-evidence.md"
check_sha "${ACCEPTED_CONFIG_K_SHA}" "${REPO_ROOT}/spine/configuration-augmentation/src/configuration-augmentation.k"
check_sha "${ACCEPTED_CONFIG_JAVA_SHA}" "${REPO_ROOT}/spine/configuration-augmentation/src/java/org/kframework/kink/configuration/ConfigurationAugmentationDriver.java"
check_sha "${ACCEPTED_CONFIG_REPLAY_SHA}" "${REPO_ROOT}/spine/configuration-augmentation/replay.sh"
check_sha "${ACCEPTED_CONFIG_RESULTS_SHA}" "${REPO_ROOT}/evidence/r2-g-06-k-configuration-augmentation/results.json"
check_sha "${ACCEPTED_CONFIG_REPORT_SHA}" "${REPO_ROOT}/evidence/r2-g-06-k-configuration-augmentation/report.md"
[[ "$(git rev-parse HEAD:spine/configuration-augmentation)" == "${ACCEPTED_CONFIG_SPINE_TREE}" ]]
[[ "$(git rev-parse HEAD:evidence/r2-g-06-k-configuration-augmentation)" == "${ACCEPTED_CONFIG_EVIDENCE_TREE}" ]]
check_sha "${ACCEPTED_TRACE_K_SHA}" "${REPO_ROOT}/spine/rule-applied-trace/src/rule-applied-trace.k"
check_sha "${ACCEPTED_TRACE_JAVA_SHA}" "${REPO_ROOT}/spine/rule-applied-trace/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java"
check_sha "${ACCEPTED_TRACE_REPLAY_SHA}" "${REPO_ROOT}/spine/rule-applied-trace/replay.sh"
check_sha "${ACCEPTED_TRACE_RUNNER_SHA}" "${REPO_ROOT}/spine/rule-applied-trace/run-driver.sh"
check_sha "${ACCEPTED_TRACE_VERIFY_SHA}" "${REPO_ROOT}/spine/rule-applied-trace/verify.sh"
check_sha "${ACCEPTED_TRACE_RESULTS_SHA}" "${REPO_ROOT}/evidence/r3-g-01-single-rule-applied-trace/results.json"
check_sha "${ACCEPTED_TRACE_REPORT_SHA}" "${REPO_ROOT}/evidence/r3-g-01-single-rule-applied-trace/report.md"
[[ "$(git rev-parse HEAD:spine/rule-applied-trace)" == "${ACCEPTED_TRACE_SPINE_TREE}" ]]
[[ "$(git rev-parse HEAD:evidence/r3-g-01-single-rule-applied-trace)" == "${ACCEPTED_TRACE_EVIDENCE_TREE}" ]]
check_sha "${P3_SHA}" "${P3}"
check_sha "${FIRING_SHA}" "${FIRING}"
check_sha "${NORMALIZER_SHA}" "${NORMALIZER}"
check_sha "${FIXTURE_SHA}" "${FIXTURE}"
check_sha "${CONFIG_ORACLE_SHA}" "${CONFIG_ORACLE}"
check_sha "${ORACLE_TEMPLATE_SHA}" "${ORACLE_TEMPLATE}"
check_sha "${NONFIRING_SHA}" "${NONFIRING}"
cmp "${TRACE_K}" "${REPO_ROOT}/spine/rule-applied-trace/src/rule-applied-trace.k"
python3 - "${REPO_ROOT}/spine/rule-applied-trace/fixtures/p3-trace.k" "${FIXTURE}" <<'PY'
import sys
from pathlib import Path

accepted, task = (Path(value) for value in sys.argv[1:])
left = accepted.read_text(encoding="utf-8").splitlines()
right = task.read_text(encoding="utf-8").splitlines()
if len(left) != len(right) or left[26] != "      <trace> .List </trace>" or right[26] != "":
    raise SystemExit("task fixture did not preserve the exact blank-line delta")
if left[:26] != right[:26] or left[27:] != right[27:]:
    raise SystemExit("task fixture changed beyond the accepted line-27 delta")
PY
[[ "${REPAIR_CYCLES}" =~ ^[1-2]$ ]]
[[ ! -e "${OUTPUT}" ]]

export LC_ALL=C LANG=C TZ=UTC
mkdir -p "${OUTPUT}"/{logs,records,runtime,projections,api,generated} \
  "${BUILD_ROOT}/overlay/source/k-frontend/src/main/java/org/kframework/kompile" \
  "${BUILD_ROOT}/overlay/classes" "${BUILD_ROOT}/driver-classes"
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
javac -encoding UTF-8 -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" -d "${BUILD_ROOT}/driver-classes" \
  "${DRIVER}" "${CONFIG_DRIVER}" >"${OUTPUT}/logs/driver-javac.stdout" 2>"${OUTPUT}/logs/driver-javac.stderr"
java -cp "${BUILD_ROOT}/driver-classes:${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  org.kframework.kink.trace.RuleAppliedTraceDriver --parser-self-test \
  >"${OUTPUT}/logs/parser-self-test.stdout" 2>"${OUTPUT}/logs/parser-self-test.stderr"

kompile "${CONFIG_K}" --backend llvm --main-module KINK-TRACE-CONFIGURATION-AUGMENTATION \
  --syntax-module KINK-TRACE-CONFIGURATION-AUGMENTATION-SYNTAX \
  --output-definition "${OUTPUT}/configuration-k-kompiled" \
  >"${OUTPUT}/logs/configuration-k.stdout" 2>"${OUTPUT}/logs/configuration-k.stderr"
kompile "${TRACE_K}" --backend llvm --main-module KINK-RULE-TRACE \
  --syntax-module KINK-RULE-TRACE-SYNTAX --output-definition "${OUTPUT}/trace-k-kompiled" \
  >"${OUTPUT}/logs/trace-k.stdout" 2>"${OUTPUT}/logs/trace-k.stderr"
javap -classpath "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" -p org.kframework.kompile.Kompile \
  >"${OUTPUT}/api/Kompile.signatures"
grep -Fq 'Function<org.kframework.definition.Definition, org.kframework.definition.Definition>, java.util.function.Function<org.kframework.definition.Definition, org.kframework.definition.Definition>' "${OUTPUT}/api/Kompile.signatures"

readonly SEMANTIC_LITERAL_PATTERN='"(T|k|state|trace|\.List|List|<trace>|ListItem|_List_|bump-state|R3-G-01-P3-TRACE)"'
if rg -n "${SEMANTIC_LITERAL_PATTERN}" "${DRIVER}" "${CONFIG_DRIVER}"; then
  printf 'fixture semantic literal crossed into Java\n' >&2; exit 1
fi
readonly EVENT_LITERAL_PATTERN='"[^"\n]*(ruleApplied|ruleOrigin)[^"\n]*"'
if rg -n "${EVENT_LITERAL_PATTERN}" "${DRIVER}" "${CONFIG_DRIVER}"; then
  printf 'event-constructor literal crossed into Java\n' >&2; exit 1
fi
for prohibited in '"ruleApplied"' '"prefix-ruleApplied"' '"ruleApplied-suffix"' \
    '"ruleOrigin"' '"prefix-ruleOrigin"' '"ruleOrigin-suffix"'; do
  printf '%s\n' "${prohibited}" | rg -q "${EVENT_LITERAL_PATTERN}"
done
for literal in '"T"' '"k"' '"state"' '"trace"' '".List"' '"List"'; do grep -Fq "${literal}" "${CONFIG_K}"; done
for literal in '"bump"' '"<state>"' '"trace"' '"ruleApplied' '"ruleOrigin' '"_List_"' '"ListItem"'; do grep -Fq "${literal}" "${TRACE_K}"; done

identity_path="${PATH}"
while IFS= read -r tool_bin; do
  identity_path="${tool_bin}:${identity_path}"
done < <(sed -n "s/^PATH='\([^']*\/bin\)'.*/\1/p" "${KOMPILE_BIN}")
PATH="${K_ROOT}/bin:${identity_path}" \
LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${K_ROOT}/lib/kframework/native/linux64" \
java -Dfile.encoding=UTF-8 -Djava.awt.headless=true \
  -Xms64m -Xmx8192m -Xss32m -ea \
  -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  org.kframework.main.Main -kompile "${FIXTURE}" \
  --backend haskell --emit-json \
  --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
  --output-definition "${OUTPUT}/baseline" \
  >"${OUTPUT}/logs/baseline.stdout" 2>"${OUTPUT}/logs/baseline.stderr"
for artifact in compiled.bin definition.kore macros.kore syntaxDefinition.kore; do
  [[ -f "${OUTPUT}/baseline/${artifact}" ]]
done
jq -n \
  --arg definitionParsingClassSha "$(sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/DefinitionParsing.class"|awk '{print $1}')" \
  --arg kompileClassSha "$(sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/Kompile.class"|awk '{print $1}')" \
  '{mode:"identity-pre-cf-baseline",officialMain:true,
    configurationTransform:"Function.identity() through backward-compatible patched Kompile.run",
    postCfAdapterInvocations:0,backendConstructed:true,
    artifacts:{compiledBin:true,definitionKore:true,macrosKore:true,syntaxDefinitionKore:true},
    overlayClassSha256:{definitionParsing:$definitionParsingClassSha,kompile:$kompileClassSha}}' \
  >"${OUTPUT}/records/identity-baseline.json"
kompile "${P3}" --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT}/p3-oracle" \
  >"${OUTPUT}/logs/p3-oracle.stdout" 2>"${OUTPUT}/logs/p3-oracle.stderr"
kompile "${CONFIG_ORACLE}" --backend haskell --emit-json \
  --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
  --output-definition "${OUTPUT}/configuration-source-oracle" \
  >"${OUTPUT}/logs/configuration-source-oracle.stdout" 2>"${OUTPUT}/logs/configuration-source-oracle.stderr"

run_driver() {
  local mode="$1" output="$2"
  R3_G_02_BUILD_ROOT="${BUILD_ROOT}" R3_G_02_MODE="${mode}" \
  R3_G_02_PORTABLE_SOURCE="${PORTABLE_SOURCE}" \
  R3_G_02_RECORD="${OUTPUT}/records/${output}.json" \
  R3_G_02_TRACE_K_DEFINITION="${OUTPUT}/trace-k-kompiled" \
  R3_G_02_CONFIGURATION_K_DEFINITION="${OUTPUT}/configuration-k-kompiled" \
    "${TASK}/run-driver.sh" "${FIXTURE}" --backend haskell --emit-json \
      --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
}
run_driver positive-a composition-a
run_driver positive-b composition-b

python3 "${TASK}/render_source_oracles.py" \
  "${ORACLE_TEMPLATE}" "${OUTPUT}/records/composition-a.json" \
  "${OUTPUT}/generated/source-oracle.k" \
  "${OUTPUT}/generated/portable-source-oracle.k"
kompile "${OUTPUT}/generated/source-oracle.k" --backend haskell --emit-json \
  --main-module R3-G-01-SOURCE-ORACLE --syntax-module R3-G-01-SOURCE-ORACLE-SYNTAX \
  --output-definition "${OUTPUT}/source-oracle" \
  >"${OUTPUT}/logs/source-oracle.stdout" 2>"${OUTPUT}/logs/source-oracle.stderr"

run_negative() {
  local mode="$1" output="$2"
  set +e
  R3_G_02_BUILD_ROOT="${BUILD_ROOT}" R3_G_02_MODE="${mode}" \
  R3_G_02_PORTABLE_SOURCE="${PORTABLE_SOURCE}" \
  R3_G_02_RECORD="${OUTPUT}/records/${output}.json" \
  R3_G_02_TRACE_K_DEFINITION="${OUTPUT}/trace-k-kompiled" \
  R3_G_02_CONFIGURATION_K_DEFINITION="${OUTPUT}/configuration-k-kompiled" \
    "${TASK}/run-driver.sh" "${FIXTURE}" --backend haskell \
      --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
  local exit_code=$?
  set -e
  [[ ${exit_code} -ne 0 ]]
  printf '%s\n' "${exit_code}" >"${OUTPUT}/logs/${output}.exit"
}

run_negative config-stale-definition negative-config-stale-definition
run_negative config-stale-target-content negative-config-stale-content
run_negative config-stale-target-provenance negative-config-stale-provenance
run_negative config-zero-target negative-config-zero
run_negative config-duplicate-target negative-config-duplicate
run_negative config-unsupported-parent-path negative-config-parent-path
run_negative config-out-of-bounds-template-path negative-config-template-path
run_negative config-malformed-template negative-config-malformed-template
run_negative config-non-leaf-template negative-config-non-leaf-template
run_negative config-missing-production negative-config-missing-production
run_negative config-ambiguous-production negative-config-ambiguous-production
run_negative config-missing-sort negative-config-missing-sort
run_negative config-ambiguous-sort negative-config-ambiguous-sort
run_negative config-unknown-constructor negative-config-unknown-constructor
run_negative config-non-nullary-initializer negative-config-non-nullary
run_negative config-variable-initializer negative-config-variable
run_negative config-sort-invalid-initializer negative-config-sort-invalid
run_negative config-conflict-existing negative-config-conflict
run_negative config-conflict-shape negative-config-conflict-shape
run_negative config-false-already-present negative-config-false-already
run_negative config-false-already-shape negative-config-false-already-shape
run_negative config-failure-wrong-schema negative-config-failure-wrong-schema
run_negative config-failure-unknown-reason negative-config-failure-unknown-reason
run_negative config-failure-invalid-count negative-config-failure-invalid-count

run_negative stale-target-content negative-rule-stale-content
run_negative stale-target-provenance negative-rule-stale-provenance
run_negative zero-target negative-rule-zero
run_negative duplicate-target negative-rule-duplicate
run_negative unsupported-path negative-rule-path
run_negative missing-cell-metadata negative-rule-missing-cell
run_negative ambiguous-cell-metadata negative-rule-ambiguous-cell
run_negative missing-constructor-metadata negative-rule-missing-constructor
run_negative ambiguous-constructor-metadata negative-rule-ambiguous-constructor
run_negative unknown-constructor negative-rule-unknown-constructor
run_negative sort-invalid negative-rule-sort
run_negative variable-collision negative-rule-variable
run_negative conflict-existing negative-rule-conflict
run_negative false-already-present negative-rule-false-already
run_negative unsupported-shape negative-rule-unsupported-shape

for definition in baseline p3-oracle configuration-source-oracle composition-a composition-b source-oracle; do
  for program in firing nonfiring; do
    input="${FIRING}"
    [[ "${program}" == nonfiring ]] && input="${NONFIRING}"
    krun "${input}" --definition "${OUTPUT}/${definition}" \
      >"${OUTPUT}/runtime/${definition}-${program}.out" \
      2>"${OUTPUT}/runtime/${definition}-${program}.err"
    python3 "${TASK}/project_runtime.py" \
      "${OUTPUT}/runtime/${definition}-${program}.out" \
      "${OUTPUT}/projections/${definition}-${program}.json"
  done
done

for definition in composition-a composition-b; do
  python3 "${NORMALIZER}" "${OUTPUT}/${definition}/definition.kore" \
    "${OUTPUT}/projections/${definition}-definition.kore"
  python3 "${TASK}/project_rule_kore.py" --label bump-state \
    "${OUTPUT}/${definition}/definition.kore" \
    "${OUTPUT}/projections/${definition}-bump-state.kore"
done
cmp "${OUTPUT}/projections/composition-a-definition.kore" \
  "${OUTPUT}/projections/composition-b-definition.kore"
cmp "${OUTPUT}/projections/composition-a-bump-state.kore" \
  "${OUTPUT}/projections/composition-b-bump-state.kore"
grep -Fq "Lbl'-LT-'trace'-GT-'" "${OUTPUT}/projections/composition-a-bump-state.kore"
grep -Fq "LblruleApplied" "${OUTPUT}/projections/composition-a-bump-state.kore"

fixture_source="$(readlink -f "${FIXTURE}")"
config_oracle_source="$(readlink -f "${CONFIG_ORACLE}")"
python3 "${TASK}/project_trace_configuration.py" \
  "${OUTPUT}/composition-a/definition.kore" "${OUTPUT}/projections/composition-trace-cell.json" \
  --source "${fixture_source}" --expected-location 'Location(26,7,26,25)'
python3 "${TASK}/project_trace_configuration.py" \
  "${OUTPUT}/composition-b/definition.kore" "${OUTPUT}/projections/composition-b-trace-cell.json" \
  --source "${fixture_source}" --expected-location 'Location(26,7,26,25)'
cmp "${OUTPUT}/projections/composition-trace-cell.json" \
  "${OUTPUT}/projections/composition-b-trace-cell.json"
python3 "${TASK}/project_trace_configuration.py" \
  "${OUTPUT}/configuration-source-oracle/definition.kore" \
  "${OUTPUT}/projections/configuration-oracle-trace-cell.json" \
  --source "${config_oracle_source}" --expected-location 'Location(27,7,27,29)'
jq -e --slurp '
  .[0].semanticSha256 == .[1].semanticSha256
  and .[0].semanticSha256 == .[2].semanticSha256
  and .[0].sort == .[1].sort and .[0].bodySort == .[1].bodySort
  and .[0].source == .[1].source and .[0].location == .[1].location
  and .[0].source != .[2].source and .[0].location != .[2].location
' "${OUTPUT}/projections/composition-trace-cell.json" \
  "${OUTPUT}/projections/composition-b-trace-cell.json" \
  "${OUTPUT}/projections/configuration-oracle-trace-cell.json" >/dev/null

for artifact in syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT}/composition-a/${artifact}" "${OUTPUT}/composition-b/${artifact}"
  python3 "${TASK}/project_semantic_artifact.py" \
    "${OUTPUT}/composition-a/${artifact}" "${OUTPUT}/projections/composition-${artifact}" \
    --source "${fixture_source}" --trace-location 'Location(26,7,26,25)'
  python3 "${TASK}/project_semantic_artifact.py" \
    "${OUTPUT}/configuration-source-oracle/${artifact}" \
    "${OUTPUT}/projections/configuration-oracle-${artifact}" \
    --source "${config_oracle_source}" --trace-location 'Location(27,7,27,29)'
  cmp "${OUTPUT}/projections/composition-${artifact}" \
    "${OUTPUT}/projections/configuration-oracle-${artifact}"
done

for program in firing nonfiring; do
  cmp "${OUTPUT}/runtime/composition-a-${program}.out" \
    "${OUTPUT}/runtime/composition-b-${program}.out"
  cmp "${OUTPUT}/runtime/composition-a-${program}.out" \
    "${OUTPUT}/runtime/source-oracle-${program}.out"
  cmp "${OUTPUT}/projections/composition-a-${program}.json" \
    "${OUTPUT}/projections/source-oracle-${program}.json"
  for definition in baseline p3-oracle composition-a; do
    python3 "${TASK}/project_runtime.py" --erase-trace \
      "${OUTPUT}/runtime/${definition}-${program}.out" \
      "${OUTPUT}/projections/${definition}-${program}-erased.json"
  done
  cmp "${OUTPUT}/projections/baseline-${program}-erased.json" \
    "${OUTPUT}/projections/composition-a-${program}-erased.json"
  cmp "${OUTPUT}/projections/p3-oracle-${program}-erased.json" \
    "${OUTPUT}/projections/composition-a-${program}-erased.json"
done
jq -e '.k=="1" and .state=="2" and (.trace|length)==1 and .trace[0].kind=="RuleApplied"' \
  "${OUTPUT}/projections/composition-a-firing.json" >/dev/null
jq -e '. == {k:"1",state:"1",trace:[]}' \
  "${OUTPUT}/projections/composition-a-nonfiring.json" >/dev/null
jq -e '. == {k:"1",state:"2",trace:[]}' \
  "${OUTPUT}/projections/configuration-source-oracle-firing.json" >/dev/null
jq -e '. == {k:"1",state:"1",trace:[]}' \
  "${OUTPUT}/projections/configuration-source-oracle-nonfiring.json" >/dev/null
jq -e '. == {k:"1",state:"2"}' \
  "${OUTPUT}/projections/baseline-firing.json" >/dev/null
jq -e '. == {k:"1",state:"1"}' \
  "${OUTPUT}/projections/baseline-nonfiring.json" >/dev/null
jq -e '
  .mode=="identity-pre-cf-baseline" and .officialMain
  and .configurationTransform=="Function.identity() through backward-compatible patched Kompile.run"
  and .postCfAdapterInvocations==0 and .backendConstructed
  and .artifacts=={compiledBin:true,definitionKore:true,macrosKore:true,syntaxDefinitionKore:true}
' "${OUTPUT}/records/identity-baseline.json" >/dev/null

jq -e --slurpfile record "${OUTPUT}/records/composition-a.json" '
  .trace[0].origin == {
    id:$record[0].ruleTargetLineage,label:$record[0].ruleTargetLabel,
    module:$record[0].ruleTargetModule,source:$record[0].ruleTargetSource,
    location:$record[0].ruleTargetLocation
  }' "${OUTPUT}/projections/composition-a-firing.json" >/dev/null
jq -e --arg fixtureSource "${fixture_source}" --arg portableSource "${PORTABLE_SOURCE}" '
  .configurationTargetSource == $fixtureSource
  and .configurationTargetSource == .ruleTargetSource
  and (.configurationTargetSource | startswith("/"))
  and .portableConfigurationEvidenceProjected
  and .portableConfigurationOrderingValidated
  and .portableConfigurationTargetSource == $portableSource
  and .portableConfigurationTargetLineage != .configurationTargetLineage
  and .portableEvidenceProjected and .portableRuleOrderingValidated
  and .portableTermMetadataRederived and .portableSource == $portableSource
  and .portableRuleTargetSource == $portableSource
  and .portableRuleTargetLineage != .ruleTargetLineage
' "${OUTPUT}/records/composition-a.json" >/dev/null

for record in composition-a composition-b; do
  jq -e '
    .status=="accepted"
    and .configurationContract=="KTraceConfigurationAugmentation-v1"
    and .configurationHookInvocations==1
    and .configurationKInvocationsPass1==1 and .configurationKInvocationsPass2==1
    and .configurationCandidateCountPass1==1 and .configurationStatusPass1=="apply"
    and .configurationCandidateCountPass2==1 and .configurationStatusPass2=="already-present"
    and .configurationValidatedOperationCount==1 and .configurationApplicationCount==1
    and .configurationChangedConfigurationCount==1
    and .configurationAlreadyPresentValidatedCount==1
    and .configurationSecondSameReference and .configurationTransformedDefinitionReturned
    and (.configurationExpectedCloneFingerprint|length)==64
    and .configurationExpectedCloneFingerprint==.configurationInstalledCellFingerprint
    and (.portableConfigurationExpectedCloneFingerprint|length)==64
    and .portableConfigurationExpectedCloneFingerprint==.portableConfigurationInstalledCellFingerprint
    and .configurationMetadataPreserved and .configurationConditionsPreserved
    and .configurationProvenancePreserved and .configurationOriginalNodesPreserved
    and .configurationBeforeDefinition != .configurationAfterDefinition
    and (.configurationInitializerCanonical | startswith("tApply("))
    and (.configurationInitializerCanonical | contains("tTermNil"))
    and (.configurationInitializerCanonical | contains("\".List\""))
    and (.configurationInitializerCanonical | contains("cSort(\"List\""))
    and (.configurationInitializerCanonical | contains("cSortNil"))
    and ((.configurationInitializerCanonical | contains("tToken(")) | not)
    and ((.configurationInitializerCanonical | contains("tVariable(")) | not)
    and (.configurationOperationCanonicalPass1 | startswith("cloneLeafCellWithTypedContentFromInput(cPathCons(cApplicationArgument(2),cPathNil),cPathCons(cApplicationArgument(2),cPathCons(cApplicationArgument(1),cPathNil)),"))
    and .contract=="KRuleAppliedTrace-v1" and .postCfAdapterInvocations==1
    and .postCfConstructed and .ruleKInvocationsPass1==1 and .ruleKInvocationsPass2==1
    and .ruleCandidateCountPass1==1 and .ruleStatusPass1=="apply"
    and .ruleCandidateCountPass2==1 and .ruleStatusPass2=="already-present"
    and .ruleValidatedOperationCount==1 and .ruleApplicationCount==1
    and .ruleChangedRuleCount==1 and .ruleAlreadyPresentValidatedCount==1
    and .ruleSecondSameReference and .ruleTransformedDefinitionReturned
    and .ruleIdentityPreserved and .ruleProvenancePreserved
    and .ruleAttributesPreserved and .ruleConditionsPreserved
    and .ruleOriginalNodesPreserved and .generatedCellBodySort=="List"
    and .backendConstructed
  ' "${OUTPUT}/records/${record}.json" >/dev/null
done
jq -e --slurp '
  .[0].configurationRequestFingerprintPass1 == .[1].configurationRequestFingerprintPass1
  and .[0].configurationResponseFingerprintPass1 == .[1].configurationResponseFingerprintPass1
  and .[0].configurationRequestFingerprintPass2 == .[1].configurationRequestFingerprintPass2
  and .[0].configurationResponseFingerprintPass2 == .[1].configurationResponseFingerprintPass2
  and .[0].configurationOperationCanonicalPass1 == .[1].configurationOperationCanonicalPass1
  and .[0].configurationOperationCanonicalPass2 == .[1].configurationOperationCanonicalPass2
  and .[0].portableConfigurationRequestFingerprintPass1 == .[1].portableConfigurationRequestFingerprintPass1
  and .[0].portableConfigurationResponseFingerprintPass1 == .[1].portableConfigurationResponseFingerprintPass1
  and .[0].portableConfigurationRequestFingerprintPass2 == .[1].portableConfigurationRequestFingerprintPass2
  and .[0].portableConfigurationResponseFingerprintPass2 == .[1].portableConfigurationResponseFingerprintPass2
  and .[0].portableConfigurationOperationCanonicalPass1 == .[1].portableConfigurationOperationCanonicalPass1
  and .[0].portableConfigurationOperationCanonicalPass2 == .[1].portableConfigurationOperationCanonicalPass2
  and .[0].configurationExpectedCloneFingerprint == .[1].configurationExpectedCloneFingerprint
  and .[0].configurationInstalledCellFingerprint == .[1].configurationInstalledCellFingerprint
  and .[0].portableConfigurationExpectedCloneFingerprint == .[1].portableConfigurationExpectedCloneFingerprint
  and .[0].portableConfigurationInstalledCellFingerprint == .[1].portableConfigurationInstalledCellFingerprint
  and .[0].ruleRequestFingerprintPass1 == .[1].ruleRequestFingerprintPass1
  and .[0].ruleResponseFingerprintPass1 == .[1].ruleResponseFingerprintPass1
  and .[0].ruleRequestFingerprintPass2 == .[1].ruleRequestFingerprintPass2
  and .[0].ruleResponseFingerprintPass2 == .[1].ruleResponseFingerprintPass2
  and .[0].ruleOperationCanonicalPass1 == .[1].ruleOperationCanonicalPass1
  and .[0].ruleOperationCanonicalPass2 == .[1].ruleOperationCanonicalPass2
  and .[0].portableRuleRequestFingerprintPass1 == .[1].portableRuleRequestFingerprintPass1
  and .[0].portableRuleResponseFingerprintPass1 == .[1].portableRuleResponseFingerprintPass1
  and .[0].portableRuleRequestFingerprintPass2 == .[1].portableRuleRequestFingerprintPass2
  and .[0].portableRuleResponseFingerprintPass2 == .[1].portableRuleResponseFingerprintPass2
  and .[0].portableRuleOperationCanonicalPass1 == .[1].portableRuleOperationCanonicalPass1
  and .[0].portableRuleOperationCanonicalPass2 == .[1].portableRuleOperationCanonicalPass2
' "${OUTPUT}/records/composition-a.json" "${OUTPUT}/records/composition-b.json" >/dev/null

write_negative_filesystem_inventory() {
  local record="$1" stage="$2" directory="${OUTPUT}/${record}"
  local files='[]' directories='[]'
  if [[ -d "${directory}" ]]; then
    files="$(find "${directory}" -mindepth 1 \( -type f -o -type l \) -printf '%P\n' \
      | LC_ALL=C sort | jq -Rsc 'split("\n")|map(select(length>0))')"
    directories="$(find "${directory}" -mindepth 1 -type d -printf '%P\n' \
      | LC_ALL=C sort | jq -Rsc 'split("\n")|map(select(length>0))')"
  fi
  jq -n --arg key "$(jq -r .mode "${OUTPUT}/records/${record}.json")" \
    --arg stage "${stage}" --argjson files "${files}" --argjson directories "${directories}" '
    {key:$key,value:{stage:$stage,filePaths:$files,directoryPaths:$directories,
      frontendStagingPaths:[$files[]|select(test("(^|/)(cache\\.bin|parsed\\.txt|scanner|mainModule\\.txt|mainSyntaxModule\\.txt|timestamp)$"))],
      backendArtifactPaths:[$files[]|select(test("(^|/)(allRules\\.txt|backend\\.txt|compiled\\.bin|compiled\\.json|compiled\\.txt|definition\\.kore|haskellDefinition\\.bin|macros\\.kore|syntaxDefinition\\.kore)$"))]}}
  ' >"${OUTPUT}/projections/filesystem-${record}.json"
}

declare -A config_classes=(
  [negative-config-stale-definition]=stale-precondition
  [negative-config-stale-content]=stale-precondition
  [negative-config-stale-provenance]=stale-precondition
  [negative-config-zero]=k-selection
  [negative-config-duplicate]=k-selection
  [negative-config-parent-path]=path-operation
  [negative-config-template-path]=path-operation
  [negative-config-malformed-template]=path-operation
  [negative-config-non-leaf-template]=path-operation
  [negative-config-missing-production]=initializer-production-metadata
  [negative-config-ambiguous-production]=initializer-production-metadata
  [negative-config-missing-sort]=initializer-sort-metadata
  [negative-config-ambiguous-sort]=initializer-sort-metadata
  [negative-config-unknown-constructor]=initializer-production-metadata
  [negative-config-non-nullary]=initializer-term
  [negative-config-variable]=initializer-term
  [negative-config-sort-invalid]=initializer-sort
  [negative-config-conflict]=conflict
  [negative-config-conflict-shape]=conflict
  [negative-config-false-already]=envelope
  [negative-config-false-already-shape]=envelope
  [negative-config-failure-wrong-schema]=envelope
  [negative-config-failure-unknown-reason]=envelope
  [negative-config-failure-invalid-count]=envelope
)
for record in "${!config_classes[@]}"; do
  jq -e --arg class "${config_classes[$record]}" '
    .status=="rejected" and .configurationClassification==$class
    and .configurationHookInvocations==1 and .configurationApplicationCount==0
    and (.configurationTransformedDefinitionReturned|not)
    and .postCfAdapterInvocations==0 and (.postCfConstructed|not)
    and .ruleApplicationCount==0 and (.backendConstructed|not)
  ' "${OUTPUT}/records/${record}.json" >/dev/null
  for artifact in allRules.txt backend.txt compiled.bin compiled.json compiled.txt \
      definition.kore haskellDefinition.bin macros.kore syntaxDefinition.kore; do
    [[ ! -e "${OUTPUT}/${record}/${artifact}" ]]
  done
  write_negative_filesystem_inventory "${record}" pre-cf
  jq -e '.value.filePaths==[] and .value.directoryPaths==[]
    and .value.frontendStagingPaths==[] and .value.backendArtifactPaths==[]' \
    "${OUTPUT}/projections/filesystem-${record}.json" >/dev/null
done
jq -e '.configurationCandidateCountPass1==0' "${OUTPUT}/records/negative-config-zero.json" >/dev/null
jq -e '.configurationCandidateCountPass1==2' "${OUTPUT}/records/negative-config-duplicate.json" >/dev/null
jq -e '.configurationInputMutationCount==1' \
  "${OUTPUT}/records/negative-config-missing-production.json" \
  "${OUTPUT}/records/negative-config-ambiguous-production.json" \
  "${OUTPUT}/records/negative-config-missing-sort.json" \
  "${OUTPUT}/records/negative-config-ambiguous-sort.json" \
  "${OUTPUT}/records/negative-config-conflict.json" \
  "${OUTPUT}/records/negative-config-conflict-shape.json" \
  "${OUTPUT}/records/negative-config-false-already-shape.json" >/dev/null
jq -e '
  .configurationFailureObserved and .configurationFailureEnvelopeValidated
  and .configurationFailureSchema=="KTraceConfigurationAugmentation-v1"
  and .configurationFailureReason=="conflicting-existing-state"
  and .configurationFailureCount==1 and .configurationCandidateCountPass2==1
' "${OUTPUT}/records/negative-config-conflict.json" \
  "${OUTPUT}/records/negative-config-conflict-shape.json" >/dev/null
jq -e '
  .configurationStatusPass2=="already-present"
  and .configurationCandidateCountPass2==1
  and (.configurationFailureObserved|not)
' "${OUTPUT}/records/negative-config-false-already-shape.json" >/dev/null
jq -e '
  .configurationFailureObserved and (.configurationFailureEnvelopeValidated|not)
  and .configurationFailureCanonical=="cTraceAugmentationFailure(\"KTraceConfigurationAugmentation-v0\",\"structural-target-cardinality\",0)"
  and .configurationFailureSchema=="KTraceConfigurationAugmentation-v0"
  and .configurationFailureReason=="structural-target-cardinality"
  and .configurationFailureCount==0
' "${OUTPUT}/records/negative-config-failure-wrong-schema.json" >/dev/null
jq -e '
  .configurationFailureObserved and (.configurationFailureEnvelopeValidated|not)
  and .configurationFailureCanonical=="cTraceAugmentationFailure(\"KTraceConfigurationAugmentation-v1\",\"unknown-reason\",0)"
  and .configurationFailureSchema=="KTraceConfigurationAugmentation-v1"
  and .configurationFailureReason=="unknown-reason"
  and .configurationFailureCount==0
' "${OUTPUT}/records/negative-config-failure-unknown-reason.json" >/dev/null
jq -e '
  .configurationFailureObserved and (.configurationFailureEnvelopeValidated|not)
  and .configurationFailureCanonical=="cTraceAugmentationFailure(\"KTraceConfigurationAugmentation-v1\",\"structural-target-cardinality\",-1)"
  and .configurationFailureSchema=="KTraceConfigurationAugmentation-v1"
  and .configurationFailureReason=="structural-target-cardinality"
  and .configurationFailureCount==(-1)
' "${OUTPUT}/records/negative-config-failure-invalid-count.json" >/dev/null

declare -A rule_classes=(
  [negative-rule-stale-content]=stale-precondition
  [negative-rule-stale-provenance]=stale-precondition
  [negative-rule-zero]=k-selection
  [negative-rule-duplicate]=k-selection
  [negative-rule-path]=path-operation
  [negative-rule-missing-cell]=generated-metadata
  [negative-rule-ambiguous-cell]=generated-metadata
  [negative-rule-missing-constructor]=constructor-metadata
  [negative-rule-ambiguous-constructor]=constructor-metadata
  [negative-rule-unknown-constructor]=constructor-metadata
  [negative-rule-sort]=term-sort
  [negative-rule-variable]=fresh-variable
  [negative-rule-conflict]=conflict
  [negative-rule-false-already]=envelope
  [negative-rule-unsupported-shape]=conservative-shape-rejection
)
for record in "${!rule_classes[@]}"; do
  jq -e --arg class "${rule_classes[$record]}" '
    .status=="rejected" and .classification==$class
    and .configurationApplicationCount==1
    and .configurationStatusPass1=="apply"
    and .configurationStatusPass2=="already-present"
    and .configurationAlreadyPresentValidatedCount==1
    and .configurationTransformedDefinitionReturned
    and .postCfAdapterInvocations==1 and .ruleApplicationCount==0
    and (.ruleTransformedDefinitionReturned|not) and (.backendConstructed|not)
  ' "${OUTPUT}/records/${record}.json" >/dev/null
  for artifact in allRules.txt backend.txt compiled.bin compiled.json compiled.txt \
      definition.kore haskellDefinition.bin macros.kore syntaxDefinition.kore; do
    [[ ! -e "${OUTPUT}/${record}/${artifact}" ]]
  done
  write_negative_filesystem_inventory "${record}" post-cf
  jq -e '.value.filePaths==["cache.bin","parsed.txt","scanner"]
    and .value.directoryPaths==[]
    and .value.frontendStagingPaths==.value.filePaths
    and .value.backendArtifactPaths==[]' \
    "${OUTPUT}/projections/filesystem-${record}.json" >/dev/null
done
jq -e '.ruleCandidateCountPass1==0' "${OUTPUT}/records/negative-rule-zero.json" >/dev/null
jq -e '.ruleCandidateCountPass1==2' "${OUTPUT}/records/negative-rule-duplicate.json" >/dev/null

jq -s 'map({key:.mode,value:{
  classification:.configurationClassification,
  candidateCountPass1:.configurationCandidateCountPass1,
  candidateCountPass2:.configurationCandidateCountPass2,
  inputMutationCount:.configurationInputMutationCount,
  applicationCount:.configurationApplicationCount,
  transformedDefinitionReturned:.configurationTransformedDefinitionReturned,
  postCfAdapterInvocations,ruleApplicationCount,backendConstructed,
  failure:{observed:.configurationFailureObserved,
    canonical:.configurationFailureCanonical,schema:.configurationFailureSchema,
    reason:.configurationFailureReason,count:.configurationFailureCount,
    envelopeValidated:.configurationFailureEnvelopeValidated}
}})|from_entries' "${OUTPUT}"/records/negative-config-*.json \
  >"${OUTPUT}/projections/configuration-negatives.json"
jq -s 'map({key:.mode,value:{
  classification,
  configurationApplicationCount,
  configurationAlreadyPresentValidatedCount,
  candidateCountPass1:.ruleCandidateCountPass1,
  candidateCountPass2:.ruleCandidateCountPass2,
  inputMutationCount:.ruleInputMutationCount,
  applicationCount:.ruleApplicationCount,
  transformedDefinitionReturned:.ruleTransformedDefinitionReturned,
  backendConstructed
}})|from_entries' "${OUTPUT}"/records/negative-rule-*.json \
  >"${OUTPUT}/projections/rule-negatives.json"
jq -s 'map(.)|from_entries' "${OUTPUT}"/projections/filesystem-negative-*.json \
  >"${OUTPUT}/projections/negative-filesystem.json"
for group in configuration rule; do
  jq --slurpfile filesystem "${OUTPUT}/projections/negative-filesystem.json" '
    with_entries(.value += {
      filesystem:$filesystem[0][.key],
      backendArtifactsEmitted:(($filesystem[0][.key].backendArtifactPaths|length)>0)
    })
  ' "${OUTPUT}/projections/${group}-negatives.json" \
    >"${OUTPUT}/projections/${group}-negatives.with-filesystem.json"
  mv "${OUTPUT}/projections/${group}-negatives.with-filesystem.json" \
    "${OUTPUT}/projections/${group}-negatives.json"
done

python3 - "${OUTPUT}/records/composition-a.json" \
    "${OUTPUT}/projections/composition-a-firing.json" \
    "${OUTPUT}/projections/composition-a-nonfiring.json" \
    "${OUTPUT}/projections/portable-firing.json" \
    "${OUTPUT}/projections/portable-nonfiring.json" <<'PY'
import json
import sys
from pathlib import Path

record_path, firing_path, nonfiring_path, portable_firing_path, portable_nonfiring_path = map(Path, sys.argv[1:])
record = json.loads(record_path.read_text(encoding="utf-8"))
firing = json.loads(firing_path.read_text(encoding="utf-8"))
nonfiring = json.loads(nonfiring_path.read_text(encoding="utf-8"))
raw_origin = firing["trace"][0]["origin"]
if raw_origin != {
    "id": record["ruleTargetLineage"],
    "label": record["ruleTargetLabel"],
    "location": record["ruleTargetLocation"],
    "module": record["ruleTargetModule"],
    "source": record["ruleTargetSource"],
}:
    raise SystemExit("raw runtime origin was not exact selected official provenance")
firing["trace"][0]["origin"] = {
    "id": record["portableRuleTargetLineage"],
    "label": record["portableRuleTargetLabel"],
    "location": record["portableRuleTargetLocation"],
    "module": record["portableRuleTargetModule"],
    "source": record["portableRuleTargetSource"],
}
portable_firing_path.write_text(json.dumps(firing, sort_keys=True, indent=2) + "\n", encoding="utf-8")
portable_nonfiring_path.write_text(json.dumps(nonfiring, sort_keys=True, indent=2) + "\n", encoding="utf-8")
PY
! rg -F "${REPO_ROOT}" "${OUTPUT}/projections/portable-firing.json" \
  "${OUTPUT}/projections/portable-nonfiring.json" \
  "${OUTPUT}/generated/portable-source-oracle.k"

{
  sha256sum "${CONFIG_K}" "${TRACE_K}" "${DRIVER}" "${CONFIG_DRIVER}" \
    "${TASK}/replay.sh" "${TASK}/run-driver.sh" "${TASK}/verify.sh" \
    "${TASK}/project_runtime.py" "${TASK}/project_rule_kore.py" \
    "${TASK}/project_trace_configuration.py" "${TASK}/project_semantic_artifact.py" \
    "${TASK}/render_source_oracles.py"
  sha256sum "${FIXTURE}" "${CONFIG_ORACLE}" "${ORACLE_TEMPLATE}" "${NONFIRING}" \
    "${OUTPUT}/generated/portable-source-oracle.k"
  sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/"{DefinitionParsing,Kompile}.class
  sha256sum "${OUTPUT}"/records/*.json "${OUTPUT}"/runtime/*.out "${OUTPUT}"/projections/*.json
} >"${OUTPUT}/SHA256SUMS"

jq -n \
  --arg activation "${ACTIVATION}" --arg prototype "${PROTOTYPE}" \
  --arg startingRevision "${STARTING_REVISION}" --arg r3g02Activation "${R3_G_02_ACTIVATION}" \
  --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kSource "${K_SOURCE}" --arg kStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kompile "${KOMPILE_BIN}" --arg frontendSha "${FRONTEND_SHA}" \
  --arg hookPatchSha "${HOOK_PATCH_SHA}" --arg packetSha "${PACKET_SHA}" \
  --arg repairPacketSha "${REPAIR_PACKET_SHA}" --arg auditCheckpointSha "${AUDIT_CHECKPOINT_SHA}" \
  --arg checkpointSha "${CHECKPOINT_SHA}" --arg r2PacketSha "${R2_PACKET_SHA}" \
  --arg r3PacketSha "${R3_PACKET_SHA}" \
  --arg acceptedConfigKSha "${ACCEPTED_CONFIG_K_SHA}" \
  --arg acceptedConfigJavaSha "${ACCEPTED_CONFIG_JAVA_SHA}" \
  --arg acceptedConfigReplaySha "${ACCEPTED_CONFIG_REPLAY_SHA}" \
  --arg acceptedConfigResultsSha "${ACCEPTED_CONFIG_RESULTS_SHA}" \
  --arg acceptedConfigReportSha "${ACCEPTED_CONFIG_REPORT_SHA}" \
  --arg acceptedConfigSpineTree "${ACCEPTED_CONFIG_SPINE_TREE}" \
  --arg acceptedConfigEvidenceTree "${ACCEPTED_CONFIG_EVIDENCE_TREE}" \
  --arg acceptedTraceKSha "${ACCEPTED_TRACE_K_SHA}" \
  --arg acceptedTraceJavaSha "${ACCEPTED_TRACE_JAVA_SHA}" \
  --arg acceptedTraceReplaySha "${ACCEPTED_TRACE_REPLAY_SHA}" \
  --arg acceptedTraceResultsSha "${ACCEPTED_TRACE_RESULTS_SHA}" \
  --arg acceptedTraceReportSha "${ACCEPTED_TRACE_REPORT_SHA}" \
  --arg acceptedTraceSpineTree "${ACCEPTED_TRACE_SPINE_TREE}" \
  --arg acceptedTraceEvidenceTree "${ACCEPTED_TRACE_EVIDENCE_TREE}" \
  --arg configKSha "$(sha256sum "${CONFIG_K}"|awk '{print $1}')" \
  --arg traceKSha "$(sha256sum "${TRACE_K}"|awk '{print $1}')" \
  --arg driverSha "$(sha256sum "${DRIVER}"|awk '{print $1}')" \
  --arg configDriverSha "$(sha256sum "${CONFIG_DRIVER}"|awk '{print $1}')" \
  --arg replaySha "$(sha256sum "${TASK}/replay.sh"|awk '{print $1}')" \
  --arg runnerSha "$(sha256sum "${TASK}/run-driver.sh"|awk '{print $1}')" \
  --arg verifierSha "$(sha256sum "${TASK}/verify.sh"|awk '{print $1}')" \
  --arg runtimeProjectorSha "$(sha256sum "${TASK}/project_runtime.py"|awk '{print $1}')" \
  --arg ruleProjectorSha "$(sha256sum "${TASK}/project_rule_kore.py"|awk '{print $1}')" \
  --arg configProjectorSha "$(sha256sum "${TASK}/project_trace_configuration.py"|awk '{print $1}')" \
  --arg semanticProjectorSha "$(sha256sum "${TASK}/project_semantic_artifact.py"|awk '{print $1}')" \
  --arg oracleRendererSha "$(sha256sum "${TASK}/render_source_oracles.py"|awk '{print $1}')" \
  --arg packageSha "$(sha256sum "${REPO_ROOT}/package.json"|awk '{print $1}')" \
  --arg fixtureSha "$(sha256sum "${FIXTURE}"|awk '{print $1}')" \
  --arg configOracleSha "$(sha256sum "${CONFIG_ORACLE}"|awk '{print $1}')" \
  --arg oracleTemplateSha "$(sha256sum "${ORACLE_TEMPLATE}"|awk '{print $1}')" \
  --arg portableOracleSha "$(sha256sum "${OUTPUT}/generated/portable-source-oracle.k"|awk '{print $1}')" \
  --arg nonfiringSha "$(sha256sum "${NONFIRING}"|awk '{print $1}')" \
  --arg p3Sha "${P3_SHA}" --arg firingSha "${FIRING_SHA}" --arg normalizerSha "${NORMALIZER_SHA}" \
  --arg portableSource "${PORTABLE_SOURCE}" --argjson fullCycles "${FULL_CYCLES}" \
  --argjson repairCycles "${REPAIR_CYCLES}" \
  --slurpfile a "${OUTPUT}/records/composition-a.json" \
  --slurpfile identityBaseline "${OUTPUT}/records/identity-baseline.json" \
  --slurpfile firing "${OUTPUT}/projections/portable-firing.json" \
  --slurpfile nonfiring "${OUTPUT}/projections/portable-nonfiring.json" \
  --slurpfile configProjection "${OUTPUT}/projections/composition-trace-cell.json" \
  --slurpfile oracleProjection "${OUTPUT}/projections/configuration-oracle-trace-cell.json" \
  --slurpfile configNegatives "${OUTPUT}/projections/configuration-negatives.json" \
  --slurpfile ruleNegatives "${OUTPUT}/projections/rule-negatives.json" \
  '{
    schemaVersion:2,
    task:"R3-G-02A-exact-shell-and-failure-envelope",
    verdict:"pass",
    fullCycleCount:$fullCycles,
    repairCycleCount:$repairCycles,
    activationRevision:$activation,
    prototypeRevision:$prototype,
    startingRevision:$startingRevision,
    r3g02ActivationRevision:$r3g02Activation,
    contracts:["KTraceConfigurationAugmentation-v1","KRuleAppliedTrace-v1"],
    pin:{
      kRelease:$kRelease,kCommit:$kCommit,kSource:$kSource,kSourceStatus:$kStatus,
      resolvedKompile:$kompile,frontendJarSha256:$frontendSha,hookPatchSha256:$hookPatchSha,
      packetSha256:$packetSha,repairPacketSha256:$repairPacketSha,
      auditCheckpointSha256:$auditCheckpointSha,
      acceptanceCheckpointSha256:$checkpointSha,
      acceptedPackets:{configuration:$r2PacketSha,ruleTrace:$r3PacketSha},
      acceptedConfiguration:{kSemantics:$acceptedConfigKSha,javaHost:$acceptedConfigJavaSha,
        replay:$acceptedConfigReplaySha,results:$acceptedConfigResultsSha,report:$acceptedConfigReportSha,
        spineTree:$acceptedConfigSpineTree,evidenceTree:$acceptedConfigEvidenceTree},
      acceptedRuleTrace:{kSemantics:$acceptedTraceKSha,javaHost:$acceptedTraceJavaSha,
        replay:$acceptedTraceReplaySha,results:$acceptedTraceResultsSha,report:$acceptedTraceReportSha,
        spineTree:$acceptedTraceSpineTree,evidenceTree:$acceptedTraceEvidenceTree},
      environment:{LC_ALL:"C",LANG:"C",TZ:"UTC"}
    },
    taskSourceSha256:{
      repairPacket:$repairPacketSha,auditCheckpoint:$auditCheckpointSha,
      configurationK:$configKSha,unchangedRuleTraceK:$traceKSha,compositionHost:$driverSha,
      configurationHost:$configDriverSha,replay:$replaySha,runner:$runnerSha,verifier:$verifierSha,
      runtimeProjector:$runtimeProjectorSha,ruleProjector:$ruleProjectorSha,
      configurationProjector:$configProjectorSha,semanticArtifactProjector:$semanticProjectorSha,
      sourceOracleRenderer:$oracleRendererSha,
      packageManifest:$packageSha,
      twoCellFixture:$fixtureSha,configurationSourceOracle:$configOracleSha,
      sourceOracleTemplate:$oracleTemplateSha,portableGeneratedSourceOracle:$portableOracleSha,
      nonfiringProgram:$nonfiringSha,p3Definition:$p3Sha,firingProgram:$firingSha,
      identityNormalizer:$normalizerSha
    },
    ownership:{
      configurationK:["structural two-cell target and cardinality","apply/already-present/conflict",
        "target stale preconditions","parent and shell-template paths","new cell name",
        "exact official nullary initializer production and sort","complete typed ground initializer",
        "complete expected-clone status including all typed node metadata"],
      configurationJava:["complete typed official projection","canonical exact-result parsing",
        "closed failure schema/reason/count validation before classification",
        "exact descriptor and path resolution","four-argument complete expected-shell clone",
        "one complete comparator for immutable delta and idempotence validation"],
      ruleK:["unchanged structural rule selection","fresh typed variable","list/event/origin graph and payload",
        "generated-cell path and apply/already-present/conflict"],
      ruleJava:["unchanged complete post-CF projection","exact metadata/sort/path/payload validation",
        "one immutable rule rebuild and idempotence validation"]
    },
    configurationApplication:($a[0]|{
      contract:.configurationContract,hook:.configurationHook,
      kInvocationsPass1:.configurationKInvocationsPass1,
      kInvocationsPass2:.configurationKInvocationsPass2,
      requestFingerprintPass1:.portableConfigurationRequestFingerprintPass1,
      responseFingerprintPass1:.portableConfigurationResponseFingerprintPass1,
      requestFingerprintPass2:.portableConfigurationRequestFingerprintPass2,
      responseFingerprintPass2:.portableConfigurationResponseFingerprintPass2,
      candidateCountPass1:.configurationCandidateCountPass1,
      candidateCountPass2:.configurationCandidateCountPass2,
      statusPass1:.configurationStatusPass1,statusPass2:.configurationStatusPass2,
      targetLineage:.portableConfigurationTargetLineage,
      targetSource:.portableConfigurationTargetSource,
      targetLocation:.portableConfigurationTargetLocation,
      targetContentBefore:.portableConfigurationTargetContentBefore,
      targetContentAfter:.portableConfigurationTargetContentAfter,
      targetBodyBefore:.portableConfigurationTargetBodyBefore,
      targetBodyAfter:.portableConfigurationTargetBodyAfter,
      beforeDefinition:.portableConfigurationBeforeDefinition,
      afterDefinition:.portableConfigurationAfterDefinition,
      operationPass1:.portableConfigurationOperationCanonicalPass1,
      operationPass2:.portableConfigurationOperationCanonicalPass2,
      initializer:.portableConfigurationInitializerCanonical,
      rawCloneValidation:{fingerprintsRecordedInTransientRunRecords:true,
        expectedInstalledEqual:(.configurationExpectedCloneFingerprint==.configurationInstalledCellFingerprint),
        freshRepeatEqual:true,committedFingerprintValuesOmitted:true,
        omissionReason:"raw clone fingerprints include validated run-local absolute Source metadata; committing either digest would relabel checkout-specific validation as portable evidence"},
      portableExpectedCloneFingerprint:.portableConfigurationExpectedCloneFingerprint,
      portableInstalledCellFingerprint:.portableConfigurationInstalledCellFingerprint,
      validatedOperationCount:.configurationValidatedOperationCount,
      applicationCount:.configurationApplicationCount,
      changedConfigurationCount:.configurationChangedConfigurationCount,
      alreadyPresentValidatedCount:.configurationAlreadyPresentValidatedCount,
      sameReference:.configurationSecondSameReference,
      metadataPreserved:.configurationMetadataPreserved,
      conditionsPreserved:.configurationConditionsPreserved,
      provenancePreserved:.configurationProvenancePreserved,
      originalNodesPreserved:.configurationOriginalNodesPreserved
    }),
    ruleApplication:($a[0]|{
      contract,postCfAdapter,postCfAdapterInvocations,
      kInvocationsPass1:.ruleKInvocationsPass1,kInvocationsPass2:.ruleKInvocationsPass2,
      requestFingerprintPass1:.portableRuleRequestFingerprintPass1,
      responseFingerprintPass1:.portableRuleResponseFingerprintPass1,
      requestFingerprintPass2:.portableRuleRequestFingerprintPass2,
      responseFingerprintPass2:.portableRuleResponseFingerprintPass2,
      candidateCountPass1:.ruleCandidateCountPass1,candidateCountPass2:.ruleCandidateCountPass2,
      statusPass1:.ruleStatusPass1,statusPass2:.ruleStatusPass2,
      targetLineage:.portableRuleTargetLineage,targetModule:.portableRuleTargetModule,
      targetLabel:.portableRuleTargetLabel,targetSource:.portableRuleTargetSource,
      targetLocation:.portableRuleTargetLocation,
      targetContentBefore:.portableRuleTargetContentBefore,
      targetContentAfter:.portableRuleTargetContentAfter,
      targetBodyBefore:.portableRuleTargetBodyBefore,
      targetBodyAfter:.portableRuleTargetBodyAfter,
      targetRequires:.portableRuleTargetRequires,
      targetEnsures:.portableRuleTargetEnsures,
      targetAttributes:.portableRuleTargetAttributes,
      operationPass1:.portableRuleOperationCanonicalPass1,
      operationPass2:.portableRuleOperationCanonicalPass2,
      validatedOperationCount:.ruleValidatedOperationCount,
      applicationCount:.ruleApplicationCount,changedRuleCount:.ruleChangedRuleCount,
      alreadyPresentValidatedCount:.ruleAlreadyPresentValidatedCount,
      sameReference:.ruleSecondSameReference,
      identityPreserved:.ruleIdentityPreserved,
      provenancePreserved:.ruleProvenancePreserved,
      attributesPreserved:.ruleAttributesPreserved,
      conditionsPreserved:.ruleConditionsPreserved,
      originalNodesPreserved:.ruleOriginalNodesPreserved,
      generatedCellName,generatedCellLabel,
      generatedCellSort,generatedCellBodySort,backendConstructed
    }),
    payload:$firing[0].trace[0],
    idempotence:{configurationStatusPass2:$a[0].configurationStatusPass2,
      configurationApplications:$a[0].configurationApplicationCount,
      configurationSameReference:$a[0].configurationSecondSameReference,
      completeCloneValidated:$a[0].configurationAlreadyPresentValidatedCount,
      ruleStatusPass2:$a[0].ruleStatusPass2,ruleApplications:$a[0].ruleApplicationCount,
      ruleSameReference:$a[0].ruleSecondSameReference},
    provenanceInvariant:{
      runtimeTruth:"both contracts validate the exact run-local absolute official Source and source-derived lineage before official lowering/backend acceptance",
      portableEvidence:"only after raw configuration/rule/payload validation, repository-logical sources and every dependent lineage, typed metadata, definition, request, result, operation, oracle and payload are structurally rederived",
      logicalSource:$portableSource,isRawOfficialSource:false,rawFiveFieldEventEqualityValidated:true,
      rawConfigurationSourceAndLineageValidated:true,opaqueRawDigestsRelabeled:false
    },
    oracles:{
      twoCellIdentityPreCfBaseline:$identityBaseline[0],
      firingRuntime:$firing[0],nonfiringRuntime:$nonfiring[0],
      fullRuntimesEqualOrdinarySource:true,
      firingErasureEqualsTwoCellBaselineAndP3:true,
      nonfiringErasureEqualsTwoCellBaselineAndP3:true,
      configurationGenerationSemanticEqual:true,
      traceShellDifference:{classification:"source/location provenance only",
        authoredLocation:$configProjection[0].location,ordinaryLocation:$oracleProjection[0].location},
      repeat:{stable:true,configurationAndRuleRequestResultOperationFingerprints:true,
        rawExpectedAndInstalledCloneFingerprints:true,portableExpectedAndInstalledCloneFingerprints:true,
        focusedConfigurationAndRule:true,normalizedFullKore:true,syntaxKore:true,macros:true,
        eventPayload:true,bothRuntimes:true},
      syntaxAndMacros:{rawKAuthoredRepeatsByteStable:true,
        portableSemanticEqualOrdinarySourceAfterTraceShellErasure:true},
      exactResultParserRejectsNoncanonicalResidualMultipleUnknown:true,
      completeCloneComparatorRejectsIndependentPropertyTokenAndMetadataMutations:true,
      failureSemanticSelfTestsRejectCardinalityOneAndConflictZero:true
    },
    negatives:{configuration:($configNegatives[0]+{
      "exact-result-encodings":{classification:"envelope",applicationCount:0,
        transformedDefinitionReturned:false,postCfAdapterInvocations:0,
        ruleApplicationCount:0,backendConstructed:false,backendArtifactsEmitted:false}}),
      unchangedRule:($ruleNegatives[0]+{
      "exact-result-encodings":{classification:"envelope",configurationApplicationCount:1,
        configurationAlreadyPresentValidatedCount:1,applicationCount:0,
        transformedDefinitionReturned:false,backendConstructed:false,backendArtifactsEmitted:false}})},
    limitations:["one structurally selected configuration and one nullary initializer",
      "one selected concrete rule and one RuleApplied append","two concrete runtime paths only",
      "no matcher, monitor, domain event, symbolic path, corpus, multi-rule or backend-independent event claim"],
    packetAmbiguity:"none requiring a split",
    recommendedFirstMatcherPacket:"one conservative concrete RuleApplied head matcher over the accepted single-event trace, with no new event or symbolic branch"
  }' >"${OUTPUT}/results.json"

cat >"${OUTPUT}/report.md" <<'EOF'
# R3-G-02A exact trace shell and failure envelope repair

Status: repair pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Result

The ordinary fixture remains the accepted event syntax and rule set, but its
configuration has only the `k` and `state` cells. At the accepted typed pre-CF
hook, `KTraceConfigurationAugmentation-v1` structurally chose
that configuration, returned parent path `[2]`, state-shell template path
`[2,1]`, the new cell name, and the exact official nullary `.List` production
of sort `List` as a complete typed ground application. Java resolved those
declared descriptors, constructed the complete expected clone of the
four-argument official shell, installed the `KApply` initializer, and immutably
rebuilt one configuration. K and Java both compare the complete clone:
application metadata, start/end token sorts and attributes, the complete
property subtree, initializer body metadata, and all other projected node
metadata. It contains
no fixture target, cell-name, list-sort, initializer, module, rule, event, or
payload-selection literal.

Reprojection produced exactly one `already-present` candidate. The host
independently found one complete expected clone, applied nothing further, and
returned the same augmented definition reference. Run-local raw
expected/installed fingerprints are recorded in each transient driver record,
validated equal, and compared across the fresh repeat before portable
projection. Their digest values are intentionally omitted from committed
evidence because they contain the already-validated absolute `Source`; this is
an explicit omission, not relabeling. Independently rederived
repository-logical expected and installed fingerprints are committed, equal,
and stable across the fresh repeat. Official cell checks and CF then
generated the trace cell. At the unchanged post-CF boundary,
`KRuleAppliedTrace-v1` selected and edited the same one accepted rule, and its
second pass likewise validated `already-present` with the same definition.

The two-cell no-trace baseline is compiled through the patched overlay's
backward-compatible `Kompile.run`, whose pre-CF configuration transform is
`Function.identity()` and whose pipeline has no task post-CF adapter. The
overlay class hashes and zero post-CF adapter invocations are recorded.

The firing input ends at `k = 1`, `state = 2`, with exactly one `RuleApplied`
event; the non-firing integer ends at `k = 1`, `state = 1`, with an empty trace.
Both full runtimes equal the independent ordinary-source configuration/event
oracle. Trace erasure equals both the two-cell identity baseline and P3. The
focused generated trace cell equals ordinary-source generation except for the
classified shell `Source`/`Location`: the K-authored clone inherits the state
shell provenance, while the ordinary source owns its trace line. Fresh
K-authored repeats have byte-stable syntax Kore and macros; after portable
source projection and erasing only that classified shell difference, both
artifacts equal the ordinary-source semantic projections.

## Ownership and evidence

K owns configuration target/cardinality/status/conflict over the complete
expected clone, all stale
preconditions, both paths, the new name, and the complete initializer
production/sort/term. Java owns typed projection, exact canonical parsing,
generic descriptor/path/shell validation, one shared complete comparator, one
immutable application, and exact delta/idempotence checks. Every parsed
configuration failure is validated before classification: the schema is exact;
the reason is in the three-member closed set; the canonical integer is
nonnegative; structural/initializer cardinality counts cannot be one; and a
conflict count is positive. The ordinary handler and one-conflict helper share
that validator. The unchanged rule contract retains its accepted
split: K owns rule selection and the full list/event/origin payload graph;
Java resolves official descriptors and validates/rebuilds one rule.

Raw execution first validates each contract's absolute run-local official
source and derived lineage, including exact equality of all five runtime event
fields. Only afterward, committed evidence uses
`repo://spine/trace-configuration-composition/fixtures/p3-trace.k`, reorders by
portable identity, and structurally rederives every dependent typed metadata,
definition, request, result, operation, ordinary-source oracle, and payload.
No opaque raw digest is relabeled.
The raw and portable ordinary-source oracles are rendered independently from
the template through exact one-occurrence marker maps, with unique/collision,
residual-marker, and raw-domain exclusion checks; no chained identity
replacement is used.

All stale definition/content/provenance, cardinality, path, malformed shell,
initializer production/sort/shape/groundness, content conflict, property/shape
conflict, false `already-present`, wrong failure schema, unknown failure reason,
canonical negative failure count, and exact-result envelope failures stop with
zero configuration applications and no post-CF/backend artifacts. The three
malformed K-authored failure records and their exact schema/reason/count values
are recorded rather than synthesized. Filesystem inventories prove that every
pre-CF negative has no staging or backend file and that each unchanged post-CF
negative has only the pinned frontend staging allowance and no backend
artifact. All 16 accepted
post-CF failure groups remain unchanged after one successful configuration
application/idempotence validation, with zero rule applications and no backend
artifacts.

## Boundary

The stopped R3-G-02 full-oracle count remains three; this repair used the
separately recorded bounded repair count. This remains one configuration edit,
one nullary initializer, one concrete
event append, and two concrete runtime paths. It adds no matcher, monitor,
domain event, symbolic path, corpus, multi-rule facility, or
backend-independent event claim. No packet ambiguity required a split. The
recommended first matcher packet is one conservative concrete `RuleApplied`
head matcher over this accepted single-event trace, with no new event or
symbolic branch.
EOF

! rg -F "${REPO_ROOT}" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
if [[ "${R3_G_02_FREEZE_EVIDENCE:-0}" == "1" ]]; then
  cp "${OUTPUT}/results.json" "${EVIDENCE}/results.json"
  cp "${OUTPUT}/report.md" "${EVIDENCE}/report.md"
elif [[ -f "${EVIDENCE}/results.json" ]]; then
  cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"
  cmp "${EVIDENCE}/report.md" "${OUTPUT}/report.md"
fi
printf 'R3-G-02A exact trace shell and failure envelope replay: pass\n'
