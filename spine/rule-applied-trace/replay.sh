#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION="af2dbf1223126a6b655b75cdbf83c323e2cdb711"
readonly IMPORTED_PROTOTYPE="c4ad784b5a471d938ff221d1a60fe0d2ae682920"
readonly STARTING_REVISION="249c540b9274c9c9336b1ad3165f8c9976d3ccaf"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_RELEASE="v7.1.337"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly FRONTEND_SHA="c02efedc7b07e46d20e55543bfb2160c73af3e6a80d71436689656c4b7caf4d2"
readonly HOOK_PATCH_SHA="bf9c788c89a201e74c9a51df23fe544333c8bf9898a8a9973dc4163d86f3e543"
readonly PACKET_SHA="42588ee4319e123542ea7ded31ce7f1e9c951ef1f89f4bc28e91f02e2077c1c8"
readonly SEMANTIC_PACKET_SHA="7bbc5a4b6e8f0f814e635c5451c75ddc12102ec60ba2ab88581a0fadd0ed5cfb"
readonly AUDIT_SHA="a8cb763e7043bd9ce3021f5f658cc17557f438661e4d88f42418f09f83c21cbc"
readonly ACCEPTED_K_SHA="d9892fca9c017c3c318249258aafae345d549eb3686c9d7ee05f6e9980c03f2b"
readonly ACCEPTED_JAVA_SHA="9084663dd2d94c27ec28244c53cde103272a9eee5fa63e6714ced3a95f1176ad"
readonly ACCEPTED_REPLAY_SHA="bc0379f9538d316dfa273d24623ca39bf9fb741e47d9523362d8df8ca6b2450d"
readonly ACCEPTED_RUNNER_SHA="772d08fbfbff6be0a53f351adf81a83b2b1e88ede8ddd41acf6aaa2cd03d3f0f"
readonly ACCEPTED_VERIFY_SHA="5161baa37827d0729bb4c7af4ce110da50e539b37daa14469110508a83c75c1d"
readonly ACCEPTED_EVIDENCE_SHA="b1f9065b8c2ec0de29a289a3e38850e3c3683e601eeb65ef4f7f8e2bb55e6982"
readonly P3_SHA="941ae576a67090a88815974648ea1c552bb1bf033ca100fdb3a286c4da66c0f5"
readonly FIRING_SHA="46210dddc66714c3d8d226711510cf8421774214016c508c72a833a05370f6b5"
readonly NORMALIZER_SHA="de87f170a560303571f6bb3711f162a7afa3c3737448376cec87b6aca50129c1"
readonly FIXTURE_SHA="3e862710550a19044f573809275ba7ff2e837b72111e9a3298d3d0763555e2be"
readonly ORACLE_TEMPLATE_SHA="9f2100fc75985d90603c7f785422d39de2127a84a5ccff45db37ba4a7548cfac"
readonly NONFIRING_SHA="4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865"
readonly RUNTIME_PROJECTOR_SHA="db4883cc622c0fa2d177467ede498211b8478045734a8d0577ddb0f8b77841ca"
readonly RULE_PROJECTOR_SHA="04d81687ede8cffb70534f405051b53b7e6ca935386350b5e041c61a91eeeb2c"
readonly RUNNER_SHA="b313a0701e05a21a95d2e225eda8ae452ab529a72100715855f49a25b567675f"

readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly TASK="${REPO_ROOT}/spine/rule-applied-trace"
readonly EVIDENCE="${REPO_ROOT}/evidence/r3-g-01-single-rule-applied-trace"
readonly OUTPUT="${1:-${TASK}/build/acceptance}"
readonly CYCLES="${R3_G_01_FULL_CYCLE_COUNT:-3}"
readonly REPAIR_CYCLES="${R3_G_01A_REPAIR_CYCLE_COUNT:-2}"
readonly PORTABLE_SOURCE="repo://spine/rule-applied-trace/fixtures/p3-trace.k"
readonly TRACE_K="${TASK}/src/rule-applied-trace.k"
readonly DRIVER="${TASK}/src/java/org/kframework/kink/trace/RuleAppliedTraceDriver.java"
readonly FIXTURE="${TASK}/fixtures/p3-trace.k"
readonly ORACLE_TEMPLATE="${TASK}/fixtures/source-oracle-template.k"
readonly NONFIRING="${TASK}/fixtures/nonfiring.exp"
readonly P3="${REPO_ROOT}/p3/fixtures/coupled.k"
readonly FIRING="${REPO_ROOT}/p3/fixtures/program.exp"
readonly NORMALIZER="${REPO_ROOT}/investigations/w1-inprocess-adapter/normalize_identity_kore.py"
readonly HOOK_PATCH="${REPO_ROOT}/investigations/r2-g-05-pre-cf-hook-prototype/upstream.patch"
readonly PACKET="${REPO_ROOT}/tasks/wave-3/R3-G-01A-checkout-stable-source-evidence.md"
readonly SEMANTIC_PACKET="${REPO_ROOT}/tasks/wave-3/R3-G-01-single-rule-applied-trace.md"
readonly AUDIT="${REPO_ROOT}/draft/k-in-k-r3-g-01-audit-checkpoint-2026-08-19.md"
readonly ACCEPTED="${REPO_ROOT}/spine/rule-observation"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly FRONTEND_JAR="${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar"
readonly BUILD_ROOT="${OUTPUT}/host"

for tool in bun cmp git java javac javap jq kompile krun patch python3 rg sha256sum; do
  command -v "${tool}" >/dev/null
done
git merge-base --is-ancestor "${ACTIVATION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
[[ "$(git -C "${K_SOURCE}" status --short)" == " M pyk/uv.lock" ]]
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "${K_RELEASE}" >/dev/null
[[ "$(sha256sum "${FRONTEND_JAR}" | awk '{print $1}')" == "${FRONTEND_SHA}" ]]
[[ "$(sha256sum "${HOOK_PATCH}" | awk '{print $1}')" == "${HOOK_PATCH_SHA}" ]]
[[ "$(sha256sum "${PACKET}" | awk '{print $1}')" == "${PACKET_SHA}" ]]
[[ "$(sha256sum "${SEMANTIC_PACKET}" | awk '{print $1}')" == "${SEMANTIC_PACKET_SHA}" ]]
[[ "$(sha256sum "${AUDIT}" | awk '{print $1}')" == "${AUDIT_SHA}" ]]
[[ "$(sha256sum "${ACCEPTED}/src/rule-observation.k" | awk '{print $1}')" == "${ACCEPTED_K_SHA}" ]]
[[ "$(sha256sum "${ACCEPTED}/src/java/org/kframework/kink/observation/RuleObservationDriver.java" | awk '{print $1}')" == "${ACCEPTED_JAVA_SHA}" ]]
[[ "$(sha256sum "${ACCEPTED}/replay.sh" | awk '{print $1}')" == "${ACCEPTED_REPLAY_SHA}" ]]
[[ "$(sha256sum "${ACCEPTED}/run-driver.sh" | awk '{print $1}')" == "${ACCEPTED_RUNNER_SHA}" ]]
[[ "$(sha256sum "${ACCEPTED}/verify.sh" | awk '{print $1}')" == "${ACCEPTED_VERIFY_SHA}" ]]
[[ "$(sha256sum "${REPO_ROOT}/evidence/r2-g-07-single-rule-observation/results.json" | awk '{print $1}')" == "${ACCEPTED_EVIDENCE_SHA}" ]]
[[ "$(sha256sum "${P3}" | awk '{print $1}')" == "${P3_SHA}" ]]
[[ "$(sha256sum "${FIRING}" | awk '{print $1}')" == "${FIRING_SHA}" ]]
[[ "$(sha256sum "${NORMALIZER}" | awk '{print $1}')" == "${NORMALIZER_SHA}" ]]
[[ "$(sha256sum "${FIXTURE}" | awk '{print $1}')" == "${FIXTURE_SHA}" ]]
[[ "$(sha256sum "${ORACLE_TEMPLATE}" | awk '{print $1}')" == "${ORACLE_TEMPLATE_SHA}" ]]
[[ "$(sha256sum "${NONFIRING}" | awk '{print $1}')" == "${NONFIRING_SHA}" ]]
[[ "$(sha256sum "${TASK}/project_runtime.py" | awk '{print $1}')" == "${RUNTIME_PROJECTOR_SHA}" ]]
[[ "$(sha256sum "${TASK}/project_rule_kore.py" | awk '{print $1}')" == "${RULE_PROJECTOR_SHA}" ]]
[[ "$(sha256sum "${TASK}/run-driver.sh" | awk '{print $1}')" == "${RUNNER_SHA}" ]]
[[ "${CYCLES}" == "3" ]]
[[ "${REPAIR_CYCLES}" == "2" ]]
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
javac -encoding UTF-8 -cp "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  -d "${BUILD_ROOT}/driver-classes" "${DRIVER}" \
  >"${OUTPUT}/logs/driver-javac.stdout" 2>"${OUTPUT}/logs/driver-javac.stderr"
java -cp "${BUILD_ROOT}/driver-classes:${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  org.kframework.kink.trace.RuleAppliedTraceDriver --parser-self-test \
  >"${OUTPUT}/logs/parser-self-test.stdout" 2>"${OUTPUT}/logs/parser-self-test.stderr"

kompile "${TRACE_K}" --backend llvm \
  --main-module KINK-RULE-TRACE --syntax-module KINK-RULE-TRACE-SYNTAX \
  --output-definition "${OUTPUT}/trace-k-kompiled" \
  >"${OUTPUT}/logs/trace-k.stdout" 2>"${OUTPUT}/logs/trace-k.stderr"
javap -classpath "${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" -p \
  org.kframework.kompile.Kompile >"${OUTPUT}/api/Kompile.signatures"
grep -Fq 'Function<org.kframework.definition.Definition, org.kframework.definition.Definition>, java.util.function.Function<org.kframework.definition.Definition, org.kframework.definition.Definition>' \
  "${OUTPUT}/api/Kompile.signatures"
if rg -n '"(bump|state|trace|<trace>|ListItem|_List_|bump-state|R3-G-01-P3-TRACE)"' "${DRIVER}"; then
  printf 'fixture-selection literal crossed into Java\n' >&2
  exit 1
fi
readonly EVENT_LITERAL_PATTERN='"[^"\n]*(ruleApplied|ruleOrigin)[^"\n]*"'
if rg -n "${EVENT_LITERAL_PATTERN}" "${DRIVER}"; then
  printf 'event-constructor literal crossed into Java\n' >&2
  exit 1
fi
for prohibited in \
    '"ruleApplied"' '"prefix-ruleApplied"' '"ruleApplied-suffix"' \
    '"ruleOrigin"' '"prefix-ruleOrigin"' '"ruleOrigin-suffix"'; do
  printf '%s\n' "${prohibited}" | rg -q "${EVENT_LITERAL_PATTERN}"
done
for literal in '"bump"' '"<state>"' '"trace"' '"ruleApplied' '"ruleOrigin' '"_List_"' '"ListItem"'; do
  grep -Fq "${literal}" "${TRACE_K}"
done

kompile "${FIXTURE}" --backend haskell --emit-json \
  --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
  --output-definition "${OUTPUT}/baseline" \
  >"${OUTPUT}/logs/baseline.stdout" 2>"${OUTPUT}/logs/baseline.stderr"
kompile "${P3}" --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT}/p3-oracle" \
  >"${OUTPUT}/logs/p3-oracle.stdout" 2>"${OUTPUT}/logs/p3-oracle.stderr"

run_positive() {
  local mode="$1" output="$2"
  R3_G_01_BUILD_ROOT="${BUILD_ROOT}" R3_G_01_MODE="${mode}" \
  R3_G_01_PORTABLE_SOURCE="${PORTABLE_SOURCE}" \
  R3_G_01_RECORD="${OUTPUT}/records/${output}.json" \
  R3_G_01_TRACE_K_DEFINITION="${OUTPUT}/trace-k-kompiled" \
    "${TASK}/run-driver.sh" "${FIXTURE}" --backend haskell --emit-json \
      --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
}
run_positive positive-a trace-a
run_positive positive-b trace-b

python3 - "${ORACLE_TEMPLATE}" "${OUTPUT}/generated/source-oracle.k" \
    "${OUTPUT}/records/trace-a.json" <<'PY'
import json
import sys
from pathlib import Path

template, output, record = map(Path, sys.argv[1:])
data = json.loads(record.read_text(encoding="utf-8"))
text = template.read_text(encoding="utf-8")
for marker, field in (
    ("@ID@", "ruleTargetLineage"),
    ("@LABEL@", "ruleTargetLabel"),
    ("@MODULE@", "ruleTargetModule"),
    ("@SOURCE@", "ruleTargetSource"),
    ("@LOCATION@", "ruleTargetLocation"),
):
    text = text.replace(marker, json.dumps(data[field]))
output.write_text(text, encoding="utf-8")
PY
kompile "${OUTPUT}/generated/source-oracle.k" --backend haskell --emit-json \
  --main-module R3-G-01-SOURCE-ORACLE \
  --syntax-module R3-G-01-SOURCE-ORACLE-SYNTAX \
  --output-definition "${OUTPUT}/source-oracle" \
  >"${OUTPUT}/logs/source-oracle.stdout" 2>"${OUTPUT}/logs/source-oracle.stderr"

run_negative() {
  local mode="$1" output="$2"
  set +e
  R3_G_01_BUILD_ROOT="${BUILD_ROOT}" R3_G_01_MODE="${mode}" \
  R3_G_01_PORTABLE_SOURCE="${PORTABLE_SOURCE}" \
  R3_G_01_RECORD="${OUTPUT}/records/${output}.json" \
  R3_G_01_TRACE_K_DEFINITION="${OUTPUT}/trace-k-kompiled" \
    "${TASK}/run-driver.sh" "${FIXTURE}" --backend haskell \
      --main-module R3-G-01-P3-TRACE --syntax-module R3-G-01-P3-TRACE-SYNTAX \
      --output-definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/logs/${output}.stdout" 2>"${OUTPUT}/logs/${output}.stderr"
  local exit_code=$?
  set -e
  [[ ${exit_code} -ne 0 ]]
  printf '%s\n' "${exit_code}" >"${OUTPUT}/logs/${output}.exit"
}
run_negative stale-target-content negative-stale-content
run_negative stale-target-provenance negative-stale-provenance
run_negative zero-target negative-zero
run_negative duplicate-target negative-duplicate
run_negative unsupported-path negative-path
run_negative missing-cell-metadata negative-missing-cell
run_negative ambiguous-cell-metadata negative-ambiguous-cell
run_negative missing-constructor-metadata negative-missing-constructor
run_negative ambiguous-constructor-metadata negative-ambiguous-constructor
run_negative unknown-constructor negative-unknown-constructor
run_negative sort-invalid negative-sort
run_negative variable-collision negative-variable
run_negative conflict-existing negative-conflict
run_negative false-already-present negative-false-already
run_negative unsupported-shape negative-unsupported-shape

for output in baseline p3-oracle trace-a trace-b source-oracle; do
  for program in firing nonfiring; do
    input="${FIRING}"
    [[ "${program}" == nonfiring ]] && input="${NONFIRING}"
    krun "${input}" --definition "${OUTPUT}/${output}" \
      >"${OUTPUT}/runtime/${output}-${program}.out" \
      2>"${OUTPUT}/runtime/${output}-${program}.err"
    python3 "${TASK}/project_runtime.py" \
      "${OUTPUT}/runtime/${output}-${program}.out" \
      "${OUTPUT}/projections/${output}-${program}.json"
  done
done

for output in trace-a trace-b; do
  python3 "${NORMALIZER}" \
    "${OUTPUT}/${output}/definition.kore" \
    "${OUTPUT}/projections/${output}-definition.kore"
  python3 "${TASK}/project_rule_kore.py" --label bump-state \
    "${OUTPUT}/${output}/definition.kore" \
    "${OUTPUT}/projections/${output}-bump-state.kore"
done
cmp "${OUTPUT}/projections/trace-a-definition.kore" \
  "${OUTPUT}/projections/trace-b-definition.kore"
cmp "${OUTPUT}/projections/trace-a-bump-state.kore" \
  "${OUTPUT}/projections/trace-b-bump-state.kore"
grep -Fq "Lbl'-LT-'trace'-GT-'" \
  "${OUTPUT}/projections/trace-a-bump-state.kore"
grep -Fq "LblruleApplied" "${OUTPUT}/projections/trace-a-bump-state.kore"
for artifact in syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT}/trace-a/${artifact}" "${OUTPUT}/trace-b/${artifact}"
  cmp "${OUTPUT}/baseline/${artifact}" "${OUTPUT}/trace-a/${artifact}"
done

for program in firing nonfiring; do
  cmp "${OUTPUT}/runtime/trace-a-${program}.out" \
    "${OUTPUT}/runtime/trace-b-${program}.out"
  cmp "${OUTPUT}/runtime/trace-a-${program}.out" \
    "${OUTPUT}/runtime/source-oracle-${program}.out"
  cmp "${OUTPUT}/projections/trace-a-${program}.json" \
    "${OUTPUT}/projections/source-oracle-${program}.json"
  for output in baseline p3-oracle trace-a; do
    python3 "${TASK}/project_runtime.py" --erase-trace \
      "${OUTPUT}/runtime/${output}-${program}.out" \
      "${OUTPUT}/projections/${output}-${program}-erased.json"
  done
  cmp "${OUTPUT}/projections/baseline-${program}-erased.json" \
    "${OUTPUT}/projections/trace-a-${program}-erased.json"
  cmp "${OUTPUT}/projections/p3-oracle-${program}-erased.json" \
    "${OUTPUT}/projections/trace-a-${program}-erased.json"
done

jq -e '.k=="1" and .state=="2" and (.trace|length)==1
  and .trace[0].kind=="RuleApplied"' \
  "${OUTPUT}/projections/trace-a-firing.json" >/dev/null
jq -e '. == {k:"1",state:"1",trace:[]}' \
  "${OUTPUT}/projections/trace-a-nonfiring.json" >/dev/null
jq -e --slurpfile record "${OUTPUT}/records/trace-a.json" '
  .trace[0].origin == {
    id:$record[0].ruleTargetLineage,
    label:$record[0].ruleTargetLabel,
    module:$record[0].ruleTargetModule,
    source:$record[0].ruleTargetSource,
    location:$record[0].ruleTargetLocation
  }' "${OUTPUT}/projections/trace-a-firing.json" >/dev/null
fixture_source="$(readlink -f "${FIXTURE}")"
jq -e --arg fixtureSource "${fixture_source}" --arg portableSource "${PORTABLE_SOURCE}" '
  .ruleTargetSource == $fixtureSource
  and (.ruleTargetSource | startswith("/"))
  and .portableEvidenceProjected
  and .portableRuleOrderingValidated
  and .portableTermMetadataRederived
  and .portableSource == $portableSource
  and .portableRuleTargetSource == $portableSource
  and .portableRuleTargetLineage != .ruleTargetLineage
  and .portableRuleBeforeDefinition != ""
  and .portableRuleAfterDefinition != ""
  and .portableRuleTargetContentBefore != ""
  and .portableRuleTargetContentAfter != ""
  and .portableRuleTargetBodyBefore != ""
  and .portableRuleTargetBodyAfter != ""
  and .portableRuleTargetBodyBefore != .ruleTargetBodyBefore
  and .portableRuleTargetRequires != .ruleTargetRequires
  and .portableRuleTargetEnsures != .ruleTargetEnsures
  and .portableRuleRequestFingerprintPass1 != ""
  and .portableRuleRequestFingerprintPass2 != ""
  and .portableRuleResponseFingerprintPass1 != ""
  and .portableRuleResponseFingerprintPass2 != ""
  and .portableRuleOperationCanonicalPass1 != ""
  and .portableRuleOperationCanonicalPass2 != ""
' "${OUTPUT}/records/trace-a.json" >/dev/null

for record in trace-a trace-b; do
  jq -e '
    .status=="accepted" and .contract=="KRuleAppliedTrace-v1"
    and .postCfAdapterInvocations==1 and .postCfConstructed
    and .ruleKInvocationsPass1==1 and .ruleKInvocationsPass2==1
    and .ruleCandidateCountPass1==1 and .ruleStatusPass1=="apply"
    and .ruleCandidateCountPass2==1 and .ruleStatusPass2=="already-present"
    and .ruleValidatedOperationCount==1 and .ruleApplicationCount==1
    and .ruleChangedRuleCount==1 and .ruleAlreadyPresentValidatedCount==1
    and .ruleSecondSameReference and .ruleTransformedDefinitionReturned
    and .ruleSecondPassSameReference and .ruleIdentityPreserved
    and .ruleProvenancePreserved and .ruleAttributesPreserved
    and .ruleConditionsPreserved and .ruleOriginalNodesPreserved
    and .ruleBeforeDefinition != .ruleAfterDefinition
    and .ruleTargetContentBefore != .ruleTargetContentAfter
    and .ruleTargetBodyBefore != .ruleTargetBodyAfter
    and .ruleTargetRequires != "" and .ruleTargetEnsures != ""
    and .ruleTargetAttributes != ""
    and .generatedCellBodySort=="List" and .backendConstructed
  ' "${OUTPUT}/records/${record}.json" >/dev/null
done
jq -e --slurp '
  .[0].ruleRequestFingerprintPass1 == .[1].ruleRequestFingerprintPass1
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
  and ((.[0] | with_entries(select(.key | startswith("portable"))))
    == (.[1] | with_entries(select(.key | startswith("portable")))))
' "${OUTPUT}/records/trace-a.json" "${OUTPUT}/records/trace-b.json" >/dev/null

python3 - "${OUTPUT}/records/trace-a.json" \
    "${OUTPUT}/projections/trace-a-firing.json" \
    "${OUTPUT}/projections/trace-a-nonfiring.json" \
    "${OUTPUT}/generated/source-oracle.k" \
    "${OUTPUT}/projections/portable-firing.json" \
    "${OUTPUT}/projections/portable-nonfiring.json" \
    "${OUTPUT}/generated/portable-source-oracle.k" <<'PY'
import json
import sys
from pathlib import Path

record_path, firing_path, nonfiring_path, oracle_path, portable_firing_path, portable_nonfiring_path, portable_oracle_path = map(Path, sys.argv[1:])
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
    raise SystemExit("raw runtime origin was not the exact selected official provenance")
firing["trace"][0]["origin"] = {
    "id": record["portableRuleTargetLineage"],
    "label": record["portableRuleTargetLabel"],
    "location": record["portableRuleTargetLocation"],
    "module": record["portableRuleTargetModule"],
    "source": record["portableRuleTargetSource"],
}
portable_firing_path.write_text(json.dumps(firing, sort_keys=True, indent=2) + "\n", encoding="utf-8")
portable_nonfiring_path.write_text(json.dumps(nonfiring, sort_keys=True, indent=2) + "\n", encoding="utf-8")
oracle = oracle_path.read_text(encoding="utf-8")
oracle = oracle.replace(record["ruleTargetLineage"], record["portableRuleTargetLineage"])
oracle = oracle.replace(record["ruleTargetSource"], record["portableRuleTargetSource"])
portable_oracle_path.write_text(oracle, encoding="utf-8")
PY
! rg -F "${REPO_ROOT}" \
  "${OUTPUT}/projections/portable-firing.json" \
  "${OUTPUT}/projections/portable-nonfiring.json" \
  "${OUTPUT}/generated/portable-source-oracle.k"

declare -A classes=(
  [negative-stale-content]=stale-precondition
  [negative-stale-provenance]=stale-precondition
  [negative-zero]=k-selection
  [negative-duplicate]=k-selection
  [negative-path]=path-operation
  [negative-missing-cell]=generated-metadata
  [negative-ambiguous-cell]=generated-metadata
  [negative-missing-constructor]=constructor-metadata
  [negative-ambiguous-constructor]=constructor-metadata
  [negative-unknown-constructor]=constructor-metadata
  [negative-sort]=term-sort
  [negative-variable]=fresh-variable
  [negative-conflict]=conflict
  [negative-false-already]=envelope
  [negative-unsupported-shape]=conservative-shape-rejection
)
for record in "${!classes[@]}"; do
  jq -e --arg class "${classes[$record]}" '
    .status=="rejected" and .classification==$class
    and .postCfAdapterInvocations==1 and .ruleApplicationCount==0
    and (.ruleTransformedDefinitionReturned|not)
    and (.backendConstructed|not)
  ' "${OUTPUT}/records/${record}.json" >/dev/null
  for artifact in allRules.txt backend.txt compiled.bin compiled.json compiled.txt \
      definition.kore haskellDefinition.bin macros.kore syntaxDefinition.kore; do
    [[ ! -e "${OUTPUT}/${record}/${artifact}" ]]
  done
done
jq -e '.ruleCandidateCountPass1==0' \
  "${OUTPUT}/records/negative-zero.json" >/dev/null
jq -e '.ruleCandidateCountPass1==2' \
  "${OUTPUT}/records/negative-duplicate.json" >/dev/null
jq -e '.ruleInputMutationCount==1' \
  "${OUTPUT}/records/negative-missing-cell.json" \
  "${OUTPUT}/records/negative-ambiguous-cell.json" \
  "${OUTPUT}/records/negative-missing-constructor.json" \
  "${OUTPUT}/records/negative-ambiguous-constructor.json" >/dev/null
jq -e '.ruleInputMutationCount==1 and .ruleKInvocationsPass2==1' \
  "${OUTPUT}/records/negative-conflict.json" \
  "${OUTPUT}/records/negative-unsupported-shape.json" >/dev/null

jq -s '
  map({
    key:.mode,
    value:{
      classification,
      ruleCandidateCountPass1,
      ruleCandidateCountPass2,
      ruleInputMutationCount,
      ruleApplicationCount,
      ruleTransformedDefinitionReturned,
      backendConstructed,
      backendArtifactsEmitted:false
    }
  }) | from_entries
' "${OUTPUT}"/records/negative-*.json >"${OUTPUT}/projections/negatives.json"

{
  sha256sum "${TRACE_K}" "${DRIVER}" "${TASK}/replay.sh" \
    "${TASK}/run-driver.sh" "${TASK}/verify.sh" \
    "${TASK}/project_runtime.py" "${TASK}/project_rule_kore.py"
  sha256sum "${FIXTURE}" "${ORACLE_TEMPLATE}" "${NONFIRING}" \
    "${OUTPUT}/generated/source-oracle.k"
  sha256sum "${BUILD_ROOT}/overlay/classes/org/kframework/kompile/"{DefinitionParsing,Kompile}.class
  sha256sum "${OUTPUT}"/records/*.json "${OUTPUT}"/runtime/*.out \
    "${OUTPUT}"/projections/*.json
} >"${OUTPUT}/SHA256SUMS"

jq -n \
  --arg activation "${ACTIVATION}" \
  --arg importedPrototype "${IMPORTED_PROTOTYPE}" \
  --arg startingRevision "${STARTING_REVISION}" \
  --arg kCommit "${K_COMMIT}" --arg kRelease "${K_RELEASE}" \
  --arg kSource "${K_SOURCE}" --arg kStatus "$(git -C "${K_SOURCE}" status --short)" \
  --arg kompile "${KOMPILE_BIN}" --arg frontendSha "${FRONTEND_SHA}" \
  --arg hookPatchSha "${HOOK_PATCH_SHA}" --arg packetSha "${PACKET_SHA}" \
  --arg semanticPacketSha "${SEMANTIC_PACKET_SHA}" --arg auditSha "${AUDIT_SHA}" \
  --arg acceptedKSha "${ACCEPTED_K_SHA}" --arg acceptedJavaSha "${ACCEPTED_JAVA_SHA}" \
  --arg acceptedReplaySha "${ACCEPTED_REPLAY_SHA}" --arg acceptedRunnerSha "${ACCEPTED_RUNNER_SHA}" \
  --arg acceptedVerifySha "${ACCEPTED_VERIFY_SHA}" --arg acceptedEvidenceSha "${ACCEPTED_EVIDENCE_SHA}" \
  --arg traceKSha "$(sha256sum "${TRACE_K}"|awk '{print $1}')" \
  --arg driverSha "$(sha256sum "${DRIVER}"|awk '{print $1}')" \
  --arg replaySha "$(sha256sum "${TASK}/replay.sh"|awk '{print $1}')" \
  --arg runnerSha "$(sha256sum "${TASK}/run-driver.sh"|awk '{print $1}')" \
  --arg verifierSha "$(sha256sum "${TASK}/verify.sh"|awk '{print $1}')" \
  --arg runtimeSha "${RUNTIME_PROJECTOR_SHA}" --arg ruleProjectorSha "${RULE_PROJECTOR_SHA}" \
  --arg fixtureSha "${FIXTURE_SHA}" --arg oracleTemplateSha "${ORACLE_TEMPLATE_SHA}" \
  --arg generatedOracleSha "$(sha256sum "${OUTPUT}/generated/portable-source-oracle.k"|awk '{print $1}')" \
  --arg nonfiringSha "${NONFIRING_SHA}" --arg p3Sha "${P3_SHA}" \
  --arg firingSha "${FIRING_SHA}" --arg normalizerSha "${NORMALIZER_SHA}" \
  --arg portableSource "${PORTABLE_SOURCE}" \
  --argjson cycles "${CYCLES}" \
  --argjson repairCycles "${REPAIR_CYCLES}" \
  --slurpfile a "${OUTPUT}/records/trace-a.json" \
  --slurpfile b "${OUTPUT}/records/trace-b.json" \
  --slurpfile firing "${OUTPUT}/projections/portable-firing.json" \
  --slurpfile nonfiring "${OUTPUT}/projections/portable-nonfiring.json" \
  --slurpfile negatives "${OUTPUT}/projections/negatives.json" \
  '{
    schemaVersion:1,
    task:"R3-G-01A-checkout-stable-source-evidence",
    verdict:"pass",
    contract:"KRuleAppliedTrace-v1",
    semanticFullCycleCount:$cycles,
    repairFullCycleCount:$repairCycles,
    activationRevision:$activation,
    importedPrototypeRevision:$importedPrototype,
    actualStartingRevision:$startingRevision,
    pin:{
      kRelease:$kRelease,kCommit:$kCommit,kSource:$kSource,kSourceStatus:$kStatus,
      resolvedKompile:$kompile,frontendJarSha256:$frontendSha,
      hookPatchSha256:$hookPatchSha,repairPacketSha256:$packetSha,
      semanticPacketSha256:$semanticPacketSha,auditCheckpointSha256:$auditSha,
      acceptedRuleObservation:{
        kSemantics:$acceptedKSha,javaHost:$acceptedJavaSha,replay:$acceptedReplaySha,
        runner:$acceptedRunnerSha,verifier:$acceptedVerifySha,evidence:$acceptedEvidenceSha
      },
      environment:{LC_ALL:"C",LANG:"C",TZ:"UTC"}
    },
    taskSourceSha256:{
      kSemantics:$traceKSha,javaHost:$driverSha,replay:$replaySha,runner:$runnerSha,
      verifier:$verifierSha,runtimeProjector:$runtimeSha,ruleProjector:$ruleProjectorSha,
      traceFixture:$fixtureSha,sourceOracleTemplate:$oracleTemplateSha,
      portableGeneratedSourceOracle:$generatedOracleSha,nonfiringProgram:$nonfiringSha,
      p3Definition:$p3Sha,firingProgram:$firingSha,identityNormalizer:$normalizerSha
    },
    contractShape:{
      transformation:"p3-trace-bump-rule-applied@1",
      operation:"appendGeneratedCellTerm",
      before:"one fresh typed variable",
      after:"typed list append of the before variable and one singleton RuleApplied event",
      termConstructors:["tApply","tToken","tVariable"],
      metadata:["generated cell","production","sort","subsort"],
      provenanceWitnessPaths:["lineage","label","module","source","location"]
    },
    ownership:{
      k:[
        "structural coupled transition selection","complete target and provenance",
        "generated trace cell and fresh variable","every typed constructor and token placement",
        "parent and provenance witness paths","apply/already/conflict and cardinality"
      ],
      java:[
        "complete post-CF projection","canonical exact-result parsing and fingerprints",
        "declared metadata/sort/path/freshness validation","independent payload equality validation",
        "official constructor assembly and immutable ancestor/rule/module/definition rebuild"
      ]
    },
    provenanceInvariant:{
      runtimeTruth:"the real event carries the selected official rule exact run-local Source and its source-derived lineage; the host validates equality of lineage, label, module, source, and location before backend acceptance",
      portableEvidence:"only after apply/already-present and exact raw payload validation, evidence substitutes a repository-logical source, rederives every primary lineage, and recomputes all dependent canonical terms and fingerprints",
      rawOfficialSourceOmittedFromCommittedEvidence:true,
      exactRawFiveFieldEqualityValidated:true,
      ordinarySourceOracleComparedAtRawRuntime:true
    },
    portableEvidence:{
      representation:"post-validation logical provenance projection",
      method:"source-aware typed term/meta re-encoding plus structural TraceResult/TermSpec/ProductionSpec translation followed by SHA-256 rederivation",
      logicalSource:$portableSource,
      isRawOfficialSource:false,
      ruleOrdering:"portable lineage order, independent of raw source-derived lineage",
      structuralResultTranslation:true,
      termMetadataRederived:true,
      covers:[
        "source","all primary-rule lineages",
        "source-aware typed term metadata, bodies, conditions, content and attributes",
        "whole definition","request","result","operation",
        "generated production and metadata","ordinary-source oracle","runtime payload"
      ]
    },
    application:($a[0]|{
      postCfAdapterInvocations,ruleKInvocationsPass1,ruleKInvocationsPass2,
      ruleRequestFingerprintPass1:.portableRuleRequestFingerprintPass1,
      ruleResponseFingerprintPass1:.portableRuleResponseFingerprintPass1,
      ruleRequestFingerprintPass2:.portableRuleRequestFingerprintPass2,
      ruleResponseFingerprintPass2:.portableRuleResponseFingerprintPass2,
      ruleCandidateCountPass1,ruleCandidateCountPass2,ruleStatusPass1,ruleStatusPass2,
      ruleTargetLineage:.portableRuleTargetLineage,
      ruleTargetModule:.portableRuleTargetModule,
      ruleTargetLabel:.portableRuleTargetLabel,
      ruleTargetSource:.portableRuleTargetSource,
      ruleTargetLocation:.portableRuleTargetLocation,
      ruleTargetRequires:.portableRuleTargetRequires,
      ruleTargetEnsures:.portableRuleTargetEnsures,
      ruleTargetAttributes:.portableRuleTargetAttributes,
      ruleTargetContentBefore:.portableRuleTargetContentBefore,
      ruleTargetContentAfter:.portableRuleTargetContentAfter,
      ruleTargetBodyBefore:.portableRuleTargetBodyBefore,
      ruleTargetBodyAfter:.portableRuleTargetBodyAfter,
      ruleBeforeDefinition:.portableRuleBeforeDefinition,
      ruleAfterDefinition:.portableRuleAfterDefinition,
      ruleOperationCanonicalPass1:.portableRuleOperationCanonicalPass1,
      ruleOperationCanonicalPass2:.portableRuleOperationCanonicalPass2,
      ruleResultCanonicalFingerprintPass1:.portableRuleResultCanonicalFingerprintPass1,
      ruleResultCanonicalFingerprintPass2:.portableRuleResultCanonicalFingerprintPass2,
      ruleValidatedOperationCount,ruleApplicationCount,ruleChangedRuleCount,
      ruleAlreadyPresentValidatedCount,ruleSecondSameReference,
      ruleIdentityPreserved,ruleProvenancePreserved,ruleAttributesPreserved,
      ruleConditionsPreserved,ruleOriginalNodesPreserved,
      generatedCellName,generatedCellLabel,generatedCellSort,generatedCellBodySort,
      generatedCellProductionFingerprint:.portableGeneratedCellProductionFingerprint,
      generatedCellMetadataFingerprint:.portableGeneratedCellMetadataFingerprint,
      backendConstructed
    }),
    eventPayloadPortable:$firing[0].trace[0],
    idempotence:{
      statusPass2:$a[0].ruleStatusPass2,candidateCountPass2:$a[0].ruleCandidateCountPass2,
      validatedCount:$a[0].ruleAlreadyPresentValidatedCount,
      applications:$a[0].ruleApplicationCount,sameReference:$a[0].ruleSecondSameReference
    },
    repeat:{
      stable:true,requestAndResultFingerprints:true,normalizedFullKore:true,
      focusedRuleKore:true,syntaxKore:true,macros:true,eventPayload:true,bothRuntimes:true
    },
    oracles:{
      firingRuntimePortable:$firing[0],nonfiringRuntimePortable:$nonfiring[0],
      firingErasureEqualsBaselineAndP3:true,
      nonfiringErasureEqualsBaselineAndP3:true,
      ordinarySourceFullRuntimeEqual:true,
      syntaxAndMacrosEqualUninstrumentedTraceFixture:true,
      exactResultParserRejectsNoncanonicalResidualMultipleUnknown:true
    },
    negatives:($negatives[0] + {
      "exact-result-encodings":{
        classification:"envelope",ruleCandidateCountPass1:0,ruleCandidateCountPass2:0,
        ruleInputMutationCount:0,ruleApplicationCount:0,
        ruleTransformedDefinitionReturned:false,backendConstructed:false,
        backendArtifactsEmitted:false
      }
    }),
    limitations:[
      "one structurally selected primary-source rule and one concrete event append",
      "conservativity proven only for the firing and non-firing concrete programs",
      "no symbolic branch-isolation or absence claim",
      "no backend-independent event claim, matcher, monitor, corpus, multi-rule or domain-event semantics"
    ],
    packetAmbiguity:"none requiring a split",
    recommendedNextPacket:"compose K-authored trace configuration with this stable event/append contract without adding a second host boundary"
  }' >"${OUTPUT}/results.json"

cat >"${OUTPUT}/report.md" <<'EOF'
# R3-G-01A checkout-stable RuleApplied evidence

Status: pass on 19 August 2026 against K v7.1.337 at
`4a46d1231473b599c699160132fd6e76a5c46406`.

## Acceptance

Run from a checkout without pre-existing acceptance output:

```sh
bun run r3:g:rule-applied-trace
```

The replay compiles the task-owned, uninstrumented trace fixture through
ordinary official K, projects its post-CF definition through the sole
`KRuleAppliedTrace-v1` contract, and continues through unchanged lowering and
the pinned Haskell backend. The semantic packet remains frozen at three
substantive full-oracle cycles. This checkout-stability repair used two
substantive full-oracle cycles.

## Runtime truth and portable evidence

The real runtime event still contains the selected official rule's absolute,
run-local `Source` and the lineage derived from that exact source. Before
backend acceptance, Java independently validates exact equality of all five
origin fields: lineage, label, module, source, and location. The independently
compiled ordinary-source oracle uses those same raw values, and its two full
runtimes are compared byte-for-byte with the transformed runtimes.

Only after `apply`, `already-present`, and exact raw-payload validation does
the replay produce committed evidence. That representation uses
`repo://spine/rule-applied-trace/fixtures/p3-trace.k` as an explicit logical
source identity; it is not the raw official `Source`. The projection re-encodes
and re-hashes all primary-rule lineages, source-aware typed term metadata,
rule bodies/conditions/content/attributes,
whole-definition fingerprints, request/result fingerprints, canonical
operations, generated production/metadata fingerprints, the ordinary-source
oracle, and runtime payload. No raw checkout-derived digest is relabeled as a
portable digest.

## Result

- K structurally selected the one `bump-state` transition and authored the
  complete target, path, trace-cell name, fresh typed variable, typed list
  append, singleton event, origin constructor, all five payload placements,
  and `apply`/`already-present`/conflict decisions.
- The payload is one `RuleApplied` origin containing the selected rule lineage,
  label, module, source, and location. Java contains none of the fixture,
  constructor, list-label, cell, target, or payload-order selection literals.
  The replay rejects bare, suffixed, or prefixed `ruleApplied` and `ruleOrigin`
  Java string literals.
- Java resolved only exact projected generated-cell, production, sort, and
  subsort descriptors, validated typed term and provenance witness paths, and
  immutably rebuilt one rule. Lineage, provenance, attributes, conditions, and
  every original body node were preserved.
- Reprojection returned one `already-present` candidate. Independent host
  validation found exactly one equal update, performed zero further
  applications, and retained the same instrumented definition reference.
- The firing program ended at `<k> 1`, `<state> 2` with exactly one event; the
  non-firing integer ended at `<k> 1`, `<state> 1` with `.List`. Erasure matches
  both the uninstrumented trace fixture and accepted P3 program state.
- Both full runtimes match an independently compiled ordinary-source oracle.
  The fresh repeat has stable request/result fingerprints, full and focused
  normalized Kore, syntax Kore, macros, event payload, and both runtimes.
- Stale content/provenance, zero/duplicate targets, invalid paths,
  missing/ambiguous cell and constructor metadata, unknown constructors,
  incompatible sorts, variable collisions, conflicting updates, false
  `already-present`, unsupported bodies, and malformed exact results all fail
  closed with zero applications and no known backend artifacts.

## Boundary

This proves only one event and the two concrete paths. It does not prove
symbolic branch isolation or absence, backend-independent rule application, or
general event semantics. It adds no matcher, monitor, temporal language,
corpus result, symbolic path, multi-rule facility, or domain event. There was
no ambiguity requiring a split.

The recommended follow-on is the K-authored trace-configuration composition
packet, reusing this stable event/append contract without a second host
boundary.
EOF

! rg -F "${REPO_ROOT}" "${OUTPUT}/results.json" "${OUTPUT}/report.md"
if [[ -f "${EVIDENCE}/results.json" ]]; then
  cmp "${EVIDENCE}/results.json" "${OUTPUT}/results.json"
  cmp "${EVIDENCE}/report.md" "${OUTPUT}/report.md"
fi
printf 'R3-G-01A checkout-stable RuleApplied evidence replay: pass\n'
