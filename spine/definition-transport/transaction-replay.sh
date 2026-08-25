#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION_REVISION="21b05ed5d9c1691e439a03bb4f6500be6d75e28a"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly OUTPUT_ROOT="${1:-${REPO_ROOT}/spine/definition-transport/build/transaction-replay}"
readonly SPINE="${REPO_ROOT}/spine/definition-transport"
readonly DRIVER="${SPINE}/run-driver.sh"
readonly DRIVER_SOURCE="${SPINE}/src/java/org/kframework/kink/transport/DefinitionTransportDriver.java"
readonly TRANSPORT_SOURCE="${SPINE}/src/definition-transport.k"
readonly PATCH_REPLAY="${SPINE}/patch-replay.sh"
readonly TRANSACTION_REPLAY_SOURCE="${SPINE}/transaction-replay.sh"
readonly NORMALIZER="${SPINE}/normalize_start_kore.py"
readonly ADD_FIXTURE="${SPINE}/fixtures/add-values.exp"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"

for tool in bun git java javac jq kompile krun python3 sha256sum; do
  command -v "${tool}" >/dev/null
done
git merge-base --is-ancestor "${ACTIVATION_REVISION}" HEAD
[[ "${KOMPILE_BIN}" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "v7.1.337" >/dev/null
[[ -f "${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar" ]]
[[ ! -e "${OUTPUT_ROOT}" ]]

export LC_ALL=C
export LANG=C
export TZ=UTC
while IFS= read -r tool_bin; do
  PATH="${tool_bin}:${PATH}"
done < <(sed -n "s/^PATH='\([^']*\/bin\)'.*/\1/p" "${KOMPILE_BIN}")
PATH="${K_ROOT}/bin:${PATH}"
LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${K_ROOT}/lib/kframework/native/linux64"
export PATH LD_LIBRARY_PATH

cd "${REPO_ROOT}"
mkdir -p \
  "${OUTPUT_ROOT}/logs" \
  "${OUTPUT_ROOT}/records" \
  "${OUTPUT_ROOT}/runtime" \
  "${OUTPUT_ROOT}/projections"

# Accumulated R2-G-02 suite, including the full R2-G-01 replay, in fresh output.
bash "${PATCH_REPLAY}" "${OUTPUT_ROOT}/r2-g-02" \
  >"${OUTPUT_ROOT}/logs/r2-g-02.stdout" \
  2>"${OUTPUT_ROOT}/logs/r2-g-02.stderr"
readonly TRANSPORT_DEFINITION="${OUTPUT_ROOT}/r2-g-02/identity/transport-kompiled"
readonly P3_BASELINE="${OUTPUT_ROOT}/r2-g-02/identity/p3-baseline"
readonly P3_V1_PATCH="${OUTPUT_ROOT}/r2-g-02/p3-patch"

run_transaction() {
  local mode="$1"
  local name="$2"
  KINK_TRANSPORT_MODE="${mode}" \
  KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/${name}.json" \
  KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
    "${DRIVER}" p3/fixtures/coupled.k \
      --backend haskell \
      --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
      --output-definition "${OUTPUT_ROOT}/${name}" \
      >"${OUTPUT_ROOT}/logs/${name}.stdout" \
      2>"${OUTPUT_ROOT}/logs/${name}.stderr"
}

run_transaction transaction p3-transaction
run_transaction transaction p3-transaction-repeat

krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-transaction" \
  >"${OUTPUT_ROOT}/runtime/p3-transaction-start.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-transaction-start.err"
krun "${ADD_FIXTURE}" --definition "${P3_BASELINE}" \
  >"${OUTPUT_ROOT}/runtime/p3-baseline-add.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-baseline-add.err"
krun "${ADD_FIXTURE}" --definition "${OUTPUT_ROOT}/p3-transaction" \
  >"${OUTPUT_ROOT}/runtime/p3-transaction-add.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-transaction-add.err"
grep -Fq "    0 ~> .K" "${OUTPUT_ROOT}/runtime/p3-transaction-start.out"
grep -Fq "    2" "${OUTPUT_ROOT}/runtime/p3-transaction-start.out"
grep -Fq "    3 ~> .K" "${OUTPUT_ROOT}/runtime/p3-baseline-add.out"
grep -Fq "    2 ~> .K" "${OUTPUT_ROOT}/runtime/p3-transaction-add.out"

cmp "${P3_BASELINE}/syntaxDefinition.kore" \
  "${OUTPUT_ROOT}/p3-transaction/syntaxDefinition.kore"
cmp "${P3_BASELINE}/macros.kore" "${OUTPUT_ROOT}/p3-transaction/macros.kore"

python3 "${NORMALIZER}" \
  "${P3_V1_PATCH}/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-v1-patch-start.kore"
python3 "${NORMALIZER}" \
  "${OUTPUT_ROOT}/p3-transaction/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-transaction-start.kore"
python3 "${NORMALIZER}" \
  "${P3_BASELINE}/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-baseline-add.kore" \
  add-values
python3 "${NORMALIZER}" \
  "${OUTPUT_ROOT}/p3-transaction/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-transaction-add.kore" \
  add-values
cmp \
  "${OUTPUT_ROOT}/projections/p3-v1-patch-start.kore" \
  "${OUTPUT_ROOT}/projections/p3-transaction-start.kore"
! cmp -s \
  "${OUTPUT_ROOT}/projections/p3-baseline-add.kore" \
  "${OUTPUT_ROOT}/projections/p3-transaction-add.kore"
grep -Fq "VarJ" "${OUTPUT_ROOT}/projections/p3-transaction-add.kore"
! grep -Fq "Lbl'UndsPlus'Int'Unds'" \
  "${OUTPUT_ROOT}/projections/p3-transaction-add.kore"

jq -e '
  .status == "accepted"
  and .mode == "transaction"
  and .validationBoundary == "post-k-transaction-pre-apply"
  and (.sameDefinitionReference | not)
  and .transactionCardinality == 1
  and .editCount == 2
  and .validatedEditCount == 2
  and .applicationCount == 2
  and .changedLineageCount == 2
  and .outputConstructed
  and (.transactionFingerprint | test("^[0-9a-f]{64}$"))
  and .transaction.schema == "KDefinitionPatch-v2"
  and .transaction.transformation == "p3-start-and-add-values@1"
  and .transaction.transactionCount == 1
  and .transaction.editCount == 2
  and (.transaction.edits | length) == 2
  and .transaction.edits[0].canonical <= .transaction.edits[1].canonical
  and .transaction.edits[0].targetLineage != .transaction.edits[1].targetLineage
  and ([.transaction.edits[].kind] | all(. == "replaceTermFromInput"))
  and ([.transaction.edits[].targetPathCanonical]
       | all(. == "dPathCons(dRewriteRight,dPathNil)"))
  and ([.transaction.edits[].replacementPathCanonical]
       | index("dPathCons(dRewriteLeft,dPathCons(dApplicationArgument(1),dPathNil))") != null)
  and ([.transaction.edits[].replacementPathCanonical]
       | index("dPathCons(dRewriteRight,dPathCons(dApplicationArgument(1),dPathNil))") != null)
  and .transaction.definitionFingerprint == .before.contentSha256
  and .before.contentSha256 != .after.contentSha256
  and .before.moduleCount == .after.moduleCount
  and .before.localSentenceCount == .after.localSentenceCount
  and (.editOutcomes | length) == 2
  and ([range(0; 2) as $i
        | (.transaction.edits[$i].targetLineage == .editOutcomes[$i].before.lineageSha256)
          and (.transaction.edits[$i].targetContent == .editOutcomes[$i].before.contentSha256)
          and (.transaction.edits[$i].targetBody == .editOutcomes[$i].before.bodySha256)
          and (.editOutcomes[$i].before.lineageSha256 == .editOutcomes[$i].after.lineageSha256)
          and (.editOutcomes[$i].before.sentenceAttSha256 == .editOutcomes[$i].after.sentenceAttSha256)
          and (.editOutcomes[$i].before.requiresSha256 == .editOutcomes[$i].after.requiresSha256)
          and (.editOutcomes[$i].before.ensuresSha256 == .editOutcomes[$i].after.ensuresSha256)
          and (.editOutcomes[$i].before.contentSha256 != .editOutcomes[$i].after.contentSha256)
          and (.editOutcomes[$i].before.bodySha256 != .editOutcomes[$i].after.bodySha256)]
       | all)
' "${OUTPUT_ROOT}/records/p3-transaction.json" >/dev/null

[[ "$(jq -r .transactionFingerprint "${OUTPUT_ROOT}/records/p3-transaction.json")" \
   == "$(jq -r .transactionFingerprint "${OUTPUT_ROOT}/records/p3-transaction-repeat.json")" ]]

set +e
run_transaction transaction-stale-first p3-transaction-stale-first
stale_first_exit=$?
run_transaction transaction-stale-second p3-transaction-stale-second
stale_second_exit=$?
run_transaction transaction-duplicate-target p3-transaction-duplicate-target
duplicate_exit=$?
set -e

[[ "${stale_first_exit}" -ne 0 ]]
[[ "${stale_second_exit}" -ne 0 ]]
[[ "${duplicate_exit}" -ne 0 ]]
jq -e '
  .status == "rejected"
  and .mode == "transaction-stale-first"
  and .validationBoundary == "post-k-transaction-pre-apply"
  and .validatedEditCount == 0
  and .applicationCount == 0
  and .changedLineageCount == 0
  and (.outputConstructed | not)
  and .error == "transaction returned stale target content fingerprint"
  and .transaction.edits[0].targetContent == ("0" * 64)
' "${OUTPUT_ROOT}/records/p3-transaction-stale-first.json" >/dev/null
jq -e '
  .status == "rejected"
  and .mode == "transaction-stale-second"
  and .validationBoundary == "post-k-transaction-pre-apply"
  and .validatedEditCount == 1
  and .applicationCount == 0
  and .changedLineageCount == 0
  and (.outputConstructed | not)
  and .error == "transaction returned stale target content fingerprint"
  and .transaction.edits[1].targetContent == ("0" * 64)
' "${OUTPUT_ROOT}/records/p3-transaction-stale-second.json" >/dev/null
jq -e '
  .status == "rejected"
  and .mode == "transaction-duplicate-target"
  and .validationBoundary == "post-k-transaction-pre-apply"
  and .validatedEditCount == 0
  and .applicationCount == 0
  and .changedLineageCount == 0
  and (.outputConstructed | not)
  and .error == "transaction contains duplicate target lineage"
  and .transaction.edits[0].targetLineage == .transaction.edits[1].targetLineage
' "${OUTPUT_ROOT}/records/p3-transaction-duplicate-target.json" >/dev/null
for rejected in \
  p3-transaction-stale-first \
  p3-transaction-stale-second \
  p3-transaction-duplicate-target; do
  for artifact in \
    definition.kore syntaxDefinition.kore macros.kore \
    backend.txt compiled.bin haskellDefinition.bin; do
    [[ ! -e "${OUTPUT_ROOT}/${rejected}/${artifact}" ]]
  done
done

(
  cd "${OUTPUT_ROOT}"
  sha256sum \
    r2-g-02/results.json \
    projections/p3-v1-patch-start.kore \
    projections/p3-transaction-start.kore \
    projections/p3-baseline-add.kore \
    projections/p3-transaction-add.kore \
    records/p3-transaction.json \
    records/p3-transaction-repeat.json \
    records/p3-transaction-stale-first.json \
    records/p3-transaction-stale-second.json \
    records/p3-transaction-duplicate-target.json \
    runtime/p3-transaction-start.out \
    runtime/p3-baseline-add.out \
    runtime/p3-transaction-add.out \
    >SHA256SUMS
)

jq -n \
  --arg activationRevision "${ACTIVATION_REVISION}" \
  --arg headRevision "$(git rev-parse HEAD)" \
  --arg kCommit "${K_COMMIT}" \
  --arg transportSha "$(sha256sum "${TRANSPORT_SOURCE}" | awk '{print $1}')" \
  --arg driverSha "$(sha256sum "${DRIVER_SOURCE}" | awk '{print $1}')" \
  --arg replaySha "$(sha256sum "${TRANSACTION_REPLAY_SOURCE}" | awk '{print $1}')" \
  --arg normalizerSha "$(sha256sum "${NORMALIZER}" | awk '{print $1}')" \
  --arg fixtureSha "$(sha256sum "${ADD_FIXTURE}" | awk '{print $1}')" \
  --arg staleFirstExit "${stale_first_exit}" \
  --arg staleSecondExit "${stale_second_exit}" \
  --arg duplicateExit "${duplicate_exit}" \
  --slurpfile prior "${OUTPUT_ROOT}/r2-g-02/results.json" \
  --slurpfile transaction "${OUTPUT_ROOT}/records/p3-transaction.json" \
  --slurpfile staleFirst "${OUTPUT_ROOT}/records/p3-transaction-stale-first.json" \
  --slurpfile staleSecond "${OUTPUT_ROOT}/records/p3-transaction-stale-second.json" \
  --slurpfile duplicate "${OUTPUT_ROOT}/records/p3-transaction-duplicate-target.json" \
  '{
    schemaVersion: 1,
    task: "R2-G-03-atomic-two-sentence-patch",
    verdict: "pass",
    oracleCycleCount: 1,
    activationRevision: $activationRevision,
    headRevision: $headRevision,
    kCommit: $kCommit,
    transportSchema: "KDefinitionTransport-v1",
    patchSchema: "KDefinitionPatch-v2",
    transformation: "p3-start-and-add-values@1",
    implementationSha256: {
      transport: $transportSha,
      driver: $driverSha,
      transactionReplay: $replaySha,
      focusedNormalizer: $normalizerSha,
      addValuesFixture: $fixtureSha
    },
    priorRegression: {
      verdict: $prior[0].verdict,
      patchSchema: $prior[0].patchSchema,
      identityRegression: $prior[0].identityRegression,
      priorPatch: $prior[0].patch,
      priorRejections: $prior[0].rejection
    },
    transaction: {
      status: $transaction[0].status,
      fingerprint: $transaction[0].transactionFingerprint,
      cardinality: $transaction[0].transactionCardinality,
      editCount: $transaction[0].editCount,
      validatedEditCount: $transaction[0].validatedEditCount,
      applicationCount: $transaction[0].applicationCount,
      changedLineageCount: $transaction[0].changedLineageCount,
      outputConstructed: $transaction[0].outputConstructed,
      sameDefinitionReference: $transaction[0].sameDefinitionReference,
      edits: $transaction[0].transaction.edits,
      outcomes: $transaction[0].editOutcomes,
      definitionChanged: ($transaction[0].before.contentSha256 != $transaction[0].after.contentSha256),
      canonicalRepeatStable: true
    },
    rejection: {
      staleFirst: {
        status: $staleFirst[0].status,
        exitCode: ($staleFirstExit | tonumber),
        validatedEdits: $staleFirst[0].validatedEditCount,
        applications: $staleFirst[0].applicationCount,
        outputConstructed: $staleFirst[0].outputConstructed,
        error: $staleFirst[0].error
      },
      staleSecond: {
        status: $staleSecond[0].status,
        exitCode: ($staleSecondExit | tonumber),
        validatedEdits: $staleSecond[0].validatedEditCount,
        applications: $staleSecond[0].applicationCount,
        outputConstructed: $staleSecond[0].outputConstructed,
        error: $staleSecond[0].error
      },
      duplicateTarget: {
        status: $duplicate[0].status,
        exitCode: ($duplicateExit | tonumber),
        validatedEdits: $duplicate[0].validatedEditCount,
        applications: $duplicate[0].applicationCount,
        outputConstructed: $duplicate[0].outputConstructed,
        error: $duplicate[0].error
      },
      boundary: "post-k-transaction-pre-apply",
      backendArtifacts: false
    },
    acceptance: {
      startRuntime: "k=0-state=2",
      addValuesBaselineRuntime: "k=3",
      addValuesTransactionRuntime: "k=2",
      startProjection: "equal-to-r2-g-02-v1-patch",
      addValuesProjection: "different-from-official-baseline-and-replaced-by-second-input-variable",
      syntaxAndMacros: "byte-identical-to-official-baseline",
      structuralPatchOwner: "KINK-DEFINITION-TRANSPORT",
      replacementSources: "original-official-input-nodes"
    },
    limitations: [
      "exactly two input-relative replacements in two distinct existing rules",
      "rewrite and application-argument paths only",
      "no same-rule overlap semantics, synthetic terms, insertion, deletion, condition edit, or attribute edit"
    ]
  }' >"${OUTPUT_ROOT}/results.json"

printf 'R2-G-03 transaction replay: pass\n'
