#!/usr/bin/env bash
set -euo pipefail

readonly ACTIVATION_REVISION="0722781087985b88bec35bd1698d292b00db4501"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly OUTPUT_ROOT="${1:-${REPO_ROOT}/spine/definition-transport/build/patch-replay}"
readonly SPINE="${REPO_ROOT}/spine/definition-transport"
readonly DRIVER="${SPINE}/run-driver.sh"
readonly RUNNER_SOURCE="${SPINE}/run-driver.sh"
readonly DRIVER_SOURCE="${SPINE}/src/java/org/kframework/kink/transport/DefinitionTransportDriver.java"
readonly TRANSPORT_SOURCE="${SPINE}/src/definition-transport.k"
readonly IDENTITY_REPLAY="${SPINE}/replay.sh"
readonly IDENTITY_NORMALIZER="${SPINE}/normalize_identity_kore.py"
readonly START_NORMALIZER="${SPINE}/normalize_start_kore.py"
readonly PATCH_REPLAY_SOURCE="${SPINE}/patch-replay.sh"
readonly W1_SOURCE="${REPO_ROOT}/investigations/w1-inprocess-adapter/src/org/kframework/w1/OfficialDefinitionDriver.java"
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
  "${OUTPUT_ROOT}/projections" \
  "${OUTPUT_ROOT}/w1-java"

# Accumulated R2-G-01 identity and rejection behavior, using a fresh nested output.
bash "${IDENTITY_REPLAY}" "${OUTPUT_ROOT}/identity" \
  >"${OUTPUT_ROOT}/logs/identity-replay.stdout" \
  2>"${OUTPUT_ROOT}/logs/identity-replay.stderr"
readonly TRANSPORT_DEFINITION="${OUTPUT_ROOT}/identity/transport-kompiled"
readonly P3_BASELINE="${OUTPUT_ROOT}/identity/p3-baseline"

# Fresh W1-D in-process edit, compiled from its read-only oracle source into owned output.
javac -encoding UTF-8 -cp "${K_JAVA}/*" \
  -d "${OUTPUT_ROOT}/w1-java" "${W1_SOURCE}"
W1_ADAPTER_MODE=p3-start-to-bump \
W1_ADAPTER_RECORD="${OUTPUT_ROOT}/records/p3-w1-reference.json" \
  java \
    -Dfile.encoding=UTF-8 \
    -Djava.awt.headless=true \
    -Xms64m -Xmx8192m -Xss32m -ea \
    -cp "${OUTPUT_ROOT}/w1-java:${K_JAVA}/*" \
    org.kframework.w1.OfficialDefinitionDriver \
    p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-w1-reference" \
    >"${OUTPUT_ROOT}/logs/p3-w1-reference.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-w1-reference.stderr"

KINK_TRANSPORT_MODE=patch \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-patch.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-patch" \
    >"${OUTPUT_ROOT}/logs/p3-patch.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-patch.stderr"

krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-w1-reference" \
  >"${OUTPUT_ROOT}/runtime/p3-w1-reference.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-w1-reference.err"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-patch" \
  >"${OUTPUT_ROOT}/runtime/p3-patch.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-patch.err"
cmp "${OUTPUT_ROOT}/runtime/p3-w1-reference.out" "${OUTPUT_ROOT}/runtime/p3-patch.out"
grep -Fq "    0 ~> .K" "${OUTPUT_ROOT}/runtime/p3-patch.out"
grep -Fq "    2" "${OUTPUT_ROOT}/runtime/p3-patch.out"
cmp "${P3_BASELINE}/syntaxDefinition.kore" "${OUTPUT_ROOT}/p3-patch/syntaxDefinition.kore"
cmp "${P3_BASELINE}/macros.kore" "${OUTPUT_ROOT}/p3-patch/macros.kore"

python3 "${START_NORMALIZER}" \
  "${P3_BASELINE}/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-baseline-start.kore"
python3 "${START_NORMALIZER}" \
  "${OUTPUT_ROOT}/p3-w1-reference/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-w1-reference-start.kore"
python3 "${START_NORMALIZER}" \
  "${OUTPUT_ROOT}/p3-patch/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-patch-start.kore"
cmp \
  "${OUTPUT_ROOT}/projections/p3-w1-reference-start.kore" \
  "${OUTPUT_ROOT}/projections/p3-patch-start.kore"
! cmp -s \
  "${OUTPUT_ROOT}/projections/p3-baseline-start.kore" \
  "${OUTPUT_ROOT}/projections/p3-patch-start.kore"
grep -Fq "Lblbump" "${OUTPUT_ROOT}/projections/p3-patch-start.kore"
for absent in Lbladd Lblread '#Configuration'; do
  ! grep -Fq "${absent}" "${OUTPUT_ROOT}/projections/p3-patch-start.kore"
done

jq -e '
  .status == "accepted"
  and .mode == "patch"
  and .validationBoundary == "post-k-patch-pre-apply"
  and (.sameDefinitionReference | not)
  and .patchCardinality == 1
  and .editCount == 1
  and .applicationCount == 1
  and .changedLineageCount == 1
  and (.patchFingerprint | test("^[0-9a-f]{64}$"))
  and .patch.schema == "KDefinitionPatch-v1"
  and .patch.transformation == "p3-start-to-bump@1"
  and .patch.patchCount == 1
  and .patch.editCount == 1
  and (.patch.edits | length) == 1
  and .patch.edits[0].kind == "replaceTermFromInput"
  and .patch.edits[0].targetPathCanonical == "dPathCons(dRewriteRight,dPathNil)"
  and .patch.edits[0].replacementPathCanonical == "dPathCons(dRewriteRight,dPathCons(dApplicationArgument(1),dPathNil))"
  and .patch.edits[0].targetPath == [{constructor: "dRewriteRight"}]
  and .patch.edits[0].replacementPath == [{constructor: "dRewriteRight"}, {constructor: "dApplicationArgument", index: 1}]
  and .patch.definitionFingerprint == .before.contentSha256
  and .patch.targetLineage == .before.target.lineageSha256
  and .patch.targetContent == .before.target.contentSha256
  and .patch.targetBody == .before.target.bodySha256
  and .before.target.lineageSha256 == .after.target.lineageSha256
  and .before.target.sentenceAttSha256 == .after.target.sentenceAttSha256
  and .before.target.requiresSha256 == .after.target.requiresSha256
  and .before.target.ensuresSha256 == .after.target.ensuresSha256
  and .before.target.contentSha256 != .after.target.contentSha256
  and .before.target.bodySha256 != .after.target.bodySha256
  and .before.contentSha256 != .after.contentSha256
  and .before.moduleCount == .after.moduleCount
  and .before.localSentenceCount == .after.localSentenceCount
' "${OUTPUT_ROOT}/records/p3-patch.json" >/dev/null

set +e
KINK_TRANSPORT_MODE=patch-stale-content \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-patch-stale-content.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-patch-stale-content" \
    >"${OUTPUT_ROOT}/logs/p3-patch-stale-content.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-patch-stale-content.stderr"
stale_exit=$?

KINK_TRANSPORT_MODE=patch-unsupported-path \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-patch-unsupported-path.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-patch-unsupported-path" \
    >"${OUTPUT_ROOT}/logs/p3-patch-unsupported-path.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-patch-unsupported-path.stderr"
unsupported_exit=$?
set -e

[[ "${stale_exit}" -ne 0 ]]
[[ "${unsupported_exit}" -ne 0 ]]
jq -e '
  .status == "rejected"
  and .mode == "patch-stale-content"
  and .validationBoundary == "post-k-patch-pre-apply"
  and .applicationCount == 0
  and .changedLineageCount == 0
  and .error == "patch returned stale target content fingerprint"
  and .patch.targetContent == ("0" * 64)
' "${OUTPUT_ROOT}/records/p3-patch-stale-content.json" >/dev/null
jq -e '
  .status == "rejected"
  and .mode == "patch-unsupported-path"
  and .validationBoundary == "post-k-patch-pre-apply"
  and .applicationCount == 0
  and .changedLineageCount == 0
  and .error == "unsupported path step: dSequenceItem(0)"
  and .patch.edits[0].targetPathCanonical == "dPathCons(dSequenceItem(0),dPathNil)"
  and .patch.edits[0].targetPath == [{constructor: "dSequenceItem", index: 0}]
' "${OUTPUT_ROOT}/records/p3-patch-unsupported-path.json" >/dev/null
for rejected in p3-patch-stale-content p3-patch-unsupported-path; do
  for artifact in \
    definition.kore syntaxDefinition.kore macros.kore \
    backend.txt compiled.bin haskellDefinition.bin; do
    [[ ! -e "${OUTPUT_ROOT}/${rejected}/${artifact}" ]]
  done
done

(
  cd "${OUTPUT_ROOT}"
  sha256sum \
    identity/results.json \
    projections/p3-baseline-start.kore \
    projections/p3-w1-reference-start.kore \
    projections/p3-patch-start.kore \
    records/p3-patch.json \
    records/p3-patch-stale-content.json \
    records/p3-patch-unsupported-path.json \
    runtime/p3-w1-reference.out \
    runtime/p3-patch.out \
    >SHA256SUMS
)

jq -n \
  --arg activationRevision "${ACTIVATION_REVISION}" \
  --arg headRevision "$(git rev-parse HEAD)" \
  --arg kCommit "${K_COMMIT}" \
  --arg transportSha "$(sha256sum "${TRANSPORT_SOURCE}" | awk '{print $1}')" \
  --arg driverSha "$(sha256sum "${DRIVER_SOURCE}" | awk '{print $1}')" \
  --arg runnerSha "$(sha256sum "${RUNNER_SOURCE}" | awk '{print $1}')" \
  --arg patchReplaySha "$(sha256sum "${PATCH_REPLAY_SOURCE}" | awk '{print $1}')" \
  --arg identityReplaySha "$(sha256sum "${IDENTITY_REPLAY}" | awk '{print $1}')" \
  --arg identityNormalizerSha "$(sha256sum "${IDENTITY_NORMALIZER}" | awk '{print $1}')" \
  --arg startNormalizerSha "$(sha256sum "${START_NORMALIZER}" | awk '{print $1}')" \
  --arg w1OracleSha "$(sha256sum "${W1_SOURCE}" | awk '{print $1}')" \
  --arg staleExit "${stale_exit}" \
  --arg unsupportedExit "${unsupported_exit}" \
  --slurpfile identity "${OUTPUT_ROOT}/identity/results.json" \
  --slurpfile patch "${OUTPUT_ROOT}/records/p3-patch.json" \
  --slurpfile stale "${OUTPUT_ROOT}/records/p3-patch-stale-content.json" \
  --slurpfile unsupported "${OUTPUT_ROOT}/records/p3-patch-unsupported-path.json" \
  '{
    schemaVersion: 1,
    task: "R2-G-02-single-sentence-patch",
    verdict: "pass",
    oracleCycleCount: 3,
    activationRevision: $activationRevision,
    headRevision: $headRevision,
    kCommit: $kCommit,
    transportSchema: "KDefinitionTransport-v1",
    patchSchema: "KDefinitionPatch-v1",
    transformation: "p3-start-to-bump@1",
    implementationSha256: {
      transport: $transportSha,
      driver: $driverSha,
      runner: $runnerSha,
      patchReplay: $patchReplaySha,
      identityReplay: $identityReplaySha,
      identityNormalizer: $identityNormalizerSha,
      startNormalizer: $startNormalizerSha,
      w1Oracle: $w1OracleSha
    },
    identityRegression: {
      verdict: $identity[0].verdict,
      peano: $identity[0].identity.peano,
      p3: $identity[0].identity.p3,
      priorRejections: $identity[0].rejection
    },
    patch: {
      status: $patch[0].status,
      patchFingerprint: $patch[0].patchFingerprint,
      patchCardinality: $patch[0].patchCardinality,
      editCount: $patch[0].editCount,
      applicationCount: $patch[0].applicationCount,
      changedLineageCount: $patch[0].changedLineageCount,
      sameDefinitionReference: $patch[0].sameDefinitionReference,
      targetPath: $patch[0].patch.edits[0].targetPath,
      replacementPath: $patch[0].patch.edits[0].replacementPath,
      targetPathCanonical: $patch[0].patch.edits[0].targetPathCanonical,
      replacementPathCanonical: $patch[0].patch.edits[0].replacementPathCanonical,
      definitionChanged: ($patch[0].before.contentSha256 != $patch[0].after.contentSha256),
      targetContentChanged: ($patch[0].before.target.contentSha256 != $patch[0].after.target.contentSha256),
      targetBodyChanged: ($patch[0].before.target.bodySha256 != $patch[0].after.target.bodySha256),
      lineagePreserved: ($patch[0].before.target.lineageSha256 == $patch[0].after.target.lineageSha256),
      sentenceAttributesPreserved: ($patch[0].before.target.sentenceAttSha256 == $patch[0].after.target.sentenceAttSha256),
      sideConditionsPreserved: (($patch[0].before.target.requiresSha256 == $patch[0].after.target.requiresSha256) and ($patch[0].before.target.ensuresSha256 == $patch[0].after.target.ensuresSha256))
    },
    rejection: {
      staleContent: {status: $stale[0].status, exitCode: ($staleExit | tonumber), error: $stale[0].error, applications: $stale[0].applicationCount},
      unsupportedPath: {status: $unsupported[0].status, exitCode: ($unsupportedExit | tonumber), error: $unsupported[0].error, applications: $unsupported[0].applicationCount},
      boundary: "post-k-patch-pre-apply",
      backendArtifacts: false
    },
    acceptance: {
      runtime: "byte-identical-to-fresh-W1-D-inprocess-reference-and-k=0-state=2",
      focusedKore: "equal-to-W1-D-reference-and-different-from-baseline",
      syntaxAndMacros: "byte-identical-to-official-baseline",
      structuralPatchOwner: "KINK-DEFINITION-TRANSPORT",
      replacementSource: "original-official-input-node"
    },
    limitations: [
      "one input-relative term replacement in one existing rule",
      "rewrite and application-argument paths only",
      "no synthetic terms, multi-edit transaction, insertion, deletion, condition edit, or attribute edit"
    ]
  }' >"${OUTPUT_ROOT}/results.json"

printf 'R2-G-02 replay: pass\n'
