#!/usr/bin/env bash
set -euo pipefail

readonly STARTING_REVISION="058a66513962a373f69a597404a8a54442347b75"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly OUTPUT_ROOT="${1:-${REPO_ROOT}/spine/definition-transport/build/replay}"
readonly DRIVER="${REPO_ROOT}/spine/definition-transport/run-driver.sh"
readonly DRIVER_SOURCE="${REPO_ROOT}/spine/definition-transport/src/java/org/kframework/kink/transport/DefinitionTransportDriver.java"
readonly TRANSPORT_SOURCE="${REPO_ROOT}/spine/definition-transport/src/definition-transport.k"
readonly TRANSPORT_DEFINITION="${OUTPUT_ROOT}/transport-kompiled"
readonly NORMALIZER="${REPO_ROOT}/spine/definition-transport/normalize_identity_kore.py"
readonly REPLAY_SOURCE="${REPO_ROOT}/spine/definition-transport/replay.sh"

git merge-base --is-ancestor "${STARTING_REVISION}" HEAD
[[ "$(readlink -f "$(command -v kompile)")" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "v7.1.337" >/dev/null
[[ ! -e "${OUTPUT_ROOT}" ]]

export LC_ALL=C
export LANG=C
export TZ=UTC

cd "${REPO_ROOT}"
mkdir -p \
  "${OUTPUT_ROOT}/logs" \
  "${OUTPUT_ROOT}/records" \
  "${OUTPUT_ROOT}/runtime" \
  "${OUTPUT_ROOT}/projections"

kompile "${TRANSPORT_SOURCE}" \
  --backend llvm \
  --main-module KINK-DEFINITION-TRANSPORT \
  --syntax-module KINK-DEFINITION-TRANSPORT-SYNTAX \
  --output-definition "${TRANSPORT_DEFINITION}" \
  >"${OUTPUT_ROOT}/logs/transport.stdout" \
  2>"${OUTPUT_ROOT}/logs/transport.stderr"

kompile p1/fixtures/peano.k \
  --backend haskell \
  --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/peano-baseline" \
  >"${OUTPUT_ROOT}/logs/peano-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/peano-baseline.stderr"
KINK_TRANSPORT_MODE=identity \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/peano-identity.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p1/fixtures/peano.k \
    --backend haskell \
    --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/peano-identity" \
    >"${OUTPUT_ROOT}/logs/peano-identity.stdout" \
    2>"${OUTPUT_ROOT}/logs/peano-identity.stderr"

kompile p3/fixtures/coupled.k \
  --backend haskell \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/p3-baseline" \
  >"${OUTPUT_ROOT}/logs/p3-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-baseline.stderr"
KINK_TRANSPORT_MODE=identity \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-identity.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-identity" \
    >"${OUTPUT_ROOT}/logs/p3-identity.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-identity.stderr"

for fixture in peano p3; do
  for variant in baseline identity; do
    python3 "${NORMALIZER}" \
      "${OUTPUT_ROOT}/${fixture}-${variant}/definition.kore" \
      "${OUTPUT_ROOT}/projections/${fixture}-${variant}-definition.kore"
  done
  cmp \
    "${OUTPUT_ROOT}/projections/${fixture}-baseline-definition.kore" \
    "${OUTPUT_ROOT}/projections/${fixture}-identity-definition.kore"
  cmp \
    "${OUTPUT_ROOT}/${fixture}-baseline/syntaxDefinition.kore" \
    "${OUTPUT_ROOT}/${fixture}-identity/syntaxDefinition.kore"
  cmp \
    "${OUTPUT_ROOT}/${fixture}-baseline/macros.kore" \
    "${OUTPUT_ROOT}/${fixture}-identity/macros.kore"
done

krun p1/fixtures/program.peano --definition "${OUTPUT_ROOT}/peano-baseline" \
  >"${OUTPUT_ROOT}/runtime/peano-baseline.out" \
  2>"${OUTPUT_ROOT}/runtime/peano-baseline.err"
krun p1/fixtures/program.peano --definition "${OUTPUT_ROOT}/peano-identity" \
  >"${OUTPUT_ROOT}/runtime/peano-identity.out" \
  2>"${OUTPUT_ROOT}/runtime/peano-identity.err"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-baseline" \
  >"${OUTPUT_ROOT}/runtime/p3-baseline.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-baseline.err"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-identity" \
  >"${OUTPUT_ROOT}/runtime/p3-identity.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-identity.err"
cmp "${OUTPUT_ROOT}/runtime/peano-baseline.out" "${OUTPUT_ROOT}/runtime/peano-identity.out"
cmp "${OUTPUT_ROOT}/runtime/p3-baseline.out" "${OUTPUT_ROOT}/runtime/p3-identity.out"

jq -e '
  .status == "accepted"
  and .mode == "identity"
  and .sameDefinitionReference
  and .selectionCount == 0
  and .transport.selectionCount == 0
  and (.transport.selections | length) == 0
  and .before.target == null
  and (.before.contentSha256 == .after.contentSha256)
  and (.transport.definitionFingerprint == .before.contentSha256)
  and (.before.primarySourceSentenceCount > 0)
  and (.before.innerProductionAttributeCount > 0)
' "${OUTPUT_ROOT}/records/peano-identity.json" >/dev/null

jq -e '
  .status == "accepted"
  and .mode == "identity"
  and .sameDefinitionReference
  and .selectionCount == 1
  and .transport.selectionCount == 1
  and (.transport.selections | length) == 1
  and .before.target.label == "start-program"
  and (.transport.definitionFingerprint == .before.contentSha256)
  and (.transport.selections[0].lineageSha256 == .before.target.lineageSha256)
  and (.transport.selections[0].contentSha256 == .before.target.contentSha256)
  and (.transport.selections[0].bodySha256 == .before.target.bodySha256)
  and (.before.contentSha256 == .after.contentSha256)
  and (.before.innerAttributesSha256 == .after.innerAttributesSha256)
  and (.before.primarySourceProjectionSha256 == .after.primarySourceProjectionSha256)
' "${OUTPUT_ROOT}/records/p3-identity.json" >/dev/null

set +e
KINK_TRANSPORT_MODE=stale-lineage \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-stale-lineage.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-stale-lineage" \
    >"${OUTPUT_ROOT}/logs/p3-stale-lineage.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-stale-lineage.stderr"
lineage_exit=$?

KINK_TRANSPORT_MODE=stale-content \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-stale-content.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-stale-content" \
    >"${OUTPUT_ROOT}/logs/p3-stale-content.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-stale-content.stderr"
stale_exit=$?

KINK_TRANSPORT_MODE=duplicate-target \
KINK_TRANSPORT_RECORD="${OUTPUT_ROOT}/records/p3-duplicate-target.json" \
KINK_TRANSPORT_KOMPILED="${TRANSPORT_DEFINITION}" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-duplicate-target" \
    >"${OUTPUT_ROOT}/logs/p3-duplicate-target.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-duplicate-target.stderr"
duplicate_exit=$?
set -e

[[ "${lineage_exit}" -ne 0 ]]
[[ "${stale_exit}" -ne 0 ]]
[[ "${duplicate_exit}" -ne 0 ]]
jq -e '
  .status == "rejected"
  and .mode == "stale-lineage"
  and .validationBoundary == "post-k-selection-pre-backend"
  and .selectionCount == 1
  and .error == "K selection returned stale lineage"
  and .transport.selections[0].lineageSha256 == ("0" * 64)
' "${OUTPUT_ROOT}/records/p3-stale-lineage.json" >/dev/null
jq -e '
  .status == "rejected"
  and .mode == "stale-content"
  and .validationBoundary == "post-k-selection-pre-backend"
  and .selectionCount == 1
  and .error == "K selection returned stale content fingerprint"
  and .transport.selections[0].contentSha256 == ("0" * 64)
' "${OUTPUT_ROOT}/records/p3-stale-content.json" >/dev/null
jq -e '
  .status == "rejected"
  and .mode == "duplicate-target"
  and .validationBoundary == "post-k-selection-pre-backend"
  and .selectionCount == 2
  and .error == "expected 1 K structural selections, found 2"
  and (.transport.selections | length) == 2
' "${OUTPUT_ROOT}/records/p3-duplicate-target.json" >/dev/null
for rejected in p3-stale-lineage p3-stale-content p3-duplicate-target; do
  for artifact in \
    definition.kore syntaxDefinition.kore macros.kore \
    backend.txt compiled.bin haskellDefinition.bin; do
    [[ ! -e "${OUTPUT_ROOT}/${rejected}/${artifact}" ]]
  done
done

(
  cd "${OUTPUT_ROOT}"
  sha256sum \
    projections/peano-baseline-definition.kore \
    projections/peano-identity-definition.kore \
    projections/p3-baseline-definition.kore \
    projections/p3-identity-definition.kore \
    runtime/peano-baseline.out \
    runtime/peano-identity.out \
    runtime/p3-baseline.out \
    runtime/p3-identity.out \
    records/peano-identity.json \
    records/p3-identity.json \
    records/p3-stale-lineage.json \
    records/p3-stale-content.json \
    records/p3-duplicate-target.json \
    >SHA256SUMS
)

jq -n \
  --arg startingRevision "${STARTING_REVISION}" \
  --arg headRevision "$(git rev-parse HEAD)" \
  --arg kCommit "${K_COMMIT}" \
  --arg transportSchema "KDefinitionTransport-v1" \
  --arg transportSourceSha256 "$(sha256sum "${TRANSPORT_SOURCE}" | awk '{print $1}')" \
  --arg driverSourceSha256 "$(sha256sum "${DRIVER_SOURCE}" | awk '{print $1}')" \
  --arg replaySourceSha256 "$(sha256sum "${REPLAY_SOURCE}" | awk '{print $1}')" \
  --arg normalizerSourceSha256 "$(sha256sum "${NORMALIZER}" | awk '{print $1}')" \
  --arg lineageExit "${lineage_exit}" \
  --arg staleExit "${stale_exit}" \
  --arg duplicateExit "${duplicate_exit}" \
  --slurpfile peano "${OUTPUT_ROOT}/records/peano-identity.json" \
  --slurpfile p3 "${OUTPUT_ROOT}/records/p3-identity.json" \
  --slurpfile lineage "${OUTPUT_ROOT}/records/p3-stale-lineage.json" \
  --slurpfile stale "${OUTPUT_ROOT}/records/p3-stale-content.json" \
  --slurpfile duplicate "${OUTPUT_ROOT}/records/p3-duplicate-target.json" \
  '{
    schemaVersion: 1,
    task: "R2-G-01-k-definition-transport",
    verdict: "pass",
    startingRevision: $startingRevision,
    headRevision: $headRevision,
    kCommit: $kCommit,
    transportSchema: $transportSchema,
    implementationSha256: {
      transport: $transportSourceSha256,
      driver: $driverSourceSha256,
      replay: $replaySourceSha256,
      normalizer: $normalizerSourceSha256
    },
    identity: {
      peano: {
        status: $peano[0].status,
        sameDefinitionReference: $peano[0].sameDefinitionReference,
        selections: $peano[0].selectionCount
      },
      p3: {
        status: $p3[0].status,
        sameDefinitionReference: $p3[0].sameDefinitionReference,
        selections: $p3[0].selectionCount,
        selectedLabel: $p3[0].before.target.label,
        lineageValidated: ($p3[0].transport.selections[0].lineageSha256 == $p3[0].before.target.lineageSha256),
        contentValidated: ($p3[0].transport.selections[0].contentSha256 == $p3[0].before.target.contentSha256),
        bodyValidated: ($p3[0].transport.selections[0].bodySha256 == $p3[0].before.target.bodySha256)
      }
    },
    rejection: {
      staleLineage: {status: $lineage[0].status, exitCode: ($lineageExit | tonumber), error: $lineage[0].error},
      staleContent: {status: $stale[0].status, exitCode: ($staleExit | tonumber), error: $stale[0].error},
      duplicateTarget: {status: $duplicate[0].status, exitCode: ($duplicateExit | tonumber), error: $duplicate[0].error},
      boundary: "post-k-selection-pre-backend"
    },
    acceptance: {
      identityKore: "equal-after-scoped-alpha-normalization-of-backend-generated-_GenN-binders",
      syntaxAndMacros: "byte-identical",
      runtime: "byte-identical",
      structuralSelectionOwner: "KINK-DEFINITION-TRANSPORT",
      backendOnRejectedInput: false
    }
  }' >"${OUTPUT_ROOT}/results.json"

printf 'R2-G-01 replay: pass\n'
