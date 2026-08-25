#!/usr/bin/env bash
set -euo pipefail

readonly STARTING_REVISION="57c02599ab970a4d95b7155cf9801adca9bc179c"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly K_SOURCE="/home/sebdev20/Documents/git/workspaces/starstream-fv/inspirations/runtimeverification/k"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly OUTPUT_ROOT="${1:-${REPO_ROOT}/investigations/w1-inprocess-adapter/replay}"
readonly DRIVER="${REPO_ROOT}/investigations/w1-inprocess-adapter/run-driver.sh"

git merge-base --is-ancestor "${STARTING_REVISION}" HEAD
[[ "$(git -C "${K_SOURCE}" rev-parse HEAD)" == "${K_COMMIT}" ]]
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

kompile p1/fixtures/peano.k \
  --backend haskell --emit-json \
  --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/peano-baseline" \
  >"${OUTPUT_ROOT}/logs/peano-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/peano-baseline.stderr"
W1_ADAPTER_MODE=identity \
W1_ADAPTER_RECORD="${OUTPUT_ROOT}/records/peano-identity.json" \
  "${DRIVER}" p1/fixtures/peano.k \
    --backend haskell --emit-json \
    --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/peano-identity" \
    >"${OUTPUT_ROOT}/logs/peano-identity.stdout" \
    2>"${OUTPUT_ROOT}/logs/peano-identity.stderr"

kompile p3/fixtures/coupled.k \
  --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/p3-baseline" \
  >"${OUTPUT_ROOT}/logs/p3-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-baseline.stderr"
W1_ADAPTER_MODE=identity \
W1_ADAPTER_RECORD="${OUTPUT_ROOT}/records/p3-identity.json" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell --emit-json \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-identity" \
    >"${OUTPUT_ROOT}/logs/p3-identity.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-identity.stderr"

for fixture in peano p3; do
  for variant in baseline identity; do
    python3 investigations/w1-inprocess-adapter/normalize_identity_kore.py \
      "${OUTPUT_ROOT}/${fixture}-${variant}/definition.kore" \
      "${OUTPUT_ROOT}/projections/${fixture}-${variant}-definition.kore"
  done
  cmp \
    "${OUTPUT_ROOT}/projections/${fixture}-baseline-definition.kore" \
    "${OUTPUT_ROOT}/projections/${fixture}-identity-definition.kore"
  for artifact in syntaxDefinition.kore macros.kore; do
    cmp "${OUTPUT_ROOT}/${fixture}-baseline/${artifact}" "${OUTPUT_ROOT}/${fixture}-identity/${artifact}"
  done
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

for fixture in peano p3; do
  jq -e '
    .status == "accepted"
    and .mode == "identity"
    and .sameDefinitionReference
    and (.before.contentSha256 == .after.contentSha256)
    and (.before.innerAttributesSha256 == .after.innerAttributesSha256)
    and (.before.primarySourceProjectionSha256 == .after.primarySourceProjectionSha256)
    and (.before.innerProductionAttributeCount > 0)
    and (.before.primarySourceSentenceCount > 0)
  ' "${OUTPUT_ROOT}/records/${fixture}-identity.json" >/dev/null
done

# W1-A's established compiled-KAST edit is regenerated only as a local oracle.
kompile p3/fixtures/coupled.k \
  --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --post-process "python3 investigations/w1-egress/postprocess.py p3-start-to-bump" \
  --output-definition "${OUTPUT_ROOT}/p3-reference-edit" \
  >"${OUTPUT_ROOT}/logs/p3-reference-edit.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-reference-edit.stderr"
W1_ADAPTER_MODE=p3-start-to-bump \
W1_ADAPTER_RECORD="${OUTPUT_ROOT}/records/p3-inprocess-edit.json" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell --emit-json \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-inprocess-edit" \
    >"${OUTPUT_ROOT}/logs/p3-inprocess-edit.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-inprocess-edit.stderr"

krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-reference-edit" \
  >"${OUTPUT_ROOT}/runtime/p3-reference-edit.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-reference-edit.err"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-inprocess-edit" \
  >"${OUTPUT_ROOT}/runtime/p3-inprocess-edit.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-inprocess-edit.err"
cmp "${OUTPUT_ROOT}/runtime/p3-reference-edit.out" "${OUTPUT_ROOT}/runtime/p3-inprocess-edit.out"
cmp "${OUTPUT_ROOT}/p3-baseline/syntaxDefinition.kore" "${OUTPUT_ROOT}/p3-inprocess-edit/syntaxDefinition.kore"
cmp "${OUTPUT_ROOT}/p3-baseline/macros.kore" "${OUTPUT_ROOT}/p3-inprocess-edit/macros.kore"
! cmp "${OUTPUT_ROOT}/p3-baseline/definition.kore" "${OUTPUT_ROOT}/p3-inprocess-edit/definition.kore"
grep -Fq "    0 ~> .K" "${OUTPUT_ROOT}/runtime/p3-inprocess-edit.out"
grep -Fq "    2" "${OUTPUT_ROOT}/runtime/p3-inprocess-edit.out"

python3 investigations/w1-inprocess-adapter/normalize_start_kore.py \
  "${OUTPUT_ROOT}/p3-reference-edit/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-reference-start.kore"
python3 investigations/w1-inprocess-adapter/normalize_start_kore.py \
  "${OUTPUT_ROOT}/p3-inprocess-edit/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
python3 investigations/w1-inprocess-adapter/normalize_start_kore.py \
  "${OUTPUT_ROOT}/p3-baseline/definition.kore" \
  "${OUTPUT_ROOT}/projections/p3-baseline-start.kore"
! cmp "${OUTPUT_ROOT}/projections/p3-baseline-start.kore" "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
grep -Fq '#as #Configuration' "${OUTPUT_ROOT}/projections/p3-reference-start.kore"
! grep -Fq '#Configuration' "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
! grep -Fq 'Lbladd' "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
! grep -Fq 'Lblread' "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
grep -Fq 'Lblbump' "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore"
diff -u \
  "${OUTPUT_ROOT}/projections/p3-baseline-start.kore" \
  "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore" \
  >"${OUTPUT_ROOT}/projections/p3-start-program.diff" || [[ $? -eq 1 ]]
diff -u \
  "${OUTPUT_ROOT}/projections/p3-reference-start.kore" \
  "${OUTPUT_ROOT}/projections/p3-inprocess-start.kore" \
  >"${OUTPUT_ROOT}/projections/p3-pre-lowering-consumption.diff" || [[ $? -eq 1 ]]

python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/p3-baseline/compiled.json" /p3/fixtures/coupled.k \
  "${OUTPUT_ROOT}/projections/p3-baseline-identity.json"
python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/p3-inprocess-edit/compiled.json" /p3/fixtures/coupled.k \
  "${OUTPUT_ROOT}/projections/p3-inprocess-identity.json"
jq -e --slurp '
  ([.[0].sentences[] | select(.label == "start-program")][0]) as $before
  | ([.[1].sentences[] | select(.label == "start-program")][0]) as $after
  | $before.source == $after.source
    and $before.location == $after.location
    and $before.label == $after.label
    and $before.uniqueId != $after.uniqueId
    and $before.bodySha256 != $after.bodySha256
    and $before.requiresSha256 == $after.requiresSha256
    and $before.ensuresSha256 == $after.ensuresSha256
' \
  "${OUTPUT_ROOT}/projections/p3-baseline-identity.json" \
  "${OUTPUT_ROOT}/projections/p3-inprocess-identity.json" >/dev/null

jq -e '
  .status == "accepted"
  and .mode == "p3-start-to-bump"
  and (.sameDefinitionReference | not)
  and .matchedTargets == 1
  and .replacements == 1
  and .before.target.uniqueId == null
  and .after.target.uniqueId == null
  and .before.target.lineageSha256 == .after.target.lineageSha256
  and .before.target.sentenceAttSha256 == .after.target.sentenceAttSha256
  and .before.target.bodySha256 != .after.target.bodySha256
  and .before.target.requiresSha256 == .after.target.requiresSha256
  and .before.target.ensuresSha256 == .after.target.ensuresSha256
  and .before.contentSha256 != .after.contentSha256
' "${OUTPUT_ROOT}/records/p3-inprocess-edit.json" >/dev/null

set +e
W1_ADAPTER_MODE=malformed-null \
W1_ADAPTER_RECORD="${OUTPUT_ROOT}/records/p3-malformed-null.json" \
  "${DRIVER}" p3/fixtures/coupled.k \
    --backend haskell \
    --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-malformed-null" \
    >"${OUTPUT_ROOT}/logs/p3-malformed-null.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-malformed-null.stderr"
malformed_exit=$?
set -e
[[ "${malformed_exit}" -ne 0 ]]
grep -Fq "W1 adapter validation failed: transformation returned null" \
  "${OUTPUT_ROOT}/logs/p3-malformed-null.stderr"
jq -e '
  .status == "rejected"
  and .mode == "malformed-null"
  and .validationBoundary == "post-transform-pre-backend"
  and .error == "transformation returned null Definition"
' "${OUTPUT_ROOT}/records/p3-malformed-null.json" >/dev/null
[[ ! -e "${OUTPUT_ROOT}/p3-malformed-null/definition.kore" ]]

{
  for definition in \
    peano-baseline peano-identity \
    p3-baseline p3-identity p3-reference-edit p3-inprocess-edit; do
    for artifact in definition.kore syntaxDefinition.kore macros.kore; do
      sha256sum "${OUTPUT_ROOT}/${definition}/${artifact}"
    done
  done
  sha256sum "${OUTPUT_ROOT}"/records/*.json
  sha256sum "${OUTPUT_ROOT}"/runtime/*.out
  sha256sum "${OUTPUT_ROOT}"/projections/*
} >"${OUTPUT_ROOT}/SHA256SUMS"

jq -n \
  --arg startingRevision "${STARTING_REVISION}" \
  --arg kCommit "${K_COMMIT}" \
  --arg malformedExit "${malformed_exit}" \
  --slurpfile peano "${OUTPUT_ROOT}/records/peano-identity.json" \
  --slurpfile p3 "${OUTPUT_ROOT}/records/p3-identity.json" \
  --slurpfile edit "${OUTPUT_ROOT}/records/p3-inprocess-edit.json" \
  --slurpfile malformed "${OUTPUT_ROOT}/records/p3-malformed-null.json" \
  '{
    schemaVersion: 1,
    task: "W1-D-inprocess-adapter-replay",
    verdict: "pass",
    startingRevision: $startingRevision,
    kCommit: $kCommit,
    identity: {peano: $peano[0], p3: $p3[0]},
    mutation: $edit[0],
    malformed: ($malformed[0] + {exitCode: ($malformedExit | tonumber)}),
    acceptance: {
      identityKore: "equal-after-scoped-alpha-normalization-of-backend-generated-_GenN-binders",
      identityRuntime: "byte-identical",
      mutationKore: "localized-start-program-change-with-official-function-with-config-binder-eliminated",
      mutationRuntime: "byte-identical-to-W1-A-edit-oracle",
      failureBoundary: "post-transform-pre-backend"
    }
  }' >"${OUTPUT_ROOT}/results.json"

printf 'W1-D replay: pass\n'
