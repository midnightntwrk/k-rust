#!/usr/bin/env bash
set -euo pipefail

readonly STARTING_REVISION="9f30221d08de4b0f710061ce599b3c7f9f860273"
readonly K_COMMIT="4a46d1231473b599c699160132fd6e76a5c46406"
readonly REPO_ROOT="$(git rev-parse --show-toplevel)"
readonly OUTPUT_ROOT="${1:-${REPO_ROOT}/investigations/w1-egress/replay}"

git merge-base --is-ancestor "${STARTING_REVISION}" HEAD
[[ "$(readlink -f "$(command -v kompile)")" == *"${K_COMMIT}"* ]]
kompile --version | grep -F "v7.1.337"
[[ ! -e "${OUTPUT_ROOT}" ]]

export LC_ALL=C
export LANG=C
export TZ=UTC

cd "${REPO_ROOT}"
mkdir -p "${OUTPUT_ROOT}/logs" "${OUTPUT_ROOT}/runtime" "${OUTPUT_ROOT}/projections"

kompile p1/fixtures/peano.k --backend haskell --emit-json \
  --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/peano-baseline" \
  >"${OUTPUT_ROOT}/logs/peano-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/peano-baseline.stderr"
kompile p1/fixtures/peano.k --backend haskell --emit-json \
  --main-module P1-PEANO --syntax-module P1-PEANO-SYNTAX \
  --post-process "python3 investigations/w1-egress/postprocess.py identity" \
  --output-definition "${OUTPUT_ROOT}/peano-identity" \
  >"${OUTPUT_ROOT}/logs/peano-identity.stdout" \
  2>"${OUTPUT_ROOT}/logs/peano-identity.stderr"
krun p1/fixtures/program.peano --definition "${OUTPUT_ROOT}/peano-baseline" \
  >"${OUTPUT_ROOT}/runtime/peano-baseline.out" \
  2>"${OUTPUT_ROOT}/runtime/peano-baseline.err"
krun p1/fixtures/program.peano --definition "${OUTPUT_ROOT}/peano-identity" \
  >"${OUTPUT_ROOT}/runtime/peano-identity.out" \
  2>"${OUTPUT_ROOT}/runtime/peano-identity.err"

kompile p3/fixtures/coupled.k --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --output-definition "${OUTPUT_ROOT}/p3-baseline" \
  >"${OUTPUT_ROOT}/logs/p3-baseline.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-baseline.stderr"
kompile p3/fixtures/coupled.k --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --post-process "python3 investigations/w1-egress/postprocess.py identity" \
  --output-definition "${OUTPUT_ROOT}/p3-identity" \
  >"${OUTPUT_ROOT}/logs/p3-identity.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-identity.stderr"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-baseline" \
  >"${OUTPUT_ROOT}/runtime/p3-baseline.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-baseline.err"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-identity" \
  >"${OUTPUT_ROOT}/runtime/p3-identity.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-identity.err"

for artifact in definition.kore syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT_ROOT}/peano-baseline/${artifact}" "${OUTPUT_ROOT}/peano-identity/${artifact}"
  cmp "${OUTPUT_ROOT}/p3-baseline/${artifact}" "${OUTPUT_ROOT}/p3-identity/${artifact}"
done
cmp "${OUTPUT_ROOT}/runtime/peano-baseline.out" "${OUTPUT_ROOT}/runtime/peano-identity.out"
cmp "${OUTPUT_ROOT}/runtime/p3-baseline.out" "${OUTPUT_ROOT}/runtime/p3-identity.out"

python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/peano-baseline/compiled.json" /p1/fixtures/peano.k \
  "${OUTPUT_ROOT}/projections/peano-baseline.json"
python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/peano-identity/compiled.json" /p1/fixtures/peano.k \
  "${OUTPUT_ROOT}/projections/peano-identity.json"
python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/p3-baseline/compiled.json" /p3/fixtures/coupled.k \
  "${OUTPUT_ROOT}/projections/p3-baseline.json"
python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/p3-identity/compiled.json" /p3/fixtures/coupled.k \
  "${OUTPUT_ROOT}/projections/p3-identity.json"
jq -e --slurp '.[0].sentences == .[1].sentences' \
  "${OUTPUT_ROOT}/projections/peano-baseline.json" \
  "${OUTPUT_ROOT}/projections/peano-identity.json"
jq -e --slurp '.[0].sentences == .[1].sentences' \
  "${OUTPUT_ROOT}/projections/p3-baseline.json" \
  "${OUTPUT_ROOT}/projections/p3-identity.json"

kompile p3/fixtures/coupled.k --backend haskell --emit-json \
  --main-module P3-COUPLED --syntax-module P3-COUPLED-SYNTAX \
  --post-process "python3 investigations/w1-egress/postprocess.py p3-start-to-bump" \
  --output-definition "${OUTPUT_ROOT}/p3-sentence-edit" \
  >"${OUTPUT_ROOT}/logs/p3-sentence-edit.stdout" \
  2>"${OUTPUT_ROOT}/logs/p3-sentence-edit.stderr"
krun p3/fixtures/program.exp --definition "${OUTPUT_ROOT}/p3-sentence-edit" \
  >"${OUTPUT_ROOT}/runtime/p3-sentence-edit.out" \
  2>"${OUTPUT_ROOT}/runtime/p3-sentence-edit.err"
cmp "${OUTPUT_ROOT}/p3-baseline/syntaxDefinition.kore" "${OUTPUT_ROOT}/p3-sentence-edit/syntaxDefinition.kore"
cmp "${OUTPUT_ROOT}/p3-baseline/macros.kore" "${OUTPUT_ROOT}/p3-sentence-edit/macros.kore"
! cmp "${OUTPUT_ROOT}/p3-baseline/definition.kore" "${OUTPUT_ROOT}/p3-sentence-edit/definition.kore"
grep -Fq "    0 ~> .K" "${OUTPUT_ROOT}/runtime/p3-sentence-edit.out"
grep -Fq "    2" "${OUTPUT_ROOT}/runtime/p3-sentence-edit.out"
python3 investigations/w1-egress/project_identity.py \
  "${OUTPUT_ROOT}/p3-sentence-edit/compiled.json" /p3/fixtures/coupled.k \
  "${OUTPUT_ROOT}/projections/p3-sentence-edit.json"
jq -e --slurp \
  '([.[0].sentences[] | {"label":.label,"uniqueId":.uniqueId,"source":.source,"location":.location}] | sort_by(.label,.uniqueId)) == ([.[1].sentences[] | {"label":.label,"uniqueId":.uniqueId,"source":.source,"location":.location}] | sort_by(.label,.uniqueId))' \
  "${OUTPUT_ROOT}/projections/p3-baseline.json" \
  "${OUTPUT_ROOT}/projections/p3-sentence-edit.json"

for repeat in a b; do
  kompile investigations/w1-egress/fixtures/p3-observation.k \
    --backend haskell --emit-json \
    --main-module W1-P3-OBSERVATION \
    --syntax-module W1-P3-OBSERVATION-SYNTAX \
    --output-definition "${OUTPUT_ROOT}/p3-observation-${repeat}" \
    >"${OUTPUT_ROOT}/logs/p3-observation-${repeat}.stdout" \
    2>"${OUTPUT_ROOT}/logs/p3-observation-${repeat}.stderr"
  krun investigations/w1-egress/fixtures/program.exp \
    --definition "${OUTPUT_ROOT}/p3-observation-${repeat}" \
    >"${OUTPUT_ROOT}/runtime/p3-observation-${repeat}.out" \
    2>"${OUTPUT_ROOT}/runtime/p3-observation-${repeat}.err"
done
for artifact in parsed.json compiled.json definition.kore syntaxDefinition.kore macros.kore; do
  cmp "${OUTPUT_ROOT}/p3-observation-a/${artifact}" "${OUTPUT_ROOT}/p3-observation-b/${artifact}"
done
cmp "${OUTPUT_ROOT}/runtime/p3-observation-a.out" "${OUTPUT_ROOT}/runtime/p3-observation-b.out"
grep -Fq "  <observation>" "${OUTPUT_ROOT}/runtime/p3-observation-a.out"
grep -Fq "    0" "${OUTPUT_ROOT}/runtime/p3-observation-a.out"
grep -Fq "LblinitObservationCell" "${OUTPUT_ROOT}/p3-observation-a/definition.kore"

find "${OUTPUT_ROOT}" -type f \
  \( -name '*.json' -o -name '*.kore' -o -name '*.out' -o -name '*.err' \) \
  -print0 | sort -z | xargs -0 sha256sum >"${OUTPUT_ROOT}/SHA256SUMS"
printf 'W1-A replay: pass\n'
