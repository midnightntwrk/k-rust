#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$workspace"

features=cli,measure
if (( $# > 0 )); then
  if [[ $# -ne 1 || $1 != --gh-release ]]; then
    echo "usage: scripts/measure-ratchet.sh [--gh-release]" >&2
    exit 2
  fi
  features+=,z3-inference-gh-release
fi

# These snapshots measure one engine's work and must never accept mismatches.
unset KRUST_TYPE_INFERENCE_MODE INSTA_FORCE_UPDATE INSTA_FORCE_UPDATE_SNAPSHOTS
export INSTA_UPDATE=no INSTA_FORCE_PASS=0

shopt -s nullglob
reject_pending_snapshots() {
  local pending=(crates/k-rust/tests/snapshots/measure_ratchet__*.snap.new)
  if (( ${#pending[@]} > 0 )); then
    echo "error: pending measurement snapshots:" >&2
    printf '  %s\n' "${pending[@]}" >&2
    exit 1
  fi
}

cargo_command=(cargo test -p k-rust --no-default-features --features "$features" --test measure_ratchet --locked)
reject_pending_snapshots
test_list=$("${cargo_command[@]}" -- --list)
printf '%s\n' "$test_list"
for required in \
  rewrite_example_compile_stays_within_the_pinned_kompile_work \
  module_chain_compile_resolves_per_pass_and_grows_sentences_linearly \
  indexed_prediction_preserves_the_casted_chain_counts; do
  if ! grep -Fxq "$required: test" <<<"$test_list"; then
    echo "error: missing required measurement test: $required" >&2
    exit 1
  fi
done

status=0
"${cargo_command[@]}" || status=$?
reject_pending_snapshots
if (( status != 0 )); then
  exit "$status"
fi
echo "Measurement ratchet passed"
