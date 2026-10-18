#!/usr/bin/env bash
# The matching-logic position matrix (crates/k-rust/tests/ml_positions.rs): run its ignored shards
# and its completeness test in the portable build, then in the native (`z3-inference`) build, both in the test profile, so
# debug assertions and the kompile invariants run on every cell.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

usage() {
  cat <<'EOF'
usage: scripts/ml-positions.sh [SHARD...]

Run the shards of crates/k-rust/tests/ml_positions.rs (every shard by default; a SHARD is a test
name such as cond_rule_requires) in the portable and the native build. KRUST_GATE_Z3 selects how
the native build acquires Z3 as for the reference gates (gh-release, the default, downloads the
release; system links the Z3 the environment provides), KRUST_GATE_TARGET_DIR the target
directory (default target/gates), and ML_POSITIONS_OUT a directory for one TSV line per cell and
build. Exit status 0 when every cell matches the matrix in both builds, 1 otherwise, 2 on a usage
error.
EOF
}

case ${1:-} in
  -h | --help)
    usage
    exit 0
    ;;
  -*)
    usage >&2
    exit 2
    ;;
esac

case ${KRUST_GATE_Z3:-gh-release} in
  gh-release) native_features=z3-inference-gh-release ;;
  system) native_features=z3-inference ;;
  *)
    echo "error: KRUST_GATE_Z3 must be gh-release or system" >&2
    exit 2
    ;;
esac
target_dir=${KRUST_GATE_TARGET_DIR:-$workspace/target/gates}

matrix() {
  cargo test --locked --manifest-path "$workspace/Cargo.toml" --target-dir "$target_dir" \
    -p k-rust --no-default-features "$@" --test ml_positions -- --include-ignored "${shards[@]}"
}

shards=("$@")
echo "[ml-positions] portable build" >&2
matrix || exit 1
echo "[ml-positions] native build (features $native_features)" >&2
matrix --features "$native_features" || exit 1
