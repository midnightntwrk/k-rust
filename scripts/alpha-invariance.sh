#!/usr/bin/env bash
# The alpha-invariance harness (crates/k-rust/tests/alpha_invariance.rs): run all of its tests,
# the ignored whole-corpus and whole-generated-grammar tests included, in the portable build and
# then in the native (`z3-inference`) build, both in the test profile, so debug assertions and
# the kompile invariants run on every compile. Each test prints its counts and the corpus files it
# leaves out (--show-output).
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

usage() {
  cat <<'EOF_USAGE'
usage: scripts/alpha-invariance.sh [TEST...]

Run the tests of crates/k-rust/tests/alpha_invariance.rs (every test by default, the ignored ones
included; a TEST is a test name filter such as the_whole_generated_grammar) in the portable and
the native build. KRUST_GATE_Z3 selects how the native build acquires Z3 as for the reference
gates (gh-release, the default, downloads the release; system links the Z3 the environment
provides), KRUST_GATE_TARGET_DIR the target directory (default target/gates),
ALPHA_INVARIANCE_JOBS the worker threads of each test (default: the available parallelism, at
most 4), and
ALPHA_INVARIANCE_OUT a directory for one TSV line per result. The whole corpus also compiles the
manifest's cases in the k and imp-semantics checkouts beside the workspace when they are present
(K_CHECKOUT, IMP_SEMANTICS_CHECKOUT). Exit status 0 when every result matches the harness's
expected failures in both builds, 1 otherwise, 2 on a usage error.
EOF_USAGE
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

harness() {
  cargo test --locked --manifest-path "$workspace/Cargo.toml" --target-dir "$target_dir" \
    -p k-rust --no-default-features "$@" --test alpha_invariance -- --include-ignored \
    --test-threads 1 --show-output "${tests[@]}"
}

tests=("$@")
echo "[alpha-invariance] portable build" >&2
harness || exit 1
echo "[alpha-invariance] native build (features $native_features)" >&2
harness --features "$native_features" || exit 1
