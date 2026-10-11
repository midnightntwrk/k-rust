#!/usr/bin/env bash
# The two feature sets of k-rust compile one language (crates/k-rust/tests/build_agreement.rs):
# compile the manifest's compile cases through the library in the native (`z3-inference`) build,
# then in the portable build, and fail on every case they compile differently, on every case
# expected to compile that a build did not compile, and on every portable refusal
# (`Z3InferenceRequired`) that differs from the recorded set.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
refused=
cases=()

usage() {
  cat <<'EOF'
usage: scripts/build-agreement.sh [--refused CASE,...] [CASE...]

Compare the native and the portable build of k-rust on the named compile CASEs of
scripts/reference-differential.toml, by default on every compile case: the ones in the workspace
and the real-semantics ones (wasm, mir, evm-equivalence), whose checkouts resolve as the
reference gates resolve them (WASM_SEMANTICS_CHECKOUT, MIR_SEMANTICS_CHECKOUT,
EVM_SEMANTICS_CHECKOUT, default beside the workspace).

  --refused CASE,...  the cases the portable build is expected to refuse with
                      Z3InferenceRequired (default none); any other refusal fails, and so does a
                      listed case the portable build compiles

KRUST_GATE_Z3 selects how the native build acquires Z3 as for the reference gates (gh-release,
the default, downloads the release; system links the Z3 the environment provides), and
KRUST_GATE_TARGET_DIR its target directory (default target/gates). Exit status 0 when the
builds agree, 1 when they do not or a build fails, 2 on a usage error.
EOF
}

while (($# > 0)); do
  case $1 in
    --refused)
      (($# >= 2)) || { usage >&2; exit 2; }
      refused=$2
      shift 2
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    -*)
      usage >&2
      exit 2
      ;;
    *)
      cases+=("$1")
      shift
      ;;
  esac
done

case ${KRUST_GATE_Z3:-gh-release} in
  gh-release) native_features=z3-inference-gh-release ;;
  system) native_features=z3-inference ;;
  *)
    echo "error: KRUST_GATE_Z3 must be gh-release or system" >&2
    exit 2
    ;;
esac
target_dir=${KRUST_GATE_TARGET_DIR:-$workspace/target/gates}

if ((${#cases[@]} > 0)); then
  selected=$(IFS=,; echo "${cases[*]}")
  export BUILD_AGREEMENT_CASES=$selected
  unset BUILD_AGREEMENT_REAL_SEMANTICS
else
  unset BUILD_AGREEMENT_CASES
  export BUILD_AGREEMENT_REAL_SEMANTICS=1
fi
unset BUILD_AGREEMENT_RECORD BUILD_AGREEMENT_COMPARE BUILD_AGREEMENT_REFUSED

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Only the inference engine differs between the two runs: neither enables `mpfr-folding` or the
# CLI, which the native build's default features would add.
agreement() {
  cargo test --release --locked --manifest-path "$workspace/Cargo.toml" --target-dir "$target_dir" \
    -p k-rust --no-default-features "$@" --test build_agreement \
    -- --ignored --exact both_builds_compile_every_local_manifest_case_alike --nocapture
}

echo "[build-agreement] native build (features $native_features)" >&2
BUILD_AGREEMENT_RECORD=$work/native.tsv agreement --features "$native_features" || exit 1
echo "[build-agreement] portable build, expected refusals: ${refused:-none}" >&2
BUILD_AGREEMENT_COMPARE=$work/native.tsv BUILD_AGREEMENT_REFUSED=$refused agreement || exit 1
