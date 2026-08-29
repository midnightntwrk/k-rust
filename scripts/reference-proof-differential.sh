#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
kprove=${K_KPROVE:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-12582912}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=4 -Dscala.concurrent.context.maxThreads=4'}

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
if [[ -z "$kprove" ]]; then
  kprove=$(dirname "$kompile")/kprove
fi
if [[ ! -x "$kprove" ]]; then
  echo "error: set K_KPROVE to the matching pinned reference kprove executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

semantics_dir="$imp_checkout/src/kimp/kdist/imp-semantics"
semantics="$semantics_dir/imp.k"
specification="$imp_checkout/examples/specs/imp-simple-spec.k"
if [[ ! -f "$semantics" || ! -f "$specification" ]]; then
  echo "error: set IMP_SEMANTICS_CHECKOUT to the pinned IMP checkout" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"
reference_require_git_pin IMP "$imp_checkout" "$IMP_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-proof-differential.XXXXXX")
trap 'rm -rf "$work"' EXIT

echo "[imp] compiling the reference Haskell definition"
(
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  export K_OPTS="$reference_k_opts"
  "$kompile" "$semantics" \
    --backend haskell \
    --main-module IMP \
    --syntax-module IMP-SYNTAX \
    --output-definition "$work/kompiled" \
    --warnings none
)

claims=(
  IMP-SIMPLE-SPEC.addition-1
  IMP-SIMPLE-SPEC.addition-2
  IMP-SIMPLE-SPEC.addition-var
  IMP-SIMPLE-SPEC.pre-branch-proved
  IMP-SIMPLE-SPEC.branching
  IMP-SIMPLE-SPEC.branching-program
  IMP-SIMPLE-SPEC.branching-deadcode
  IMP-SIMPLE-SPEC.while-cut-rule
  IMP-SIMPLE-SPEC.while-cut-rule-delayed
  IMP-SIMPLE-SPEC.sum-loop
  IMP-SIMPLE-SPEC.sum-N
)
failure_claim=IMP-SIMPLE-SPEC.bmc-loop-concrete
claim_csv=$(IFS=,; echo "${claims[*]}")

echo "[imp] proving selected claims with reference kprove"
(
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  export K_OPTS="$reference_k_opts"
  "$kprove" "$specification" \
    --definition "$work/kompiled" \
    --spec-module IMP-SIMPLE-SPEC \
    --claims "$claim_csv" \
    --depth 100 \
    --output none \
    --warnings none \
    -I "$semantics_dir"
)

echo "[imp] checking the reference counterexample outcome for $failure_claim"
if (
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  export K_OPTS="$reference_k_opts"
  "$kprove" "$specification" \
    --definition "$work/kompiled" \
    --spec-module IMP-SIMPLE-SPEC \
    --claims "$failure_claim" \
    --depth 100 \
    --output none \
    --warnings none \
    -I "$semantics_dir" \
    >"$work/reference-failure.log" 2>&1
); then
  echo "error: reference kprove unexpectedly proved $failure_claim" >&2
  exit 1
fi
if ! grep -Fq "backend terminated because the configuration cannot be" \
  "$work/reference-failure.log"; then
  echo "error: reference kprove failed unexpectedly for $failure_claim" >&2
  cat "$work/reference-failure.log" >&2
  exit 1
fi

echo "[imp] proving selected claims with krust kprove"
rust_claim_args=()
for claim in "${claims[@]}"; do
  rust_claim_args+=(--claim "$claim")
done
(
  ulimit -v "$rust_memory_kib"
  cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust -- \
    kprove "$specification" \
    --main-module IMP-SIMPLE-SPEC \
    --definition-module IMP-VERIFICATION \
    "${rust_claim_args[@]}" \
    --depth 100 \
    -I "$semantics_dir" \
    --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
    >"$work/rust-proof.log"
)

for claim in "${claims[@]}"; do
  if ! grep -Fq "claim $claim: proven" "$work/rust-proof.log"; then
    echo "error: krust did not prove $claim" >&2
    cat "$work/rust-proof.log" >&2
    exit 1
  fi
done

echo "[imp] checking the Rust counterexample outcome for $failure_claim"
if (
  ulimit -v "$rust_memory_kib"
  cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust -- \
    kprove "$specification" \
    --main-module IMP-SIMPLE-SPEC \
    --definition-module IMP-VERIFICATION \
    --claim "$failure_claim" \
    --depth 100 \
    -I "$semantics_dir" \
    --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
    >"$work/rust-failure.log" 2>&1
); then
  echo "error: krust unexpectedly proved $failure_claim" >&2
  exit 1
fi
if ! grep -Fq "claim $failure_claim: disproved" "$work/rust-failure.log"; then
  echo "error: krust did not reproduce the counterexample outcome for $failure_claim" >&2
  cat "$work/rust-failure.log" >&2
  exit 1
fi

echo "reference IMP proof differential corpus passed"
