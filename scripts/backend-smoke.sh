#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
k_checkout=${K_CHECKOUT:-"$workspace/k"}
backend_bin=${K_BACKEND_BIN:-}

if [[ -z "$backend_bin" && -n "${K_KOMPILE:-}" ]]; then
  backend_bin=$(dirname "$K_KOMPILE")
fi
if [[ -z "$backend_bin" ]]; then
  kore_parser=$(command -v kore-parser || true)
  if [[ -n "$kore_parser" ]]; then
    backend_bin=$(dirname "$kore_parser")
  fi
fi
if [[ -z "$backend_bin" ]]; then
  echo "error: set K_BACKEND_BIN to the pinned K installation's bin directory" >&2
  exit 2
fi
for tool in kore-parser kore-exec llvm-kompile-matching llvm-kompile; do
  if [[ ! -x "$backend_bin/$tool" ]]; then
    echo "error: missing executable $backend_bin/$tool" >&2
    exit 2
  fi
done
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-backend-smoke.XXXXXX")
trap 'rm -rf "$work"' EXIT
builtins="$k_checkout/k-distribution/include/kframework/builtin"

compile_rust() {
  local source=$1
  local module=$2
  local backend=$3
  local output=$4
  shift 4
  cargo run --quiet --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
    kcompile "$source" \
    --main-module "$module" \
    --backend "$backend" \
    --output-directory "$output" \
    --builtin-directory "$builtins" \
    "$@"
}

echo "[haskell] verifying MPFR-folded FLOAT definition"
float_output="$work/float"
compile_rust \
  "$k_checkout/k-distribution/tests/regression-new/f32-mul/float-mul.k" \
  FLOAT-MUL llvm "$float_output"
"$backend_bin/kore-parser" "$float_output/definition.kore" --verify

echo "[haskell] verifying and loading reachability claims"
claims_directory="$k_checkout/k-distribution/tests/regression-new/kprove-var-equals"
claims_output="$work/claims"
compile_rust \
  "$claims_directory/var-eq-spec.k" \
  VAR-EQ-SPEC haskell "$claims_output" \
  -I "$claims_directory"
"$backend_bin/kore-parser" "$claims_output/definition.kore" --verify
claim_count=$(grep -c '^  claim' "$claims_output/definition.kore")
if ((claim_count != 4)); then
  echo "error: expected four emitted reachability claims, found $claim_count" >&2
  exit 1
fi
printf '%s\n' "LblinitGeneratedTopCell{}(Lbl'Stop'Map{}())" >"$work/initial.kore"
"$backend_bin/kore-exec" \
  "$claims_output/definition.kore" \
  --pattern "$work/initial.kore" \
  --module VAR-EQ-SPEC \
  --depth 0 \
  --smt none \
  --no-bug-report \
  --output "$work/haskell-output.kore"
test -s "$work/haskell-output.kore"

echo "[llvm] generating decision trees and a native interpreter"
llvm_output="$work/llvm"
compile_rust \
  "$k_checkout/k-distribution/tests/regression-new/cell_map/test.k" \
  TEST llvm "$llvm_output"
"$backend_bin/kore-parser" "$llvm_output/definition.kore" --verify
mkdir -p "$llvm_output/dt"
"$backend_bin/llvm-kompile-matching" \
  "$llvm_output/definition.kore" qbaL "$llvm_output/dt" 1/2
"$backend_bin/llvm-kompile" \
  "$llvm_output/definition.kore" "$llvm_output/dt" main \
  -o "$llvm_output/interpreter" -- -Wno-unused-command-line-argument
test -x "$llvm_output/interpreter"

echo "Haskell and LLVM backend smoke tests passed"
