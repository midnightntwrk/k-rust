#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-backend-smoke.XXXXXX")
trap 'rm -rf "$work"' EXIT

krust() {
  cargo run --quiet --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- "$@"
}

echo "[rust] compiling backend KORE artifacts"
rust_output="$work/rust"
krust kcompile "$workspace/examples/rewrite.k" \
  --main-module REWRITE \
  --output-directory "$rust_output"
for artifact in definition.kore syntaxDefinition.kore macros.kore; do
  test -s "$rust_output/$artifact"
done

echo "[rust] executing with the in-process backend"
execution=$(krust krun "$workspace/examples/rewrite.k" \
  --main-module REWRITE \
  --sort State \
  --expression a \
  --depth 10)
grep -q 'Lblb{}()' <<<"$execution"

echo "[rust] matching equal builtin Lists through the full frontend/backend path"
list_execution=$(krust krun "$workspace/examples/list-unification.k" \
  --main-module LIST-UNIFICATION \
  --sort Val \
  --expression test1 \
  --depth 10)
grep -q "Lblsuccess'Unds'LIST-UNIFICATION'Unds'Val{}()" <<<"$list_execution"
test "$(grep -c 'LblListItem{}' <<<"$list_execution")" -eq 6

echo "[rust] proving a reachability claim with in-process Z3"
proof=$(krust kprove "$workspace/examples/reachability.k" \
  --main-module REACHABILITY \
  --claim reaches-b \
  --depth 10)
grep -q 'claim reaches-b: proven' <<<"$proof"

backend_bin=${K_BACKEND_BIN:-}
if [[ -z "$backend_bin" && -n "${K_KOMPILE:-}" ]]; then
  backend_bin=$(dirname "$K_KOMPILE")
fi
if [[ -z "$backend_bin" ]]; then
  echo "[llvm] skipped; set K_BACKEND_BIN to exercise the secondary LLVM target"
  echo "In-process Rust backend smoke tests passed"
  exit 0
fi

for tool in llvm-kompile-matching llvm-kompile; do
  if [[ ! -x "$backend_bin/$tool" ]]; then
    echo "error: missing executable $backend_bin/$tool" >&2
    exit 2
  fi
done

k_checkout=${K_CHECKOUT:-"$workspace/k"}
builtins="$k_checkout/k-distribution/include/kframework/builtin"
if [[ ! -d "$builtins" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

echo "[llvm] generating decision trees and a native interpreter"
llvm_output="$work/llvm"
krust kcompile \
  "$k_checkout/k-distribution/tests/regression-new/cell_map/test.k" \
  --main-module TEST \
  --backend llvm \
  --output-directory "$llvm_output" \
  --builtin-directory "$builtins"
mkdir -p "$llvm_output/dt"
"$backend_bin/llvm-kompile-matching" \
  "$llvm_output/definition.kore" qbaL "$llvm_output/dt" 1/2
"$backend_bin/llvm-kompile" \
  "$llvm_output/definition.kore" "$llvm_output/dt" main \
  -o "$llvm_output/interpreter" -- -Wno-unused-command-line-argument
test -x "$llvm_output/interpreter"

echo "In-process Rust and LLVM backend smoke tests passed"
