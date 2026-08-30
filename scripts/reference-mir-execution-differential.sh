#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
mir_checkout=${MIR_SEMANTICS_CHECKOUT:-"$workspace/mir-semantics"}
kompile=${K_KOMPILE:-}
kmir_python=${KMIR_PYTHON:-"$mir_checkout/kmir/.venv/bin/python"}

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
krun=${K_KRUN:-"$(dirname "$kompile")/krun"}
if [[ ! -x "$krun" ]]; then
  echo "error: missing matching pinned reference executable: $krun" >&2
  exit 2
fi
if [[ ! -x "$kmir_python" ]]; then
  echo "error: set KMIR_PYTHON to the pinned kmir environment's Python executable" >&2
  exit 2
fi

source_path="$mir_checkout/kmir/src/kmir/kdist/mir-semantics/kmir.md"
include_path="$mir_checkout/kmir/src/kmir/kdist"
smir_path="$mir_checkout/kmir/src/tests/integration/data/exec-smir/main-a-b-c/main-a-b-c.smir.json"
builtin_path="$k_checkout/k-distribution/include/kframework/builtin"
for path in "$source_path" "$smir_path"; do
  if [[ ! -f "$path" ]]; then
    echo "error: missing pinned MIR input: $path" >&2
    exit 2
  fi
done
for path in "$include_path" "$builtin_path"; do
  if [[ ! -d "$path" ]]; then
    echo "error: missing pinned include directory: $path" >&2
    exit 2
  fi
done

reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"
reference_require_git_pin MIR "$mir_checkout" "$MIR_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-mir-execution.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "MIR differential artifacts retained at: $work"' EXIT
else
  trap 'find "$work" -depth -delete' EXIT
fi
reference_definition="$work/reference-kompiled"
rust_definition="$work/rust-kompiled"
initial="$work/main-a-b-c.initial.kore"
reference_result="$work/main-a-b-c.reference.kore"
rust_result="$work/main-a-b-c.rust.kore"

echo "[mir] compiling the pinned concrete Haskell definition"
"$kompile" "$source_path" \
  --backend haskell \
  --main-module KMIR \
  --syntax-module KMIR-AST \
  --output-definition "$reference_definition" \
  --emit-json \
  -I "$include_path" \
  --md-selector 'k & ! symbolic' \
  --warnings none

echo "[mir] compiling the same concrete definition with k-rust"
cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
  -p k-rust --bin krust -- \
  kcompile "$source_path" \
  --main-module KMIR \
  --syntax-module KMIR-AST \
  --backend llvm \
  --output-directory "$rust_definition" \
  -I "$include_path" \
  --md-selector 'k & ! symbolic' \
  --builtin-directory "$builtin_path"

echo "[mir] generating one shared raw initial KORE pattern from pinned SMIR"
"$kmir_python" "$workspace/scripts/reference-mir-initial.py" \
  "$reference_definition" "$smir_path" "$initial"

echo "[mir] executing the shared pattern with the pinned Haskell backend"
"$krun" "$initial" \
  --definition "$reference_definition" \
  --term \
  --parser cat \
  --output kore \
  >"$reference_result"

echo "[mir] executing the shared pattern with k-rust"
cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
  -p k-rust --bin krust -- \
  kore-exec "$rust_definition/definition.kore" \
  --module KMIR \
  --pattern "$initial" \
  >"$rust_result"

K_REFERENCE_EXECUTION="$reference_result" \
  K_RUST_EXECUTION="$rust_result" \
  cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --test reference_differential -- --ignored --exact \
    executed_kore_matches_the_reference_backend

echo "reference MIR shared-KORE execution differential passed"
