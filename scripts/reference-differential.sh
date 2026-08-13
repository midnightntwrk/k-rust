#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-differential.XXXXXX")
trap 'rm -rf "$work"' EXIT

cases=(
  "append|k/k-distribution/tests/regression-new/append/test.k|TEST"
  "ambiguous-rewrite|k/k-distribution/tests/regression-new/amb-rew/test.k|TEST"
  "casts|k/k-distribution/tests/regression-new/cast/test.k|TEST"
  "cell-map|k/k-distribution/tests/regression-new/cell_map/test.k|TEST"
  "fresh-variables|k/k-distribution/tests/regression-new/fresh1/test.k|TEST"
  "list-set|k/k-distribution/tests/regression-new/list-set/test.k|TEST"
  "macro-rewrite|k/k-distribution/tests/regression-new/macro-rewrite/test.k|TEST"
)
selected_count=0

for fixture in "${cases[@]}"; do
  IFS='|' read -r name relative_source module <<<"$fixture"
  selected=true
  if (($#)); then
    selected=false
    for requested in "$@"; do
      if [[ "$requested" == "$name" ]]; then
        selected=true
      fi
    done
  fi
  if [[ "$selected" != true ]]; then
    continue
  fi
  selected_count=$((selected_count + 1))
  source="$workspace/$relative_source"
  reference="$work/$name/reference"
  rust="$work/$name/rust"
  mkdir -p "$reference" "$rust"

  echo "[$name] compiling with reference frontend"
  (
    cd "$reference"
    "$kompile" "$source" \
      --backend kore \
      --main-module "$module" \
      --output-definition kompiled \
      --warnings none
  )

  echo "[$name] compiling with k-rust"
  cargo run --quiet --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
    kcompile "$source" \
    --main-module "$module" \
    --backend llvm \
    --output-directory "$rust" \
    --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin"

  echo "[$name] comparing structural KORE"
  K_REFERENCE_KORE="$reference/$(basename "${source%.k}").kore" \
    K_RUST_KORE="$rust/definition.kore" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      emitted_kore_matches_the_reference_frontend
done

if (($# && selected_count != $#)); then
  echo "error: one or more requested corpus cases are unknown" >&2
  echo "available cases: append ambiguous-rewrite casts cell-map fresh-variables list-set macro-rewrite" >&2
  exit 2
fi

echo "reference differential corpus passed"
