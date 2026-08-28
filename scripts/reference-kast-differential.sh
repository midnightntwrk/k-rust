#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
k_checkout=${K_CHECKOUT:-"$workspace/k"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
evm_checkout=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
mir_checkout=${MIR_SEMANTICS_CHECKOUT:-"$workspace/mir-semantics"}
kompile=${K_KOMPILE:-}
kast=${K_KAST:-}
memory_limit_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-}

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
if [[ -z "$kast" ]]; then
  kast=$(dirname "$kompile")/kast
fi
if [[ ! -x "$kast" ]]; then
  echo "error: set K_KAST to the matching pinned reference kast executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-kast-differential.XXXXXX")
trap 'rm -rf "$work"' EXIT

cases=(
  "wasm|$wasm_checkout/pykwasm/src/pykwasm/kdist/wasm-semantics/test.md|WASM-TEST|WASM-TEST-SYNTAX|ModuleDecl|(module)"
  "evm-equivalence|$evm_checkout/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/optimizations.md|EVM-OPTIMIZATIONS|EVM-OPTIMIZATIONS|Schedule|CANCUN|$evm_checkout/kevm-pyk/src/kevm_pyk/kproj/plugin"
  "mir|$mir_checkout/kmir/src/kmir/kdist/mir-semantics/kmir.md|KMIR|KMIR-AST|Span|span(0)|$mir_checkout/kmir/src/kmir/kdist|k & ! concrete|KMIR-AST"
)
selected_count=0

for fixture in "${cases[@]}"; do
  IFS='|' read -r name source main_module parser_module sort expression include selector syntax_module <<<"$fixture"
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
  if [[ ! -f "$source" ]]; then
    echo "error: missing $name semantics source: $source" >&2
    exit 2
  fi

  reference="$work/$name/reference"
  mkdir -p "$reference"
  include_args=()
  selector_args=()
  syntax_args=()
  if [[ -n "$include" ]]; then
    include_args=(-I "$include")
  fi
  if [[ -n "$selector" ]]; then
    selector_args=(--md-selector "$selector")
  fi
  if [[ -n "$syntax_module" ]]; then
    syntax_args=(--syntax-module "$syntax_module")
  fi

  echo "[$name] compiling the reference parser"
  (
    if [[ -n "$memory_limit_kib" ]]; then
      ulimit -v "$memory_limit_kib"
    fi
    if [[ -n "$reference_k_opts" ]]; then
      export K_OPTS="$reference_k_opts"
    fi
    cd "$reference"
    "$kompile" "$source" \
      --backend kore \
      --main-module "$main_module" \
      --output-definition kompiled \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      "${syntax_args[@]}" \
      --warnings none
  )

  echo "[$name] parsing with reference kast"
  (
    if [[ -n "$memory_limit_kib" ]]; then
      ulimit -v "$memory_limit_kib"
    fi
    if [[ -n "$reference_k_opts" ]]; then
      export K_OPTS="$reference_k_opts"
    fi
    "$kast" \
      --definition "$reference/kompiled" \
      --module "$parser_module" \
      --sort "$sort" \
      --expression "$expression" \
      --output json \
      --warnings none >"$work/$name/reference.json"
  )

  echo "[$name] parsing with krust kast"
  (
    if [[ -n "$memory_limit_kib" ]]; then
      ulimit -v "$memory_limit_kib"
    fi
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
      kast "$source" \
      --module "$parser_module" \
      --sort "$sort" \
      --expression "$expression" \
      --output json \
      --backend rust \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$name/rust.json"
  )

  echo "[$name] comparing structural KAST"
  K_REFERENCE_KAST="$work/$name/reference.json" \
    K_RUST_KAST="$work/$name/rust.json" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      parsed_kast_matches_the_reference_frontend
done

if (($# && selected_count != $#)); then
  echo "error: one or more requested corpus cases are unknown" >&2
  echo "available cases: wasm evm-equivalence mir" >&2
  exit 2
fi

echo "reference KAST differential corpus passed"
