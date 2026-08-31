#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
evm_checkout=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
evm_equivalence_checkout=${EVM_EQUIVALENCE_CHECKOUT:-"$workspace/evm-equivalence"}
mir_checkout=${MIR_SEMANTICS_CHECKOUT:-"$workspace/mir-semantics"}
kompile=${K_KOMPILE:-}
kast=${K_KAST:-}
reference_memory_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-}
manifest_json=$(
  WORKSPACE="$workspace" \
  K_CHECKOUT="$k_checkout" \
  IMP_SEMANTICS_CHECKOUT="$imp_checkout" \
  WASM_SEMANTICS_CHECKOUT="$wasm_checkout" \
  EVM_SEMANTICS_CHECKOUT="$evm_checkout" \
  EVM_EQUIVALENCE_CHECKOUT="$evm_equivalence_checkout" \
  MIR_SEMANTICS_CHECKOUT="$mir_checkout" \
    "$workspace/scripts/reference-manifest.py"
)

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
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-kast-differential.XXXXXX")
trap 'find "$work" -depth -delete' EXIT

mapfile -t cases < <(
  jq -r '.kast[] |
    select((.requires | index("semantics-support")) == null) | [
    .name,
    .source,
    .["main-module"],
    .["parser-module"],
    (.include // ""),
    (.["markdown-selector"] // ""),
    (.["syntax-module"] // ""),
    ((.["hook-namespaces"] // []) | join(" "))
  ] | join("\u001f")' <<<"$manifest_json"
)
selected_count=0

for fixture in "${cases[@]}"; do
  IFS=$'\x1f' read -r name source main_module parser_module include selector syntax_module hook_namespaces <<<"$fixture"
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
  case "$name" in
    imp)
      reference_require_git_pin IMP "$imp_checkout" "$IMP_REFERENCE_REVISION"
      ;;
    wasm)
      reference_require_git_pin WASM "$wasm_checkout" "$WASM_REFERENCE_REVISION"
      ;;
    evm-equivalence)
      reference_require_git_pin evm-equivalence "$evm_equivalence_checkout" \
        "$EVM_EQUIVALENCE_REFERENCE_REVISION"
      reference_require_git_pin KEVM "$evm_checkout" "$EVM_SEMANTICS_REFERENCE_REVISION"
      reference_require_git_pin KEVM-plugin \
        "$evm_checkout/kevm-pyk/src/kevm_pyk/kproj/plugin" \
        "$EVM_PLUGIN_REFERENCE_REVISION"
      ;;
    mir)
      reference_require_git_pin MIR "$mir_checkout" "$MIR_REFERENCE_REVISION"
      ;;
  esac

  reference="$work/$name/reference"
  mkdir -p "$reference"
  include_args=()
  selector_args=()
  syntax_args=()
  hook_args=()
  if [[ -n "$include" ]]; then
    include_args=(-I "$include")
  fi
  if [[ -n "$selector" ]]; then
    selector_args=(--md-selector "$selector")
  fi
  if [[ -n "$syntax_module" ]]; then
    syntax_args=(--syntax-module "$syntax_module")
  fi
  if [[ -n "$hook_namespaces" ]]; then
    hook_args=(--hook-namespaces "$hook_namespaces")
  fi

  echo "[$name] compiling the reference parser"
  (
    if [[ -n "$reference_memory_kib" ]]; then
      ulimit -v "$reference_memory_kib"
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
      "${hook_args[@]}" \
      --warnings none
  )

  mapfile -t parse_cases < <(
    jq -r --arg name "$name" '.kast[] | select(.name == $name) | .accept[] |
      [.name, .sort, (if .file then "@" + .file else .expression end)] |
      join("\u001f")' <<<"$manifest_json"
  )

  rust_batch_args=()
  for parse_fixture in "${parse_cases[@]}"; do
    IFS=$'\x1f' read -r parse_name parse_sort parse_expression <<<"$parse_fixture"
    if [[ "$parse_expression" == @* ]]; then
      parse_expression=$(<"${parse_expression#@}")
    fi
    echo "[$name:$parse_name] parsing with reference kast"
    (
      if [[ -n "$reference_memory_kib" ]]; then
        ulimit -v "$reference_memory_kib"
      fi
      if [[ -n "$reference_k_opts" ]]; then
        export K_OPTS="$reference_k_opts"
      fi
      "$kast" \
        --definition "$reference/kompiled" \
        --module "$parser_module" \
        --sort "$parse_sort" \
        --expression "$parse_expression" \
        --output json \
        --warnings none >"$work/$name/reference-$parse_name.json"
    )
    rust_batch_args+=(--batch-case "$parse_name" "$parse_sort" "$parse_expression")
  done

  mapfile -t rejected_cases < <(
    jq -r --arg name "$name" '.kast[] | select(.name == $name) | .reject[] |
      [.name, .sort, (if .file then "@" + .file else .expression end)] |
      join("\u001f")' <<<"$manifest_json"
  )
  for rejected_fixture in "${rejected_cases[@]}"; do
    IFS=$'\x1f' read -r rejected_name rejected_sort rejected_case <<<"$rejected_fixture"
    if [[ "$rejected_case" == @* ]]; then
      rejected_case=$(<"${rejected_case#@}")
    fi
    rust_batch_args+=(--batch-reject-case "$rejected_name" "$rejected_sort" "$rejected_case")
  done

  echo "[$name] parsing the corpus with one krust kast frontend session"
  (
    if [[ -n "$rust_memory_kib" ]]; then
      ulimit -v "$rust_memory_kib"
    fi
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
      kast "$source" \
      --module "$parser_module" \
      "${rust_batch_args[@]}" \
      --output json \
      --backend rust \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$name/rust-batch.json"
  )

  for parse_fixture in "${parse_cases[@]}"; do
    IFS=$'\x1f' read -r parse_name _ <<<"$parse_fixture"
    echo "[$name:$parse_name] comparing structural KAST"
    K_REFERENCE_KAST="$work/$name/reference-$parse_name.json" \
      K_RUST_KAST="$work/$name/rust-batch.json" \
      K_RUST_KAST_CASE="$parse_name" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        parsed_kast_matches_the_reference_frontend
  done

  for rejected_fixture in "${rejected_cases[@]}"; do
    IFS=$'\x1f' read -r rejected_name rejected_sort rejected_case <<<"$rejected_fixture"
    if [[ "$rejected_case" == @* ]]; then
      rejected_case=$(<"${rejected_case#@}")
    fi
    echo "[$name:$rejected_name] checking rejection agreement"
    if (
      if [[ -n "$reference_memory_kib" ]]; then
        ulimit -v "$reference_memory_kib"
      fi
      if [[ -n "$reference_k_opts" ]]; then
        export K_OPTS="$reference_k_opts"
      fi
      "$kast" \
        --definition "$reference/kompiled" \
        --module "$parser_module" \
        --sort "$rejected_sort" \
        --expression "$rejected_case" \
        --output json \
        --warnings none >"$work/$name/reference-rejected-$rejected_name.json" \
        2>"$work/$name/reference-rejected-$rejected_name.log"
    ); then
      echo "error: reference kast unexpectedly accepted $name:$rejected_name rejection fixture" >&2
      exit 1
    fi
  done
done

if (($# && selected_count != $#)); then
  echo "error: one or more requested corpus cases are unknown" >&2
  echo "available cases: $(jq -r '[.kast[] |
    select((.requires | index("semantics-support")) == null) | .name] |
    join(" ")' <<<"$manifest_json")" >&2
  exit 2
fi

echo "reference KAST differential corpus passed"
