#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
evm_checkout=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
evm_equivalence_checkout=${EVM_EQUIVALENCE_CHECKOUT:-"$workspace/evm-equivalence"}
mir_checkout=${MIR_SEMANTICS_CHECKOUT:-"$workspace/mir-semantics"}
kompile=${K_KOMPILE:-}
reference_memory_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}
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
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-differential.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "differential artifacts retained at: $work"' EXIT
else
  trap 'find "$work" -depth -delete' EXIT
fi

mapfile -t cases < <(
  jq -r '.compile[] |
    select((.requires | index("semantics-support")) == null) | [
    .name,
    .source,
    .["main-module"],
    (.include // ""),
    (.["markdown-selector"] // ""),
    (.["syntax-module"] // ""),
    ((.["hook-namespaces"] // []) | join(" ")),
    (.comparisons | join(" "))
  ] | join("\u001f")' <<<"$manifest_json"
)
selected_count=0

for fixture in "${cases[@]}"; do
  IFS=$'\x1f' read -r name source module include selector syntax_module hook_namespaces comparisons <<<"$fixture"
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
    case "$name" in
      imp)
        echo "error: set IMP_SEMANTICS_CHECKOUT to the pinned IMP semantics checkout (default: $workspace/imp-semantics)" >&2
        ;;
      wasm)
        echo "error: set WASM_SEMANTICS_CHECKOUT to the pinned WASM semantics checkout (default: $workspace/wasm-semantics)" >&2
        ;;
      evm-equivalence)
        echo "error: set EVM_SEMANTICS_CHECKOUT to the pinned EVM semantics checkout (default: $workspace/evm-semantics)" >&2
        ;;
      mir)
        echo "error: set MIR_SEMANTICS_CHECKOUT to the pinned MIR semantics checkout (default: $workspace/mir-semantics)" >&2
        ;;
      *)
        echo "error: missing corpus source: $source" >&2
        ;;
    esac
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
  rust="$work/$name/rust"
  mkdir -p "$reference" "$rust"
  include_args=()
  selector_args=()
  syntax_args=()
  reference_hook_args=()
  rust_hook_args=()
  if [[ -n "$include" ]]; then
    if [[ ! -d "$include" ]]; then
      echo "error: missing include directory: $include" >&2
      exit 2
    fi
    include_args=(-I "$include")
  fi
  if [[ -n "$selector" ]]; then
    selector_args=(--md-selector "$selector")
  fi
  if [[ -n "$syntax_module" ]]; then
    syntax_args=(--syntax-module "$syntax_module")
  fi
  if [[ -n "$hook_namespaces" ]]; then
    reference_hook_args=(--hook-namespaces "$hook_namespaces")
    rust_hook_args=(--hook-namespaces "${hook_namespaces// /,}")
  fi

  echo "[$name] compiling with reference frontend"
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
      --main-module "$module" \
      --output-definition kompiled \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      "${syntax_args[@]}" \
      "${reference_hook_args[@]}" \
      --emit-json \
      --warnings none
  )

  echo "[$name] compiling with k-rust"
  reference_run_rust_frontend cargo run --quiet --release \
    --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
    kcompile "$source" \
    --main-module "$module" \
    --backend llvm \
    --output-directory "$rust" \
    --emit-json \
    "${include_args[@]}" \
    "${selector_args[@]}" \
    "${syntax_args[@]}" \
    "${rust_hook_args[@]}" \
    --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin"

  if [[ " $comparisons " == *" semantic-kore "* ]]; then
    echo "[$name] comparing semantic KORE"
    K_REFERENCE_KORE="$reference/$(basename "${source%.*}").kore" \
      K_RUST_KORE="$rust/definition.kore" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        emitted_kore_matches_the_reference_frontend
  fi
  if [[ " $comparisons " == *" syntax-kore "* ]]; then
    echo "[$name] comparing syntax KORE"
    K_REFERENCE_KORE="$reference/kompiled/syntaxDefinition.kore" \
      K_RUST_KORE="$rust/syntaxDefinition.kore" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        emitted_kore_matches_the_reference_frontend
  fi
  if [[ " $comparisons " == *" macro-kore "* ]]; then
    echo "[$name] comparing macro KORE"
    K_REFERENCE_KORE="$reference/kompiled/macros.kore" \
      K_RUST_KORE="$rust/macros.kore" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        emitted_macro_kore_matches_the_reference_frontend
  fi
  if [[ " $comparisons " == *" parsed-definition "* ]]; then
    echo "[$name] comparing parsed definitions"
    K_REFERENCE_DEFINITION="$reference/kompiled/parsed.json" \
      K_RUST_DEFINITION="$rust/parsed.json" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        parsed_definition_matches_the_reference_frontend
  fi
done

if (($# && selected_count != $#)); then
  echo "error: one or more requested corpus cases are unknown" >&2
  echo "available cases: $(jq -r '[.compile[] |
    select((.requires | index("semantics-support")) == null) | .name] |
    join(" ")' <<<"$manifest_json")" >&2
  exit 2
fi

echo "reference differential corpus passed"
