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
kore_parser=${K_KORE_PARSER:-}
reference_memory_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-$reference_default_k_opts}
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

if (($#)); then
  all_selected_pending=true
  pending_messages=()
  for requested in "$@"; do
    selected_case=$(jq -c --arg name "$requested" \
      '.compile[] | select(.name == $name and ((.requires | index("semantics-support")) == null))' \
      <<<"$manifest_json")
    if [[ -z "$selected_case" ]]; then
      echo "error: unknown runnable compile case: $requested" >&2
      echo "available cases: $(jq -r '[.compile[] |
        select((.requires | index("semantics-support")) == null) | .name] |
        join(" ")' <<<"$manifest_json")" >&2
      exit 2
    fi
    blocking_tickets=$(jq -r \
      '[.requires[] | select(startswith("ticket:")) | ltrimstr("ticket:")] | join(", ")' \
      <<<"$selected_case")
    if [[ -z "$blocking_tickets" || "${REFERENCE_DIFFERENTIAL_PENDING:-0}" == 1 ]]; then
      all_selected_pending=false
    else
      pending_messages+=("[$requested] pending: blocked by $blocking_tickets")
    fi
  done
  if [[ "$all_selected_pending" == true ]]; then
    printf '%s\n' "${pending_messages[@]}"
    echo "reference differential corpus passed"
    exit 0
  fi
fi

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
kore_parser=${kore_parser:-"$(dirname "$kompile")/kore-parser"}
if [[ ! -x "$kore_parser" ]]; then
  echo "error: set K_KORE_PARSER to the matching pinned kore-parser executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

requested_pairings=${REFERENCE_DIFFERENTIAL_PAIRINGS:-}
requested_pairings=${requested_pairings//,/ }
for pairing in $requested_pairings; do
  if [[ "$pairing" != kore/llvm && "$pairing" != haskell/rust ]]; then
    echo "error: unknown REFERENCE_DIFFERENTIAL_PAIRINGS value: $pairing" >&2
    exit 2
  fi
done

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-differential.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "differential artifacts retained at: $work"' EXIT
else
  trap 'find "$work" -depth -delete' EXIT
fi

run_reference_tool() (
  if [[ -n "$reference_memory_kib" ]]; then
    ulimit -v "$reference_memory_kib"
  fi
  export K_OPTS="$reference_k_opts"
  "$@"
)

pairing_is_requested() {
  local candidate=$1
  local requested
  if [[ -z "$requested_pairings" ]]; then
    return 0
  fi
  for requested in $requested_pairings; do
    if [[ "$requested" == "$candidate" ]]; then
      return 0
    fi
  done
  return 1
}

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
    ((.comparisons // []) | join(" ")),
    ((.pairings // ["kore/llvm", "haskell/rust"]) | join(" ")),
    (.expect // "accept"),
    ([.requires[] | select(startswith("ticket:")) | ltrimstr("ticket:")] | join(", ")),
    (.["unique-id-divergence-ceilings"]["kore/llvm"] // -1),
    (.["unique-id-divergence-ceilings"]["haskell/rust"] // -1)
  ] | join("\u001f")' <<<"$manifest_json"
)
ignore_unique_id_ticket=$(jq -r '.normalisations.ignore_unique_id // ""' <<<"$manifest_json")
selected_count=0

for fixture in "${cases[@]}"; do
  IFS=$'\x1f' read -r name source module include selector syntax_module hook_namespaces \
    comparisons pairings expect blocking_tickets kore_ceiling haskell_ceiling <<<"$fixture"
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
  if [[ -n "$blocking_tickets" && "${REFERENCE_DIFFERENTIAL_PENDING:-0}" != 1 ]]; then
    echo "[$name] pending: blocked by $blocking_tickets"
    continue
  fi
  if [[ ! -f "$source" ]]; then
    echo "error: missing corpus source: $source" >&2
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

  pairing_count=0
  for pairing in $pairings; do
    if ! pairing_is_requested "$pairing"; then
      continue
    fi
    pairing_count=$((pairing_count + 1))
    case "$pairing" in
      kore/llvm)
        reference_backend=kore
        rust_backend=llvm
        ceiling=$kore_ceiling
        ;;
      haskell/rust)
        reference_backend=haskell
        rust_backend=rust
        ceiling=$haskell_ceiling
        ;;
      *)
        echo "error: case $name declares unknown pairing $pairing" >&2
        exit 2
        ;;
    esac
    pairing_key=${pairing//\//-}
    reference="$work/$name/$pairing_key/reference"
    rust="$work/$name/$pairing_key/rust"
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
    elif [[ "$pairing" == haskell/rust && "$source" == *.md ]]; then
      selector_args=(--md-selector 'k & ! concrete')
    fi
    if [[ -n "$syntax_module" ]]; then
      syntax_args=(--syntax-module "$syntax_module")
    fi
    if [[ -n "$hook_namespaces" ]]; then
      reference_hook_args=(--hook-namespaces "$hook_namespaces")
      rust_hook_args=(--hook-namespaces "${hook_namespaces// /,}")
    fi

    echo "[$name:$pairing] compiling with reference frontend"
    set +e
    (
      cd "$reference"
      run_reference_tool "$kompile" "$source" \
        --backend "$reference_backend" \
        --main-module "$module" \
        --output-definition kompiled \
        "${include_args[@]}" \
        "${selector_args[@]}" \
        "${syntax_args[@]}" \
        "${reference_hook_args[@]}" \
        --emit-json \
        --warnings none
    ) >"$work/$name/$pairing_key/reference.log" 2>&1
    reference_status=$?

    echo "[$name:$pairing] compiling with k-rust"
    reference_run_rust_frontend cargo run --quiet --release \
      --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust -- \
      kcompile "$source" \
      --main-module "$module" \
      --backend "$rust_backend" \
      --output-directory "$rust" \
      --emit-json \
      "${include_args[@]}" \
      "${selector_args[@]}" \
      "${syntax_args[@]}" \
      "${rust_hook_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$name/$pairing_key/rust.log" 2>&1
    rust_status=$?
    set -e

    if [[ "$expect" == reject ]]; then
      echo "[$name:$pairing] reference rejection: $(grep -m1 -E '\[Error\]|error:' "$work/$name/$pairing_key/reference.log" || head -n1 "$work/$name/$pairing_key/reference.log")"
      echo "[$name:$pairing] k-rust rejection: $(head -n1 "$work/$name/$pairing_key/rust.log")"
      if ((reference_status == 0 || rust_status == 0)); then
        echo "error: reject case $name must be rejected by both compilers for $pairing" >&2
        exit 1
      fi
      continue
    fi
    if ((reference_status != 0)); then
      cat "$work/$name/$pairing_key/reference.log" >&2
      echo "error: reference frontend rejected accept case $name for $pairing" >&2
      exit 1
    fi
    if ((rust_status != 0)); then
      cat "$work/$name/$pairing_key/rust.log" >&2
      echo "error: k-rust rejected accept case $name for $pairing" >&2
      exit 1
    fi

    if [[ "$pairing" == haskell/rust ]]; then
      semantic_reference="$reference/kompiled/definition.kore"
    else
      semantic_reference="$reference/$(basename "${source%.*}").kore"
    fi

    if [[ "${REFERENCE_DIFFERENTIAL_VERIFY:-1}" == 0 ]]; then
      echo "[$name:$pairing] warning: definition verification disabled explicitly"
    else
      echo "[$name:$pairing] verifying reference definition.kore"
      if ! run_reference_tool "$kore_parser" "$semantic_reference" \
        >"$work/$name/$pairing_key/verify-reference.log" 2>&1; then
        cat "$work/$name/$pairing_key/verify-reference.log" >&2
        echo "error: reference definition rejected by kore-parser" >&2
        exit 2
      fi
      echo "[$name:$pairing] verifying k-rust definition.kore"
      if ! run_reference_tool "$kore_parser" "$rust/definition.kore" \
        >"$work/$name/$pairing_key/verify-rust.log" 2>&1; then
        cat "$work/$name/$pairing_key/verify-rust.log" >&2
        echo "error: k-rust definition rejected by kore-parser" >&2
        exit 1
      fi
    fi

    if [[ "$pairing" == haskell/rust ]]; then
      effective_comparisons="semantic-kore"
    else
      effective_comparisons=$comparisons
    fi
    if [[ " $effective_comparisons " == *" semantic-kore "* ]]; then
      echo "[$name:$pairing] comparing semantic KORE"
      compare_environment=()
      if [[ ",$blocking_tickets," != *",$ignore_unique_id_ticket,"* ]]; then
        compare_environment=(K_DIFFERENTIAL_IGNORE_UNIQUE_ID=1)
      fi
      if ! comparison_output=$(env \
        "${compare_environment[@]}" \
        K_REFERENCE_KORE="$semantic_reference" \
        K_RUST_KORE="$rust/definition.kore" \
        cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
          -p k-rust --test reference_differential -- --ignored --exact \
          emitted_kore_matches_the_reference_frontend --nocapture 2>&1); then
        printf '%s\n' "$comparison_output" >&2
        exit 1
      fi
      printf '%s\n' "$comparison_output"
      unique_id_divergences=$(sed -n 's/^unique-id divergences: \([0-9][0-9]*\)$/\1/p' <<<"$comparison_output" | tail -n1)
      unique_id_divergences=${unique_id_divergences:-0}
      if [[ -n "$ignore_unique_id_ticket" ]]; then
        echo "[$name:$pairing] unique-id divergences ignored ($ignore_unique_id_ticket pending): $unique_id_divergences"
        if ((ceiling < 0)); then
          echo "error: case $name has no UNIQUE_ID divergence ceiling for $pairing" >&2
          exit 2
        fi
        if ((unique_id_divergences > ceiling)); then
          echo "error: $name $pairing has $unique_id_divergences UNIQUE_ID divergences, above its pinned ceiling $ceiling" >&2
          exit 1
        fi
        if ((unique_id_divergences < ceiling)); then
          echo "[$name:$pairing] UNIQUE_ID ceiling can improve from $ceiling to $unique_id_divergences"
        fi
      fi
    fi
    if [[ "$pairing" == kore/llvm && " $effective_comparisons " == *" syntax-kore "* ]]; then
      echo "[$name:$pairing] comparing syntax KORE"
      K_REFERENCE_KORE="$reference/kompiled/syntaxDefinition.kore" \
        K_RUST_KORE="$rust/syntaxDefinition.kore" \
        cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
          -p k-rust --test reference_differential -- --ignored --exact \
          emitted_kore_matches_the_reference_frontend
    fi
    if [[ "$pairing" == kore/llvm && " $effective_comparisons " == *" macro-kore "* ]]; then
      echo "[$name:$pairing] comparing macro KORE"
      K_REFERENCE_KORE="$reference/kompiled/macros.kore" \
        K_RUST_KORE="$rust/macros.kore" \
        cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
          -p k-rust --test reference_differential -- --ignored --exact \
          emitted_macro_kore_matches_the_reference_frontend
    fi
    if [[ "$pairing" == kore/llvm && " $effective_comparisons " == *" parsed-definition "* ]]; then
      echo "[$name:$pairing] comparing parsed definitions"
      K_REFERENCE_DEFINITION="$reference/kompiled/parsed.json" \
        K_RUST_DEFINITION="$rust/parsed.json" \
        cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
          -p k-rust --test reference_differential -- --ignored --exact \
          parsed_definition_matches_the_reference_frontend
    fi
  done
  if ((pairing_count == 0)); then
    echo "error: no requested pairing applies to compile case $name" >&2
    exit 2
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
