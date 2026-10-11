#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"
source "$workspace/scripts/reference-cache.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
evm_checkout=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
evm_equivalence_checkout=${EVM_EQUIVALENCE_CHECKOUT:-"$workspace/evm-equivalence"}
mir_checkout=${MIR_SEMANTICS_CHECKOUT:-"$workspace/mir-semantics"}
kompile=${K_KOMPILE:-}
kast=${K_KAST:-}
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
  for requested in "$@"; do
    selected_case=$(jq -c --arg name "$requested" \
      '.kast[] | select(.name == $name and ((.requires | index("semantics-support")) == null))' \
      <<<"$manifest_json")
    if [[ -z "$selected_case" ]]; then
      echo "error: unknown runnable KAST case: $requested" >&2
      echo "available cases: $(jq -r '[.kast[] |
        select((.requires | index("semantics-support")) == null) | .name] |
        join(" ")' <<<"$manifest_json")" >&2
      exit 2
    fi
  done
fi

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
kdep=${K_KDEP:-"$(dirname "$kompile")/kdep"}
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-kast-differential.XXXXXX")
trap 'find "$work" -depth -delete' EXIT

# The structural comparison of one parse, by the comparator test binary built once below.
compare_artifacts() {
  (
    cd "$workspace/crates/k-rust"
    "$reference_comparator" --quiet --ignored --exact "$@"
  )
}

# parse_entries KIND
#   Prints one line per KIND entry (accept, reject, port-accepts or port-rejects) of the current
#   case: its name, its sort and its text field (see entry_text), separated by U+001F.
parse_entries() {
  jq -r --arg name "$name" --arg kind "$1" '.kast[] | select(.name == $name) |
    (.[$kind] // [])[] |
    [.name, .sort, (if .file then "@" + .file else "=" + (.expression | @base64) end)] |
    join("\u001f")' <<<"$manifest_json"
}

# entry_text VARIABLE FIELD
#   Sets VARIABLE to the text a parse entry gives: `@PATH` is the contents of a file, `=BASE64` an
#   inline expression. The expression travels base64-encoded because the entries are read one per
#   line, and it keeps every line end it has, a trailing one included, since a token regex anchor
#   reads them.
entry_text() {
  local text
  case $2 in
    @*) text=$(<"${2#@}") ;;
    =*) text=$(base64 -d <<<"${2#=}" && printf .) && text=${text%.} ;;
    *) return 2 ;;
  esac
  printf -v "$1" '%s' "$text"
}

# reference_parse ENTRY SORT TEXT OUTPUT
#   Parses TEXT at SORT with the pinned kast and the reference parser of the current case, writing
#   the KAST JSON to OUTPUT and the diagnostics to OUTPUT.log; returns kast's exit status.
reference_parse() {
  (
    if [[ -n "$reference_memory_kib" ]]; then
      ulimit -v "$reference_memory_kib"
    fi
    if [[ -n "$reference_k_opts" ]]; then
      export K_OPTS="$reference_k_opts"
    fi
    reference_cached kast "$name:$1" --input "$reference/kompiled" -- \
      "$kast" \
      --definition "$reference/kompiled" \
      --module "$parser_module" \
      --sort "$2" \
      --expression "$3" \
      --output json \
      --warnings none >"$4" 2>"$4.log"
  )
}

# divergence_field ENTRY KIND FIELD
#   Prints FIELD of the KIND (port-accepts or port-rejects) entry ENTRY of the current case.
divergence_field() {
  jq -r --arg name "$name" --arg entry "$1" --arg kind "$2" --arg field "$3" \
    '.kast[] | select(.name == $name) | .[$kind][] | select(.name == $entry) | .[$field]' \
    <<<"$manifest_json"
}

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

reference_announce_krust_gate_build
reference_run_rust_frontend cargo build --quiet --release "${krust_gate_cargo_args[@]}" \
  --manifest-path "$workspace/Cargo.toml" -p k-rust --bin krust
reference_comparator=$(reference_build_comparator "$workspace" "${krust_gate_z3_args[@]}")
reference_cache_begin "$work"
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
    reference_cached kompile "$name" --output-root . --kdep "$kdep" -- \
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

  mapfile -t parse_cases < <(parse_entries accept)
  mapfile -t rejected_cases < <(parse_entries reject)
  mapfile -t port_accepted_cases < <(parse_entries port-accepts)
  mapfile -t port_rejected_cases < <(parse_entries port-rejects)

  for parse_fixture in "${parse_cases[@]}"; do
    IFS=$'\x1f' read -r parse_name parse_sort parse_field <<<"$parse_fixture"
    entry_text parse_expression "$parse_field"
    echo "[$name:$parse_name] parsing with reference kast"
    if ! reference_parse "$parse_name" "$parse_sort" "$parse_expression" \
      "$work/$name/reference-$parse_name.json"; then
      cat "$work/$name/reference-$parse_name.json.log" >&2
      echo "error: reference kast rejected $name:$parse_name acceptance fixture" >&2
      exit 1
    fi
  done

  # krust must accept every accept and port-accepts entry and reject every reject and
  # port-rejects entry; the session fails otherwise.
  rust_batch_args=()
  for parse_fixture in "${parse_cases[@]}" "${port_accepted_cases[@]}"; do
    IFS=$'\x1f' read -r parse_name parse_sort parse_field <<<"$parse_fixture"
    entry_text parse_expression "$parse_field"
    rust_batch_args+=(--batch-case "$parse_name" "$parse_sort" "$parse_expression")
  done
  for rejected_fixture in "${rejected_cases[@]}" "${port_rejected_cases[@]}"; do
    IFS=$'\x1f' read -r rejected_name rejected_sort rejected_field <<<"$rejected_fixture"
    entry_text rejected_case "$rejected_field"
    rust_batch_args+=(--batch-reject-case "$rejected_name" "$rejected_sort" "$rejected_case")
  done

  echo "[$name] parsing the corpus with one krust kast frontend session"
  reference_run_rust_frontend "$krust_gate_binary" \
    kast "$source" \
    --module "$parser_module" \
    "${rust_batch_args[@]}" \
    --output json \
    --backend rust \
    "${include_args[@]}" \
    "${selector_args[@]}" \
    --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
    >"$work/$name/rust-batch.json"

  for parse_fixture in "${parse_cases[@]}"; do
    IFS=$'\x1f' read -r parse_name _ <<<"$parse_fixture"
    echo "[$name:$parse_name] comparing structural KAST"
    K_REFERENCE_KAST="$work/$name/reference-$parse_name.json" \
      K_RUST_KAST="$work/$name/rust-batch.json" \
      K_RUST_KAST_CASE="$parse_name" \
      compare_artifacts parsed_kast_matches_the_reference_frontend
  done

  for rejected_fixture in "${rejected_cases[@]}"; do
    IFS=$'\x1f' read -r rejected_name rejected_sort rejected_field <<<"$rejected_fixture"
    entry_text rejected_case "$rejected_field"
    echo "[$name:$rejected_name] checking rejection agreement"
    if reference_parse "$rejected_name" "$rejected_sort" "$rejected_case" \
      "$work/$name/reference-rejected-$rejected_name.json"; then
      echo "error: reference kast unexpectedly accepted $name:$rejected_name rejection fixture" >&2
      exit 1
    fi
  done

  # A recorded divergence pins both sides, so it fails when either moves: krust's side is the
  # session above, the reference's side is checked here (a port-accepts rejection by the
  # diagnostic it records, not only by its exit status).
  for divergence in "${port_accepted_cases[@]}"; do
    IFS=$'\x1f' read -r divergence_name divergence_sort divergence_field <<<"$divergence"
    entry_text divergence_text "$divergence_field"
    reason=$(divergence_field "$divergence_name" port-accepts reason)
    reference_error=$(divergence_field "$divergence_name" port-accepts reference-error)
    log="$work/$name/reference-port-accepts-$divergence_name.json.log"
    echo "[$name:$divergence_name] recorded divergence: $reason"
    if reference_parse "$divergence_name" "$divergence_sort" "$divergence_text" \
      "$work/$name/reference-port-accepts-$divergence_name.json"; then
      echo "error: reference kast accepted port-accepts case $name:$divergence_name; the recorded divergence is gone" >&2
      exit 1
    fi
    echo "[$name:$divergence_name] reference rejection: $(grep -m1 -E '\[Error\]|error:' "$log" || head -n1 "$log")"
    if ! grep -qF -- "$reference_error" "$log"; then
      cat "$log" >&2
      echo "error: reference kast rejection of port-accepts case $name:$divergence_name changed: its output lacks the recorded reference-error \"$reference_error\"" >&2
      exit 1
    fi
  done
  for divergence in "${port_rejected_cases[@]}"; do
    IFS=$'\x1f' read -r divergence_name divergence_sort divergence_field <<<"$divergence"
    entry_text divergence_text "$divergence_field"
    reason=$(divergence_field "$divergence_name" port-rejects reason)
    echo "[$name:$divergence_name] recorded divergence: $reason"
    if ! reference_parse "$divergence_name" "$divergence_sort" "$divergence_text" \
      "$work/$name/reference-port-rejects-$divergence_name.json"; then
      cat "$work/$name/reference-port-rejects-$divergence_name.json.log" >&2
      echo "error: reference kast rejected port-rejects case $name:$divergence_name; the recorded divergence is gone" >&2
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

reference_cache_finish
echo "reference KAST differential corpus passed"
