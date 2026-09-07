#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
kompile=${K_KOMPILE:-}
krun=${K_KRUN:-}
kast=${K_KAST:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-8388608}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_retries=${REFERENCE_EXECUTION_RETRIES:-3}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-$reference_default_k_opts}
manifest_json=$(
  WORKSPACE="$workspace" K_CHECKOUT="$k_checkout" \
  IMP_SEMANTICS_CHECKOUT="$imp_checkout" \
    "$workspace/scripts/reference-manifest.py"
)

if (($#)); then
  for requested in "$@"; do
    selected_case=$(jq -c --arg name "$requested" \
      '.execution[] | select(.name == $name and ((.requires | index("semantics-support")) == null))' \
      <<<"$manifest_json")
    if [[ -z "$selected_case" ]]; then
      echo "error: unknown runnable local execution case: $requested" >&2
      echo "available cases: $(jq -r '[.execution[] |
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
if [[ -z "$krun" ]]; then
  krun=$(dirname "$kompile")/krun
fi
kast=${kast:-"$(dirname "$kompile")/kast"}
for tool in "$krun" "$kast"; do
  if [[ ! -x "$tool" ]]; then
    echo "error: missing matching pinned reference executable: $tool" >&2
    exit 2
  fi
done
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-execution.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "differential artifacts retained at: $work"' EXIT
else
  trap 'find "$work" -depth -delete' EXIT
fi

run_reference_krun() {
  local output=$1
  local expected_status=$2
  shift 2
  local attempt status
  for ((attempt = 1; attempt <= reference_retries; attempt++)); do
    set +e
    (
      ulimit -v "$reference_memory_kib"
      export GHCRTS=${GHCRTS:--N1}
      export K_OPTS="$reference_k_opts"
      "$krun" "$@" >"$output"
    )
    status=$?
    set -e
    if ((status == expected_status)); then
      return 0
    fi
    rm -f "$output"
    if ((attempt < reference_retries)); then
      echo "reference krun exited $status instead of $expected_status; retrying ($attempt/$reference_retries)" >&2
    fi
  done
  echo "error: reference krun exited $status instead of $expected_status" >&2
  return 1
}

compare_execution() {
  local reference=$1
  local actual=$2
  local definition=$3
  local module=$4
  K_REFERENCE_EXECUTION="$reference" \
    K_RUST_EXECUTION="$actual" \
    K_DIFFERENTIAL_DEFINITION="$definition" \
    K_DIFFERENTIAL_MODULE="$module" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      executed_kore_matches_the_reference_backend
}

mapfile -t available < <(
  jq -r '.execution[] |
    select((.requires | index("semantics-support")) == null) | .name' <<<"$manifest_json"
)
selected=("${available[@]}")
if (($#)); then
  selected=("$@")
fi

for name in "${selected[@]}"; do
  if ! printf '%s\n' "${available[@]}" | grep -Fxq "$name"; then
    echo "error: unknown runnable local execution case: $name" >&2
    echo "available cases: ${available[*]}" >&2
    exit 2
  fi
  suite=$(jq -c --arg name "$name" '.execution[] | select(.name == $name)' <<<"$manifest_json")
  source=$(jq -r '.source' <<<"$suite")
  main_module=$(jq -r '.["main-module"]' <<<"$suite")
  syntax_module=$(jq -r '.["syntax-module"]' <<<"$suite")
  program_sort=$(jq -r '.sort' <<<"$suite")
  export K_KAST="$kast"
  export KAST_PROGRAM_SORT="$program_sort"
  execution_depth=$(jq -r '.depth' <<<"$suite")
  expected_exit_code=$(jq -r '.["exit-code"] // 0' <<<"$suite")
  mapfile -t configuration_args < <(
    jq -r '(.configuration // [])[] | "-c" + .' <<<"$suite"
  )
  mapfile -t hook_namespaces < <(
    jq -r '(.["hook-namespaces"] // [])[]' <<<"$suite"
  )
  hook_args=()
  if ((${#hook_namespaces[@]})); then
    hook_args=(--hook-namespaces "${hook_namespaces[*]}")
  fi
  if [[ ! -f "$source" ]]; then
    echo "error: missing $name semantics source: $source" >&2
    exit 2
  fi
  if [[ "$name" == imp ]]; then
    reference_require_git_pin IMP "$imp_checkout" "$IMP_REFERENCE_REVISION"
  fi

  definition="$work/$name-kompiled"
  export KAST_DEFINITION="$definition"
  echo "[$name] compiling the reference Haskell definition"
  (
    ulimit -v "$reference_memory_kib"
    export GHCRTS=${GHCRTS:--N1}
    export K_OPTS="$reference_k_opts"
    "$kompile" "$source" \
      --backend haskell \
      --main-module "$main_module" \
      --syntax-module "$syntax_module" \
      --output-definition "$definition" \
      "${hook_args[@]}" \
      --warnings none
  )

  # The oracle is the Haskell backend's krun (kore-exec in its default --strategy all:
  # every applicable rule is explored), so krust runs with --strategy all as well; plain
  # krust krun follows one successor per step; see docs/compatibility.md#search-results.
  mapfile -t programs < <(jq -r '(.programs // [])[]' <<<"$suite")
  for program in "${programs[@]}"; do
    if [[ ! -f "$program" ]]; then
      echo "error: missing $name program: $program" >&2
      exit 2
    fi
    program_name=$(basename "$program")
    echo "[$name:$program_name] executing with reference krun"
    run_reference_krun "$work/$name-$program_name.reference.kore" \
      "$expected_exit_code" \
      "$program" \
      --definition "$definition" \
      --parser "$workspace/scripts/reference-kast-parser.sh" \
      "${configuration_args[@]}" \
      --depth "$execution_depth" \
      --smt none \
      --output kore

    echo "[$name:$program_name] executing with krust krun"
    set +e
    (
      ulimit -v "$rust_memory_kib"
      export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
      cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --bin krust -- \
        krun "$source" \
        --main-module "$main_module" \
        --sort "$program_sort" \
        "$program" \
        "${configuration_args[@]}" \
        --depth "$execution_depth" \
        --strategy all \
        --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
        >"$work/$name-$program_name.rust.kore"
    )
    rust_status=$?
    set -e
    if ((rust_status != expected_exit_code)); then
      echo "error: krust krun exited $rust_status instead of $expected_exit_code" >&2
      exit 1
    fi

    oracle_exception=$(jq -c --arg program "$program" \
      '(."oracle-exception" // [])[] | select(.program == $program)' <<<"$suite")
    if [[ -n "$oracle_exception" ]]; then
      expected=$(jq -r '.expected' <<<"$oracle_exception")
      recorded_reference=$(jq -r '.reference' <<<"$oracle_exception")
      reason=$(jq -r '.reason' <<<"$oracle_exception")
      echo "[$name:$program_name] oracle-exception: $reason"
      compare_execution \
        "$expected" \
        "$work/$name-$program_name.rust.kore" \
        "$definition/definition.kore" \
        "$main_module"
      compare_execution \
        "$recorded_reference" \
        "$work/$name-$program_name.reference.kore" \
        "$definition/definition.kore" \
        "$main_module"
      if compare_execution \
        "$work/$name-$program_name.reference.kore" \
        "$work/$name-$program_name.rust.kore" \
        "$definition/definition.kore" \
        "$main_module" >/dev/null 2>&1; then
        echo "error: oracle exception for $name:$program_name is no longer needed" >&2
        exit 1
      fi
      if compare_execution \
        "$recorded_reference" \
        "$expected" \
        "$definition/definition.kore" \
        "$main_module" >/dev/null 2>&1; then
        echo "error: committed oracle exception expectations for $name:$program_name are equivalent" >&2
        exit 2
      fi
    else
      compare_execution \
        "$work/$name-$program_name.reference.kore" \
        "$work/$name-$program_name.rust.kore" \
        "$definition/definition.kore" \
        "$main_module"
    fi
  done

  mapfile -t searches < <(
    jq -r '(.search // [])[] |
      [.name, .program, .mode, (.depth // ""), (.["result-bound"] // "")] |
      join("\u001f")' <<<"$suite"
  )
  for search in "${searches[@]}"; do
    IFS=$'\x1f' read -r search_name program mode depth result_bound <<<"$search"
    program_name=$(basename "$program")
    depth_args=()
    if [[ -n "$depth" ]]; then
      depth_args=(--depth "$depth")
    fi
    reference_result_bound_args=()
    rust_result_bound_args=()
    if [[ -n "$result_bound" ]]; then
      reference_result_bound_args=(--bound "$result_bound")
      rust_result_bound_args=(--search-bound "$result_bound")
    fi

    echo "[$name:$search_name] searching with reference krun"
    run_reference_krun "$work/$name-$search_name.reference.kore" \
      0 \
      "$program" \
      --definition "$definition" \
      --parser "$workspace/scripts/reference-kast-parser.sh" \
      "${configuration_args[@]}" \
      "$mode" \
      "${depth_args[@]}" \
      "${reference_result_bound_args[@]}" \
      --smt none \
      --output kore

    echo "[$name:$search_name] searching with krust krun"
    (
      ulimit -v "$rust_memory_kib"
      export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
      cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --bin krust -- \
        krun "$source" \
        --main-module "$main_module" \
        --sort "$program_sort" \
        "$program" \
        "${configuration_args[@]}" \
        "$mode" \
        "${depth_args[@]}" \
        "${rust_result_bound_args[@]}" \
        --strategy all \
        --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
        >"$work/$name-$search_name.rust.kore"
    )

    compare_execution \
      "$work/$name-$search_name.reference.kore" \
      "$work/$name-$search_name.rust.kore" \
      "$definition/definition.kore" \
      "$main_module"
  done
done

echo "reference local execution differential corpus passed"
