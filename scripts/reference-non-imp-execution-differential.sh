#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
kompile=${K_KOMPILE:-}
krun=${K_KRUN:-}
kast=${K_KAST:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-8388608}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_retries=${REFERENCE_EXECUTION_RETRIES:-3}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2'}
manifest_json=$(
  WORKSPACE="$workspace" K_CHECKOUT="$k_checkout" \
  IMP_SEMANTICS_CHECKOUT="$imp_checkout" \
    "$workspace/scripts/reference-manifest.py"
)

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
  shift
  local attempt
  for ((attempt = 1; attempt <= reference_retries; attempt++)); do
    if (
      ulimit -v "$reference_memory_kib"
      export GHCRTS=${GHCRTS:--N1}
      export K_OPTS="$reference_k_opts"
      "$krun" "$@" >"$output"
    ); then
      return 0
    fi
    rm -f "$output"
    if ((attempt < reference_retries)); then
      echo "reference krun preprocessing failed; retrying ($attempt/$reference_retries)" >&2
    fi
  done
  return 1
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

  mapfile -t programs < <(jq -r '(.programs // [])[]' <<<"$suite")
  for program in "${programs[@]}"; do
    program_name=$(basename "$program")
    echo "[$name:$program_name] executing with reference krun"
    run_reference_krun "$work/$name-$program_name.reference.kore" \
      "$program" \
      --definition "$definition" \
      --parser "$workspace/scripts/reference-kast-parser.sh" \
      "${configuration_args[@]}" \
      --depth "$execution_depth" \
      --smt none \
      --output kore

    echo "[$name:$program_name] executing with krust krun"
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
        --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
        >"$work/$name-$program_name.rust.kore"
    )

    K_REFERENCE_EXECUTION="$work/$name-$program_name.reference.kore" \
      K_RUST_EXECUTION="$work/$name-$program_name.rust.kore" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        executed_kore_matches_the_reference_backend
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
        --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
        >"$work/$name-$search_name.rust.kore"
    )

    K_REFERENCE_EXECUTION="$work/$name-$search_name.reference.kore" \
      K_RUST_EXECUTION="$work/$name-$search_name.rust.kore" \
      cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
        -p k-rust --test reference_differential -- --ignored --exact \
        executed_kore_matches_the_reference_backend
  done
done

echo "reference local execution differential corpus passed"
