#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
krun=${K_KRUN:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-12582912}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_retries=${REFERENCE_EXECUTION_RETRIES:-3}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=4 -Dscala.concurrent.context.maxThreads=4'}
manifest_json=$(
  WORKSPACE="$workspace" K_CHECKOUT="$k_checkout" IMP_SEMANTICS_CHECKOUT="$imp_checkout" \
    "$workspace/scripts/reference-manifest.py"
)
execution=$(jq -c '.execution[] | select(.name == "imp")' <<<"$manifest_json")

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
if [[ ! -x "$krun" ]]; then
  echo "error: set K_KRUN to the matching pinned reference krun executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi

semantics=$(jq -r '.source' <<<"$execution")
main_module=$(jq -r '.["main-module"]' <<<"$execution")
syntax_module=$(jq -r '.["syntax-module"]' <<<"$execution")
program_sort=$(jq -r '.sort' <<<"$execution")
execution_depth=$(jq -r '.depth' <<<"$execution")
mapfile -t configuration_args < <(
  jq -r '.configuration[] | "-c" + .' <<<"$execution"
)
if [[ ! -f "$semantics" ]]; then
  echo "error: set IMP_SEMANTICS_CHECKOUT to the pinned IMP checkout" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"
reference_require_git_pin IMP "$imp_checkout" "$IMP_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-execution-differential.XXXXXX")
trap 'rm -rf "$work"' EXIT

run_reference_krun() {
  local output=$1
  shift
  local attempt
  for ((attempt = 1; attempt <= reference_retries; attempt++)); do
    if (
      ulimit -v "$reference_memory_kib"
      export GHCRTS=${GHCRTS:--N1}
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

echo "[imp] compiling the reference Haskell definition"
(
  ulimit -v "$reference_memory_kib"
  export GHCRTS=${GHCRTS:--N1}
  export K_OPTS="$reference_k_opts"
  "$kompile" "$semantics" \
    --backend haskell \
    --main-module "$main_module" \
    --syntax-module "$syntax_module" \
    --output-definition "$work/kompiled" \
    --warnings none
)

mapfile -t cases < <(jq -r '.programs[]' <<<"$execution")

for program in "${cases[@]}"; do
  if [[ ! -f "$program" ]]; then
    echo "error: missing IMP execution fixture: $program" >&2
    exit 2
  fi
  program_name=$(basename "$program")

  echo "[imp:$program_name] executing with reference krun"
  run_reference_krun "$work/$program_name.reference.kore" \
    "$program" \
    --definition "$work/kompiled" \
    "${configuration_args[@]}" \
    --depth "$execution_depth" \
    --smt none \
    --output kore

  echo "[imp:$program_name] executing with krust krun"
  (
    ulimit -v "$rust_memory_kib"
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --bin krust -- \
      krun "$semantics" \
      --main-module "$main_module" \
      --sort "$program_sort" \
      "$program" \
      "${configuration_args[@]}" \
      --depth "$execution_depth" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$program_name.rust.kore"
  )

  echo "[imp:$program_name] comparing terminal KORE"
  K_REFERENCE_EXECUTION="$work/$program_name.reference.kore" \
    K_RUST_EXECUTION="$work/$program_name.rust.kore" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      executed_kore_matches_the_reference_backend
done

mapfile -t search_cases < <(
  jq -r '.search[] | [.name, .program, .mode, (.depth // "")] | join("\u001f")' \
    <<<"$execution"
)

for fixture in "${search_cases[@]}"; do
  IFS=$'\x1f' read -r name search_program mode depth <<<"$fixture"
  search_program_name=$(basename "$search_program")
  depth_args=()
  if [[ -n "$depth" ]]; then
    depth_args=(--depth "$depth")
  fi

  echo "[imp:$search_program_name:$name] searching with reference krun"
  run_reference_krun "$work/$search_program_name.$name.reference.kore" \
    "$search_program" \
    --definition "$work/kompiled" \
    "${configuration_args[@]}" \
    "$mode" \
    "${depth_args[@]}" \
    --smt none \
    --output kore

  echo "[imp:$search_program_name:$name] searching with krust krun"
  (
    ulimit -v "$rust_memory_kib"
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --bin krust -- \
      krun "$semantics" \
      --main-module "$main_module" \
      --sort "$program_sort" \
      "$search_program" \
      "${configuration_args[@]}" \
      "$mode" \
      "${depth_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$search_program_name.$name.rust.kore"
  )

  echo "[imp:$search_program_name:$name] comparing search KORE"
  K_REFERENCE_EXECUTION="$work/$search_program_name.$name.reference.kore" \
    K_RUST_EXECUTION="$work/$search_program_name.$name.rust.kore" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      executed_kore_matches_the_reference_backend
done

echo "reference IMP execution and search differential corpus passed"
