#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
imp_checkout=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
krun=${K_KRUN:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-12582912}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_retries=${REFERENCE_EXECUTION_RETRIES:-3}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=4 -Dscala.concurrent.context.maxThreads=4'}

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

semantics="$imp_checkout/src/kimp/kdist/imp-semantics/imp.k"
examples="$imp_checkout/examples"
if [[ ! -f "$semantics" ]]; then
  echo "error: set IMP_SEMANTICS_CHECKOUT to the pinned IMP checkout" >&2
  exit 2
fi

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
    --main-module IMP \
    --syntax-module IMP-SYNTAX \
    --output-definition "$work/kompiled" \
    --warnings none
)

cases=(
  sumto10.imp
  while-and-following.imp
  dangling-else.imp
)

for program in "${cases[@]}"; do
  if [[ ! -f "$examples/$program" ]]; then
    echo "error: missing IMP execution fixture: $examples/$program" >&2
    exit 2
  fi

  echo "[imp:$program] executing with reference krun"
  run_reference_krun "$work/$program.reference.kore" \
    "$examples/$program" \
    --definition "$work/kompiled" \
    -cENV=.Map \
    --depth 10000 \
    --smt none \
    --output kore

  echo "[imp:$program] executing with krust krun"
  (
    ulimit -v "$rust_memory_kib"
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --bin krust -- \
      krun "$semantics" \
      --main-module IMP \
      --sort Stmt \
      "$examples/$program" \
      -cENV=.Map \
      --depth 10000 \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$program.rust.kore"
  )

  echo "[imp:$program] comparing terminal KORE"
  K_REFERENCE_EXECUTION="$work/$program.reference.kore" \
    K_RUST_EXECUTION="$work/$program.rust.kore" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      executed_kore_matches_the_reference_backend
done

search_program=sumto10.imp
search_cases=(
  "one|--search-one-step|"
  "star-depth-two|--search-all|2"
)

for fixture in "${search_cases[@]}"; do
  IFS='|' read -r name mode depth <<<"$fixture"
  depth_args=()
  if [[ -n "$depth" ]]; then
    depth_args=(--depth "$depth")
  fi

  echo "[imp:$search_program:$name] searching with reference krun"
  run_reference_krun "$work/$search_program.$name.reference.kore" \
    "$examples/$search_program" \
    --definition "$work/kompiled" \
    -cENV=.Map \
    "$mode" \
    "${depth_args[@]}" \
    --smt none \
    --output kore

  echo "[imp:$search_program:$name] searching with krust krun"
  (
    ulimit -v "$rust_memory_kib"
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --bin krust -- \
      krun "$semantics" \
      --main-module IMP \
      --sort Stmt \
      "$examples/$search_program" \
      -cENV=.Map \
      "$mode" \
      "${depth_args[@]}" \
      --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin" \
      >"$work/$search_program.$name.rust.kore"
  )

  echo "[imp:$search_program:$name] comparing search KORE"
  K_REFERENCE_EXECUTION="$work/$search_program.$name.reference.kore" \
    K_RUST_EXECUTION="$work/$search_program.$name.rust.kore" \
    cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
      -p k-rust --test reference_differential -- --ignored --exact \
      executed_kore_matches_the_reference_backend
done

echo "reference IMP execution and search differential corpus passed"
