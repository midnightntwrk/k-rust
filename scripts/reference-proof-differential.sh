#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
kprove=${K_KPROVE:-}
reference_memory_kib=${REFERENCE_EXECUTION_MEMORY_KIB:-12582912}
rust_memory_kib=${RUST_DIFFERENTIAL_MEMORY_KIB:-6291456}
reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2'}
manifest_json=$(
  WORKSPACE="$workspace" K_CHECKOUT="$k_checkout"     "$workspace/scripts/reference-manifest.py"
)

if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
if [[ -z "$kprove" ]]; then
  kprove=$(dirname "$kompile")/kprove
fi
if [[ ! -x "$kprove" ]]; then
  echo "error: set K_KPROVE to the matching pinned reference kprove executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-reference-proof.XXXXXX")
if [[ "${REFERENCE_DIFFERENTIAL_KEEP_WORK:-0}" == 1 ]]; then
  trap 'echo "proof artifacts retained at: '"$work"'"' EXIT
else
  trap 'find "'"$work"'" -depth -delete' EXIT
fi

mapfile -t available < <(
  jq -r '.proof[] |
    select((.requires | index("semantics-support")) == null) | .name' <<<"$manifest_json"
)
selected=("${available[@]}")
if (($#)); then
  selected=("$@")
fi

for name in "${selected[@]}"; do
  if ! printf '%s\n' "${available[@]}" | grep -Fxq "$name"; then
    echo "error: unknown runnable local proof case: $name" >&2
    echo "available cases: ${available[*]}" >&2
    exit 2
  fi
  proof=$(jq -c --arg name "$name" '.proof[] | select(.name == $name)' <<<"$manifest_json")
  semantics=$(jq -r '.source' <<<"$proof")
  main_module=$(jq -r '.["main-module"]' <<<"$proof")
  syntax_module=$(jq -r '.["syntax-module"]' <<<"$proof")
  specification=$(jq -r '.specification' <<<"$proof")
  spec_module=$(jq -r '.["spec-module"]' <<<"$proof")
  definition_module=$(jq -r '.["definition-module"]' <<<"$proof")
  proof_depth=$(jq -r '.depth' <<<"$proof")
  if [[ ! -f "$semantics" || ! -f "$specification" ]]; then
    echo "error: missing local proof fixture for $name" >&2
    exit 2
  fi
  semantics_dir=$(dirname "$semantics")
  definition="$work/$name-kompiled"

  echo "[$name] compiling the reference Haskell definition"
  (
    ulimit -v "$reference_memory_kib"
    export GHCRTS=${GHCRTS:--N1}
    export K_OPTS="$reference_k_opts"
    "$kompile" "$semantics"       --backend haskell       --main-module "$main_module"       --syntax-module "$syntax_module"       --output-definition "$definition"       --warnings none
  )

  mapfile -t proven_claims < <(jq -r '.claims[]' <<<"$proof")
  failure_claim=$(jq -r '.["failure-claim"]' <<<"$proof")
  for claim in "${proven_claims[@]}"; do
    echo "[$name:$claim] checking the reference proven verdict"
    (
      ulimit -v "$reference_memory_kib"
      export GHCRTS=${GHCRTS:--N1}
      export K_OPTS="$reference_k_opts"
      "$kprove" "$specification"         --definition "$definition"         --spec-module "$spec_module"         --claims "$claim"         --depth "$proof_depth"         --output none         --warnings none         -I "$semantics_dir"
    ) >"$work/$name-$claim.reference.log" 2>&1

    echo "[$name:$claim] checking the k-rust proven verdict"
    (
      ulimit -v "$rust_memory_kib"
      cargo run --quiet --release --manifest-path "$workspace/Cargo.toml"         -p k-rust --bin krust --         kprove "$specification"         --main-module "$spec_module"         --definition-module "$definition_module"         --claim "$claim"         --depth "$proof_depth"         -I "$semantics_dir"         --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin"
    ) >"$work/$name-$claim.rust.log" 2>&1
    if ! grep -Fq "claim $claim: proven" "$work/$name-$claim.rust.log"; then
      echo "error: k-rust did not report the proven verdict for $name:$claim" >&2
      cat "$work/$name-$claim.rust.log" >&2
      exit 1
    fi
  done

  echo "[$name:$failure_claim] checking the reference refuted verdict"
  if (
    ulimit -v "$reference_memory_kib"
    export GHCRTS=${GHCRTS:--N1}
    export K_OPTS="$reference_k_opts"
    "$kprove" "$specification"       --definition "$definition"       --spec-module "$spec_module"       --claims "$failure_claim"       --depth "$proof_depth"       --output none       --warnings none       -I "$semantics_dir"
  ) >"$work/$name-$failure_claim.reference.log" 2>&1; then
    echo "error: reference kprove unexpectedly proved $name:$failure_claim" >&2
    exit 1
  fi
  if ! grep -Fq "backend terminated because the configuration cannot be"     "$work/$name-$failure_claim.reference.log"; then
    echo "error: reference kprove failed unexpectedly for $name:$failure_claim" >&2
    cat "$work/$name-$failure_claim.reference.log" >&2
    exit 1
  fi

  echo "[$name:$failure_claim] checking the k-rust refuted verdict"
  if (
    ulimit -v "$rust_memory_kib"
    cargo run --quiet --release --manifest-path "$workspace/Cargo.toml"       -p k-rust --bin krust --       kprove "$specification"       --main-module "$spec_module"       --definition-module "$definition_module"       --claim "$failure_claim"       --depth "$proof_depth"       -I "$semantics_dir"       --builtin-directory "$k_checkout/k-distribution/include/kframework/builtin"
  ) >"$work/$name-$failure_claim.rust.log" 2>&1; then
    echo "error: k-rust unexpectedly proved $name:$failure_claim" >&2
    exit 1
  fi
  if ! grep -Fq "claim $failure_claim: disproved" "$work/$name-$failure_claim.rust.log"; then
    echo "error: k-rust did not report the refuted verdict for $name:$failure_claim" >&2
    cat "$work/$name-$failure_claim.rust.log" >&2
    exit 1
  fi
done

echo "reference local proof differential corpus passed"
