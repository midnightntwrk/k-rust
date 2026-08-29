#!/usr/bin/env bash

reference_scripts=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
reference_manifest_json=$("$reference_scripts/reference-manifest.py")
readonly K_REFERENCE_REVISION=$(jq -r '.reference.k.revision' <<<"$reference_manifest_json")
readonly K_REFERENCE_VERSION=$(jq -r '.reference.k.version' <<<"$reference_manifest_json")
readonly IMP_REFERENCE_REVISION=$(jq -r '.reference.imp.revision' <<<"$reference_manifest_json")
readonly WASM_REFERENCE_REVISION=$(jq -r '.reference.wasm.revision' <<<"$reference_manifest_json")
readonly EVM_EQUIVALENCE_REFERENCE_REVISION=$(jq -r '.reference["evm-equivalence"].revision' <<<"$reference_manifest_json")
readonly EVM_SEMANTICS_REFERENCE_REVISION=$(jq -r '.reference.kevm.revision' <<<"$reference_manifest_json")
readonly EVM_PLUGIN_REFERENCE_REVISION=$(jq -r '.reference["kevm-plugin"].revision' <<<"$reference_manifest_json")
readonly MIR_REFERENCE_REVISION=$(jq -r '.reference.mir.revision' <<<"$reference_manifest_json")

reference_require_git_pin() {
  local name=$1
  local checkout=$2
  local expected=$3
  local actual
  local changes

  if [[ "${REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED:-0}" == 1 ]]; then
    echo "warning: skipping revision check for $name" >&2
    return
  fi
  if [[ ! -e "$checkout/.git" ]]; then
    echo "error: $name reference is not a Git checkout: $checkout" >&2
    return 2
  fi
  if ! actual=$(git -c safe.directory="$checkout" -C "$checkout" rev-parse HEAD 2>/dev/null); then
    echo "error: could not read the $name reference revision: $checkout" >&2
    return 2
  fi
  if [[ "$actual" != "$expected" ]]; then
    echo "error: $name reference revision is $actual; expected $expected" >&2
    return 2
  fi
  changes=$(git -c safe.directory="$checkout" -C "$checkout" \
    status --short --untracked-files=no)
  if [[ -n "$changes" ]]; then
    echo "error: $name reference has tracked modifications: $checkout" >&2
    printf '%s\n' "$changes" >&2
    return 2
  fi
}

reference_require_k_version() {
  local kompile=$1
  local version

  if [[ "${REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED:-0}" == 1 ]]; then
    echo "warning: skipping reference K executable version check" >&2
    return
  fi
  version=$("$kompile" --version | sed -n 's/^K version:[[:space:]]*//p')
  if [[ "$version" != "$K_REFERENCE_VERSION" ]]; then
    echo "error: reference K executable version is ${version:-unknown}; expected $K_REFERENCE_VERSION" >&2
    return 2
  fi
}
