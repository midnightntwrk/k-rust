#!/usr/bin/env bash
# shellcheck disable=SC2034  # the pins are consumed by the scripts that source this file

reference_scripts=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
reference_manifest_json=$("$reference_scripts/reference-manifest.py")
K_REFERENCE_REVISION=$(jq -r '.reference.k.revision' <<<"$reference_manifest_json")
K_REFERENCE_VERSION=$(jq -r '.reference.k.version' <<<"$reference_manifest_json")
IMP_REFERENCE_REVISION=$(jq -r '.reference.imp.revision' <<<"$reference_manifest_json")
WASM_REFERENCE_REVISION=$(jq -r '.reference.wasm.revision' <<<"$reference_manifest_json")
EVM_EQUIVALENCE_REFERENCE_REVISION=$(jq -r '.reference["evm-equivalence"].revision' <<<"$reference_manifest_json")
EVM_SEMANTICS_REFERENCE_REVISION=$(jq -r '.reference.kevm.revision' <<<"$reference_manifest_json")
EVM_PLUGIN_REFERENCE_REVISION=$(jq -r '.reference["kevm-plugin"].revision' <<<"$reference_manifest_json")
MIR_REFERENCE_REVISION=$(jq -r '.reference.mir.revision' <<<"$reference_manifest_json")
readonly K_REFERENCE_REVISION K_REFERENCE_VERSION IMP_REFERENCE_REVISION WASM_REFERENCE_REVISION EVM_EQUIVALENCE_REFERENCE_REVISION EVM_SEMANTICS_REFERENCE_REVISION EVM_PLUGIN_REFERENCE_REVISION MIR_REFERENCE_REVISION

# Runs git on the repository at $1. `git -C` only changes the directory git discovers a
# repository from; an inherited GIT_DIR, GIT_WORK_TREE or other repository-local variable
# still names the repository, and `git bisect run` and `git rebase --exec` export GIT_DIR
# when run in a linked worktree. Clearing those variables makes every call read the checkout
# it names.
reference_git() (
  local checkout=$1
  local -a repository_variables
  shift
  mapfile -t repository_variables < <(git rev-parse --local-env-vars)
  unset "${repository_variables[@]}"
  git -c safe.directory="$checkout" -C "$checkout" "$@"
)

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
  if ! actual=$(reference_git "$checkout" rev-parse HEAD 2>/dev/null); then
    echo "error: could not read the $name reference revision: $checkout" >&2
    return 2
  fi
  if [[ "$actual" != "$expected" ]]; then
    echo "error: $name reference revision is $actual; expected $expected" >&2
    return 2
  fi
  changes=$(reference_git "$checkout" status --short --untracked-files=no)
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
