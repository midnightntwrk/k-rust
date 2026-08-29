#!/usr/bin/env bash

readonly K_REFERENCE_REVISION=4a46d1231473b599c699160132fd6e76a5c46406
readonly K_REFERENCE_VERSION=v7.1.337
readonly IMP_REFERENCE_REVISION=683a773418add3bcae8ded47c2b24e94494e1988
readonly WASM_REFERENCE_REVISION=212271bd434bd402e27c42f6416854342733386d
readonly EVM_EQUIVALENCE_REFERENCE_REVISION=3a757eb6f88000047d6fd064d6b72b78b6e23592
readonly EVM_SEMANTICS_REFERENCE_REVISION=5dd05ea7936c13f4029389bafd25785ed9ff0a55
readonly EVM_PLUGIN_REFERENCE_REVISION=651a2db5afc1789c89553f9113c1afa39e391e35
readonly MIR_REFERENCE_REVISION=4d793252bcd77091ee759ca6cd1629db41ed5496

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
