#!/usr/bin/env bash
# Decides which path-triggered CI checks a push or pull request needs.
#
# usage: scripts/ci-changed-paths.sh --push BEFORE AFTER [--forced]
#        scripts/ci-changed-paths.sh --pull-request BASE HEAD
#        scripts/ci-changed-paths.sh --all
#
# Prints one `CHECK=true|false` line per check, the format of `$GITHUB_OUTPUT`, and explains
# each decision on standard error. Whenever the changed files cannot be determined exactly (a
# new branch, a force push, a commit missing from the clone), every check runs: a check skipped
# by mistake is a silent loss, while a check run by mistake costs only time.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

# Each check's trigger paths, as extended regular expressions over repository-relative paths.
# The workflow files and this script define the checks, so a change to them runs every check.
definition_paths=(
  '^\.github/workflows/(ci|nightly)\.yml$'
  '^scripts/ci-changed-paths\.sh$'
)

# The portable feature set compiles the `not(feature = "z3-inference")` side of k-rust, the
# `not(feature = "z3")` side of the backend, and the WebAssembly bindings that ship it. Any
# source of those crates (including the prelude and parser sources k-rust embeds), any manifest
# that selects features, and the nextest profile the suite runs under can change its result.
portable_suite_paths=(
  '^crates/k-rust/src/'
  '^crates/k-rust/builtin/'
  '^crates/k-rust/cparser/'
  '^crates/k-rust-backend/src/'
  '^crates/k-rust-wasm/'
  '^crates/[^/]+/Cargo\.toml$'
  '^Cargo\.(toml|lock)$'
  '^\.config/nextest\.toml$'
)

# The acquisition check reads the dependency and feature graphs from the manifests, and runs one
# named `inner_rules` test and the CLI on `examples/z3-inference.k` against the system library.
z3_acquisition_paths=(
  '^crates/[^/]+/Cargo\.toml$'
  '^Cargo\.(toml|lock)$'
  '^scripts/z3-acquisition-check\.sh$'
  '^crates/k-rust/tests/z3_acquisition\.rs$'
  '^crates/k-rust/tests/inner_rules\.rs$'
  '^examples/z3-inference\.k$'
)

checks=(portable-suite z3-acquisition)

trigger_paths() {
  case $1 in
    portable-suite) printf '%s\n' "${portable_suite_paths[@]}" ;;
    z3-acquisition) printf '%s\n' "${z3_acquisition_paths[@]}" ;;
  esac
}

usage() {
  sed -n '4,6s/^# //p' "${BASH_SOURCE[0]}" >&2
  exit 2
}

git_in() {
  git -C "$workspace" "$@"
}

is_commit() {
  [[ -n $1 ]] && git_in cat-file -e "$1^{commit}" 2>/dev/null
}

run_everything() {
  echo "every path-triggered check runs: $1" >&2
  local check
  for check in "${checks[@]}"; do
    echo "$check=true"
  done
  exit 0
}

# Prints the first changed file that matches one of the given patterns, if any.
first_match() {
  local file pattern
  for file in "${changed[@]}"; do
    for pattern in "$@" "${definition_paths[@]}"; do
      if [[ $file =~ $pattern ]]; then
        echo "$file"
        return 0
      fi
    done
  done
  return 1
}

(( $# >= 1 )) || usage
case $1 in
  --all)
    (( $# == 1 )) || usage
    run_everything "requested"
    ;;
  --push)
    (( $# == 3 || $# == 4 )) || usage
    before=$2 after=$3
    if (( $# == 4 )); then
      [[ $4 == --forced ]] || usage
      run_everything "the push rewrote the branch's history"
    fi
    if [[ -z $before || $before =~ ^0+$ ]]; then
      run_everything "the push created the branch, so there is no previous commit to compare with"
    fi
    is_commit "$after" || { echo "error: the pushed commit $after is not in the clone" >&2; exit 1; }
    is_commit "$before" || run_everything "the previous commit $before is not in the clone"
    git_in merge-base --is-ancestor "$before" "$after" \
      || run_everything "the previous commit $before is not an ancestor of $after"
    base=$before head=$after
    ;;
  --pull-request)
    (( $# == 3 )) || usage
    head=$3
    is_commit "$head" || { echo "error: the pull request head $head is not in the clone" >&2; exit 1; }
    is_commit "$2" || run_everything "the pull request base $2 is not in the clone"
    base=$(git_in merge-base "$2" "$head") \
      || run_everything "the pull request base $2 and head $head share no history"
    ;;
  *)
    usage
    ;;
esac

# Without rename detection a moved file appears under both its old and its new path, so moving
# a file out of a trigger path triggers too.
mapfile -t changed < <(git_in diff --name-only --no-renames "$base" "$head")
echo "${#changed[@]} files changed between $base and $head" >&2

for check in "${checks[@]}"; do
  mapfile -t patterns < <(trigger_paths "$check")
  if trigger=$(first_match "${patterns[@]}"); then
    echo "$check runs: $trigger changed" >&2
    echo "$check=true"
  else
    echo "$check is skipped: no trigger path changed" >&2
    echo "$check=false"
  fi
done
