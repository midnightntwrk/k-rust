#!/usr/bin/env bash
# The reference frontend over the K text the class matrix emits (NT-42): Java K's kompile reads
# each batch definition that scripts/krs-class.sh wrote under KRS_CLASS_K_OUT=DIR, and, where it
# refuses one, the definition of each case of that batch alone, so that a refusal names its
# cases. No other check of the class matrix reads the emitted K with an independent frontend
# (K2 judges the class, K3 the `krs expand` closure, K6 the native compile).
#
# Opt-in, and no rule: a refusal is evidence about the K text, to reason about from what the
# sentence means, and the script fails on none. Each verdict is cached by the definition's
# content and the kompile that gave it, under KRS_REFERENCE_FRONTEND_CACHE (default
# ${XDG_CACHE_HOME:-~/.cache}/k-rust/reference-frontend/v1), so a definition is kompiled once.
# Every kompile runs under the reference memory guard with a bounded JVM.
#
# usage: scripts/krs-class-reference-frontend.sh [--jobs N] DIR
#   --jobs N   concurrent kompiles (default: the available memory over 3 GiB, at most 8)
# Writes DIR/reference-frontend.tsv, one line per definition kompiled:
#   batch|case <TAB> ID (the batch's hash, or the case's ID) <TAB> accepted|refused <TAB> message
# and prints the counts and the time taken. Exit status 0 when every definition was judged, 2 on
# a usage or tool error.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
jobs=
while (($#)); do
  case $1 in
    --jobs)
      [[ ${2:-} =~ ^[1-9][0-9]*$ ]] || { echo "error: --jobs takes a positive number" >&2; exit 2; }
      jobs=$2
      shift 2
      ;;
    -h | --help)
      sed -n '2,21p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) break ;;
  esac
done
[[ $# -eq 1 && -d $1 ]] || { echo "usage: $0 [--jobs N] DIR" >&2; exit 2; }
dir=$(cd "$1" && pwd)

# shellcheck source=scripts/reference-memory-guard.sh
source "$here/reference-memory-guard.sh"
reference_enter_whole_job "$@" || exit 2

kompile=${K_KOMPILE:-$(command -v kompile || true)}
[[ -n $kompile && -x $kompile ]] || { echo "error: no kompile: set K_KOMPILE" >&2; exit 2; }
version=$("$kompile" --version 2>/dev/null | head -n 1)
[[ -n $version ]] || { echo "error: $kompile --version printed nothing" >&2; exit 2; }
cache=${KRS_REFERENCE_FRONTEND_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/k-rust/reference-frontend/v1}
mkdir -p "$cache"
export K_OPTS=${REFERENCE_DIFFERENTIAL_K_OPTS:-"-Xmx2048m -Xss32m -XX:+UseSerialGC"}
if [[ -z $jobs ]]; then
  available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
  jobs=$((available_kib / (3 * 1024 * 1024)))
  ((jobs <= 8)) || jobs=8
  ((jobs >= 1)) || jobs=1
fi
export kompile version cache

# verdict DEFINITION: prints `accepted`, or `refused<TAB>first error line`, from the cache or a
# kompile of DEFINITION's main module (the module whose `-SYNTAX` twin the file declares). The
# kore backend writes the frontend's KORE and validates nothing further: the Haskell backend's
# own checks (it refuses a constructor of a variable result sort, which the terms base declares)
# are no frontend's verdict.
verdict() {
  local definition=$1 key main work status
  key=$({ printf '%s\n--backend kore\n' "$version"; cat "$definition"; } | sha256sum | cut -c1-64)
  if [[ -f $cache/$key ]]; then
    cat "$cache/$key"
    return
  fi
  main=
  while read -r module; do
    if grep -qx "module $module-SYNTAX" "$definition"; then
      main=$module
      break
    fi
  done < <(sed -n 's/^module \([^ ]*\)$/\1/p' "$definition")
  [[ -n $main ]] || { printf 'refused\tno main module with a -SYNTAX module\n'; return; }
  work=$(mktemp -d "${TMPDIR:-/tmp}/krs-reference-frontend-XXXXXX")
  status=0
  "$kompile" "$definition" --main-module "$main" --syntax-module "$main-SYNTAX" \
    --backend kore --output-definition "$work/kompiled" >"$work/log" 2>&1 || status=$?
  if ((status == 0)); then
    printf 'accepted\n' >"$work/verdict"
  elif grep -q '^\[Error\]' "$work/log"; then
    printf 'refused\t%s\n' "$(grep -m 1 '^\[Error\]' "$work/log" | tr '\t' ' ')" >"$work/verdict"
  else
    # No verdict of the frontend (the JVM did not start, a signal): not cached.
    printf 'error\tkompile exited %s: %s\n' "$status" "$(tail -n 1 "$work/log" | tr '\t' ' ')"
    rm -rf "$work"
    return
  fi
  mv "$work/verdict" "$cache/$key"
  rm -rf "$work"
  cat "$cache/$key"
}
export -f verdict

# judge KIND ID DEFINITION: one TSV line.
judge() {
  printf '%s\t%s\t%s\n' "$1" "$2" "$(verdict "$3")"
}
export -f judge

# judge_line LINE: `judge case` of a line `ID<TAB>DEFINITION`.
judge_line() {
  judge case "${1%%$'\t'*}" "${1#*$'\t'}"
}
export -f judge_line

started=$SECONDS
out=$dir/reference-frontend.tsv
find "$dir" -mindepth 2 -maxdepth 2 -name definition.k -printf '%h\n' | sort |
  xargs -r -P "$jobs" -I{} bash -c 'judge batch "$(basename "$1")" "$1/definition.k"' _ {} >"$out"
# The cases of each refused batch, alone.
refused_batches=$(awk -F'\t' '$1 == "batch" && $3 == "refused" { print $2 }' "$out")
for batch in $refused_batches; do
  for case in "$dir/$batch"/cases/*/; do
    printf '%s\t%s\n' "$(cat "$case/id")" "$case/definition.k"
  done
done | xargs -r -P "$jobs" -d '\n' -I{} bash -c 'judge_line "$1"' _ {} >>"$out"
batches=$(awk -F'\t' '$1 == "batch"' "$out" | wc -l)
refused=$(awk -F'\t' '$1 == "batch" && $3 == "refused"' "$out" | wc -l)
cases=$(awk -F'\t' '$1 == "case" && $3 == "refused"' "$out" | wc -l)
errors=$(awk -F'\t' '$3 == "error"' "$out" | wc -l)
echo "[reference-frontend] $batches batch definitions, $refused refused; $cases cases refused alone; $errors without a verdict; $((SECONDS - started)) s with $jobs jobs" >&2
((errors == 0)) || exit 2
