#!/usr/bin/env bash
# The reference frontend over the K text the class matrix emits (NT-42): Java K's kompile reads
# each batch definition that scripts/krs-class.sh wrote under KRS_CLASS_K_OUT=DIR, and, where it
# refuses one, the definition of each case of that batch alone, so that a refusal names its
# cases. No other check of the class matrix reads the emitted K with an independent frontend
# (K2 judges the class, K3 the `krs expand` closure, K6 the native compile).
#
# A refusal is evidence about the K text, to reason about from what the sentence means, never a
# rule to copy. The known ones are pinned in krs/tests/class-matrix/reference-frontend.toml, each
# naming the finding (krs/tests/class-matrix/findings.toml) that owns it, so a new refusal is
# read by someone: the run fails on a case refused alone that no pin lists, on a refused batch
# that no case refused alone accounts for, on a pinned case that is now accepted, on a pin whose
# refusal is another message, and on a pin naming no registered finding. A pinned case the dump
# does not hold (a filtered run) is reported as not judged.
#
# Only the frontend's own verdicts are cached: `accepted` (kompile exits 0) and `refused` (an
# `[Error]` line of the frontend's, not `[Error] Internal:`, an uncaught exception or a JVM that
# ran out of memory, did not start or was killed). Anything else is an `error`, never cached,
# and fails the run. A verdict is cached by everything it depends on: kompile's path and full
# version output, its arguments, K_OPTS and the definition's bytes, under
# KRS_REFERENCE_FRONTEND_CACHE (default ${XDG_CACHE_HOME:-~/.cache}/k-rust/reference-frontend/v2).
# Every kompile runs under the reference memory guard with a bounded JVM.
#
# The class matrix records each batch or case whose emission failed under DIR/dropped/; their
# cases have no K text and so no verdict, and the run fails while any exists.
#
# usage: scripts/krs-class-reference-frontend.sh [--jobs N] DIR
#   --jobs N   concurrent kompiles (default: the memory headroom, the smaller of MemAvailable
#              and the guard's scope limit, over one kompile's estimate: K_OPTS's -Xmx plus
#              KRS_REFERENCE_FRONTEND_JVM_OVERHEAD_KIB, default 1 GiB, of the JVM's own memory)
# Environment: KRS_REFERENCE_FRONTEND_PINS (default krs/tests/class-matrix/reference-frontend.toml)
# and KRS_REFERENCE_FRONTEND_FINDINGS (default krs/tests/class-matrix/findings.toml).
# Writes DIR/reference-frontend.tsv, one line per definition kompiled:
#   batch|case <TAB> ID (the batch's hash, or the case's ID) <TAB> accepted|refused|error <TAB> message
# and prints the counts, the pin check and the time taken.
# Exit status: 0 when every definition was judged and the verdicts match the pins; 1 on a pin
# mismatch; 2 on a usage or tool error, a definition without a verdict, or a dropped emission.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/.." && pwd)
jobs=
while (($#)); do
  case $1 in
    --jobs)
      [[ ${2:-} =~ ^[1-9][0-9]*$ ]] || { echo "error: --jobs takes a positive number" >&2; exit 2; }
      jobs=$2
      shift 2
      ;;
    -h | --help)
      sed -n '2,37p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) break ;;
  esac
done
[[ $# -eq 1 && -d $1 ]] || { echo "usage: $0 [--jobs N] DIR" >&2; exit 2; }
dir=$(cd "$1" && pwd)
pins=${KRS_REFERENCE_FRONTEND_PINS:-$root/krs/tests/class-matrix/reference-frontend.toml}
findings=${KRS_REFERENCE_FRONTEND_FINDINGS:-$root/krs/tests/class-matrix/findings.toml}
[[ -f $pins ]] || { echo "error: no pin list at $pins" >&2; exit 2; }
[[ -f $findings ]] || { echo "error: no findings registry at $findings" >&2; exit 2; }

# shellcheck source=scripts/reference-memory-guard.sh
source "$here/reference-memory-guard.sh"
reference_enter_whole_job "$@" || exit 2

kompile=${K_KOMPILE:-$(command -v kompile || true)}
[[ -n $kompile && -x $kompile ]] || { echo "error: no kompile: set K_KOMPILE" >&2; exit 2; }
kompile=$(readlink -f "$kompile")
version=$("$kompile" --version 2>/dev/null || true)
[[ -n $version ]] || { echo "error: $kompile --version printed nothing" >&2; exit 2; }
cache=${KRS_REFERENCE_FRONTEND_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/k-rust/reference-frontend/v2}
mkdir -p "$cache"
export K_OPTS=${REFERENCE_DIFFERENTIAL_K_OPTS:-"-Xmx2048m -Xss32m -XX:+UseSerialGC"}

# The memory one kompile may take: its heap bound (the last -Xmx of K_OPTS; the JVM's default is
# a quarter of the host, which no headroom can plan for) plus the JVM's memory beside the heap
# (metaspace, code cache, thread stacks, the GC's own), which the overhead states.
heap_kib() {
  local option value heap=
  for option in $K_OPTS; do
    [[ $option == -Xmx* ]] || continue
    value=${option#-Xmx}
    case $value in
      *[kK]) heap=${value%?} ;;
      *[mM]) heap=$((${value%?} * 1024)) ;;
      *[gG]) heap=$((${value%?} * 1024 * 1024)) ;;
      *[0-9]) heap=$((value / 1024)) ;;
      *) heap= ;;
    esac
  done
  [[ $heap =~ ^[0-9]+$ ]] && ((heap > 0)) || return 1
  printf '%s\n' "$heap"
}
# The memory the guard leaves the whole job: under a systemd scope, the scope's memory.high (or
# memory.max where high is unbounded), read from this process's own cgroup; under the RLIMIT_AS
# fallback, which bounds each process's address space and not the job's resident memory, none.
scope_kib() {
  local group limit file
  [[ ${reference_job_guard_kind:-} == systemd-scope ]] || return 1
  group=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
  for file in memory.high memory.max; do
    limit=$(cat "/sys/fs/cgroup$group/$file" 2>/dev/null || true)
    if [[ $limit =~ ^[0-9]+$ ]]; then
      printf '%s\n' $((limit / 1024))
      return 0
    fi
  done
  printf '%s\n' "$reference_job_memory_max_kib"
}
if [[ -z $jobs ]]; then
  heap=$(heap_kib) || { echo "error: K_OPTS ($K_OPTS) sets no -Xmx, so one kompile's memory is unbounded; set REFERENCE_DIFFERENTIAL_K_OPTS" >&2; exit 2; }
  overhead=${KRS_REFERENCE_FRONTEND_JVM_OVERHEAD_KIB:-1048576}
  [[ $overhead =~ ^[0-9]+$ ]] || { echo "error: KRS_REFERENCE_FRONTEND_JVM_OVERHEAD_KIB must be a number of KiB" >&2; exit 2; }
  per_kompile=$((heap + overhead))
  budget=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
  budget_source="MemAvailable $((budget / 1024)) MiB"
  if limit=$(scope_kib) && ((limit < budget)); then
    budget=$limit
    budget_source="the guard's scope limit $((limit / 1024)) MiB"
  fi
  jobs=$((budget / per_kompile))
  ((jobs >= 1)) || jobs=1
  echo "[reference-frontend] $jobs jobs: $budget_source over $((per_kompile / 1024)) MiB per kompile (-Xmx $((heap / 1024)) MiB + $((overhead / 1024)) MiB JVM overhead; guard ${reference_job_guard_kind:-none})" >&2
else
  echo "[reference-frontend] $jobs jobs (--jobs)" >&2
fi
export kompile version cache

# verdict DEFINITION: prints `accepted`, `refused<TAB>first error line`, or
# `error<TAB>why there is no verdict`, from the cache or a kompile of DEFINITION's main module
# (the module whose `-SYNTAX` twin the file declares). The kore backend writes the frontend's KORE
# and validates nothing further: the Haskell backend's own checks (it refuses a constructor of a
# variable result sort, which the terms base declares) are no frontend's verdict.
verdict() {
  local definition=$1 key main work status first
  local -a arguments
  main=
  while read -r module; do
    if grep -qx "module $module-SYNTAX" "$definition"; then
      main=$module
      break
    fi
  done < <(sed -n 's/^module \([^ ]*\)$/\1/p' "$definition")
  # The file's own shape, not the frontend's verdict: no kompile reads it, nothing is cached.
  [[ -n $main ]] || { printf 'error\tno main module with a -SYNTAX module\n'; return; }
  arguments=(--main-module "$main" --syntax-module "$main-SYNTAX" --backend kore)
  key=$({
    printf 'kompile %s\n%s\n' "$kompile" "$version"
    printf 'argument %s\n' "${arguments[@]}"
    printf 'K_OPTS %s\n' "$K_OPTS"
    cat "$definition"
  } | sha256sum | cut -c1-64)
  if [[ -f $cache/$key ]]; then
    cat "$cache/$key"
    return
  fi
  work=$(mktemp -d "${TMPDIR:-/tmp}/krs-reference-frontend-XXXXXX")
  status=0
  "$kompile" "$definition" "${arguments[@]}" --output-definition "$work/kompiled" \
    >"$work/log" 2>&1 || status=$?
  first=$(grep -m 1 '^\[Error\]' "$work/log" | tr '\t' ' ' || true)
  if ((status == 0)); then
    printf 'accepted\n' >"$work/verdict"
  elif [[ -n $first && $first != '[Error] Internal:'* ]] && ((status < 128)) &&
    ! grep -qE 'OutOfMemoryError|StackOverflowError|Uncaught exception|Could not reserve enough space|unable to create native thread|Error occurred during initialization of VM' "$work/log"; then
    printf 'refused\t%s\n' "$first" >"$work/verdict"
  else
    # No verdict of the frontend (an internal or resource failure, a JVM that did not start, a
    # signal): not cached, and the run fails.
    printf 'error\tkompile exited %s: %s\n' "$status" \
      "${first:-$(tail -n 1 "$work/log" | tr '\t' ' ')}"
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
    [[ -f $case/id ]] || continue
    printf '%s\t%s\n' "$(cat "$case/id")" "$case/definition.k"
  done
done | xargs -r -P "$jobs" -d '\n' -I{} bash -c 'judge_line "$1"' _ {} >>"$out"
batches=$(awk -F'\t' '$1 == "batch"' "$out" | wc -l)
refused=$(awk -F'\t' '$1 == "batch" && $3 == "refused"' "$out" | wc -l)
cases=$(awk -F'\t' '$1 == "case" && $3 == "refused"' "$out" | wc -l)
errors=$(awk -F'\t' '$3 == "error"' "$out" | wc -l)
dropped=0
if [[ -d $dir/dropped ]]; then
  dropped=$(find "$dir/dropped" -maxdepth 1 -name '*.txt' | wc -l)
fi
echo "[reference-frontend] $batches batch definitions, $refused refused; $cases cases refused alone; $errors without a verdict; $dropped emissions dropped; $((SECONDS - started)) s with $jobs jobs" >&2
status=0
if ((errors > 0)); then
  echo "error: no verdict of the frontend for:" >&2
  awk -F'\t' '$3 == "error" { printf "  %s %s: %s\n", $1, $2, $4 }' "$out" >&2
  status=2
fi
if ((dropped > 0)); then
  echo "error: emissions the class matrix dropped, whose cases have no K text and so no verdict:" >&2
  for record in "$dir"/dropped/*.txt; do
    sed -n '1s/^/  /p; 2,$s/^/    /p' "$record" >&2
  done
  status=2
fi

# The pin check: the verdicts against the known refusals. Exit 10 on a mismatch; any other
# nonzero status is the check's own failure.
pin_status=0
python3 -I - "$dir" "$out" "$pins" "$findings" <<'PY' || pin_status=$?
import os
import sys
import tomllib

directory, tsv, pins_path, findings_path = sys.argv[1:]
with open(pins_path, "rb") as file:
    pins = tomllib.load(file)
with open(findings_path, "rb") as file:
    findings = tomllib.load(file)

batch_verdicts = {}
case_verdicts = {}
with open(tsv, encoding="utf-8") as file:
    for line in file:
        kind, identity, verdict, *message = line.rstrip("\n").split("\t")
        target = batch_verdicts if kind == "batch" else case_verdicts
        target[identity] = (verdict, message[0] if message else "")

# The cases each batch holds, from the dump.
members = {}
for batch in batch_verdicts:
    cases = os.path.join(directory, batch, "cases")
    held = []
    if os.path.isdir(cases):
        for case in sorted(os.listdir(cases)):
            path = os.path.join(cases, case, "id")
            if os.path.isfile(path):
                with open(path, encoding="utf-8") as file:
                    held.append(file.read())
    members[batch] = held

failures = []
for case, pin in pins.items():
    if (
        not isinstance(pin, dict)
        or set(pin) != {"finding", "refusal"}
        or not all(isinstance(pin[key], str) for key in pin)
    ):
        failures.append(f"pin {case!r}: needs exactly `finding` and `refusal`, both strings")
    elif pin["finding"] not in findings:
        failures.append(f"pin {case!r}: finding {pin['finding']} is not registered in findings.toml")
for case, (verdict, message) in sorted(case_verdicts.items()):
    if verdict != "refused":
        continue
    pin = pins.get(case)
    if pin is None:
        failures.append(f"{case}: refused, and no pin lists it: {message}")
    elif isinstance(pin, dict) and isinstance(pin.get("refusal"), str) and pin["refusal"] not in message:
        failures.append(
            f"{case}: refused with another message than its pin's ({pin['refusal']!r}): {message}"
        )
for batch, (verdict, message) in sorted(batch_verdicts.items()):
    if verdict == "refused" and not any(
        case_verdicts.get(case, ("",))[0] == "refused" for case in members[batch]
    ):
        failures.append(f"batch {batch}: refused, and no case of it is refused alone: {message}")
not_judged = []
for case in sorted(pins):
    accepted_alone = case_verdicts.get(case, ("",))[0] == "accepted"
    in_accepted = any(
        case in members[batch] and verdict == "accepted"
        for batch, (verdict, _) in batch_verdicts.items()
    )
    if accepted_alone or in_accepted:
        where = "alone" if accepted_alone else "in its batch"
        finding = pins[case].get("finding") if isinstance(pins[case], dict) else None
        failures.append(f"{case}: pinned as refused ({finding}), now accepted {where}")
    elif case not in case_verdicts:
        not_judged.append(case)

for case in not_judged:
    print(f"[reference-frontend] pin not judged (the dump does not hold it): {case}", file=sys.stderr)
met = sum(1 for case, (verdict, _) in case_verdicts.items() if verdict == "refused" and case in pins)
print(
    f"[reference-frontend] pins: {len(pins)} listed, {met} met, {len(not_judged)} not judged, "
    f"{len(failures)} mismatches",
    file=sys.stderr,
)
for failure in failures:
    print(f"error: {failure}", file=sys.stderr)
sys.exit(10 if failures else 0)
PY
case $pin_status in
  0 | 10) ;;
  *)
    echo "error: the pin check could not run (status $pin_status)" >&2
    exit 2
    ;;
esac
((status == 0)) || exit "$status"
((pin_status == 0)) || exit 1
exit 0
