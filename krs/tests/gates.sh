#!/usr/bin/env bash
# Runs KRS's gates for the krs-* entries of scripts/gates.toml.
#
# usage: krs/tests/gates.sh light|lint|tour-pages|ports-rust
#        krs/tests/gates.sh imp|kevm|kmir|kwasm|ports-emit [ARG...]
#
# `light` runs every gate except the browser ones (which need a fork build, krs/README.md) and
# the four heavy ones, as many at a time as the available memory has room for at 3 GiB each
# (KRS_LIGHT_JOBS overrides), prints each gate's output and wall time as it finishes, and fails when
# any of them fails. The gates share one Cargo target, whose lock
# serializes their builds; afterwards `light` removes the collectors of the gates' temporary
# packages from it (support/krs.py, prune_dead_collectors). `lint` runs Clippy and the MSRV check
# over the standalone test packages (tests/package-lint/verify.py), which CI runs and `light` does
# not. `tour-pages` runs tour-proof-evidence alone, the one gate that reads site pages.
# `ports-emit` runs the four ports' emission against the heavy gates' pins (tests/ports-emit/verify.py;
# `--record` rewrites only its own macro-output pins). The heavy gates take the arguments after their
# name (`--artifacts-only`, `--java-reference`, `--record`); before starting several, check that the
# available memory has room for them. `ports-rust` runs the four with `--artifacts-only`, as many at a
# time as the available memory has room for at 8 GiB each (KRS_PORTS_JOBS overrides), and fails when
# any of them fails.
# A job count follows memory, not CPU load: load fluctuates far more, and an oversubscribed CPU only
# slows a run, while exhausted memory fails it. It is at least 1 and at most the CPU count.
# The gates find the Z3 4.12.5 library through KRS_Z3_LIB or the Nix store, and K 7.1.337, which a
# cold reference cache needs, through KRS_K_BIN or PATH (krs/README.md, "Prerequisites").
set -euo pipefail
script=$(realpath "${BASH_SOURCE[0]}")
cd "$(dirname "$script")/.."
export PYTHONDONTWRITEBYTECODE=1

# Longest first, so the last gates to start are short ones.
light=(
  verification-surface grammar-lexing builtin-domains configuration-cells rule-forms
  patterns-functions sorts-algebra cli explicit-registration tour-proof-evidence
  tour-composition tour-negatives repo-hygiene tour-minimal tour-imp precedence-associativity
  imp_static_semantics imp-state imp-control-flow
)

# The job count of a pool: the value of the variable named $1 when set, else the available memory
# over $2 GiB, at least 1 and at most the CPU count (or the cgroup's quota).
job_count() {
  local override=${!1:-} available_kib count limit quota period
  if [[ -n $override ]]; then
    [[ $override =~ ^[1-9][0-9]?$ ]] || { echo "$1 must be from 1 to 99" >&2; exit 2; }
    echo "$override"
    return
  fi
  available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
  count=$((available_kib / ($2 * 1024 * 1024)))
  if read -r quota period 2>/dev/null </sys/fs/cgroup/cpu.max && [[ $quota != max ]]; then
    limit=$(((quota + period - 1) / period))
  else
    limit=$(nproc)
  fi
  ((count <= limit)) || count=$limit
  ((count >= 1)) || count=1
  echo "$count"
}

# Run `tests/GATE/verify.py ARG` for each GATE, LIMIT at a time; print each gate's output and wall
# time as it finishes, and collect the failed gates in `failed`.
failed=()
run_pool() {
  local limit=$1 argument=$2
  shift 2
  echo "$limit at a time ($(($(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo) / 1024 / 1024)) GiB available)"
  logs=$(mktemp -d "${TMPDIR:-/tmp}/krs-gates.XXXXXX")
  declare -gA running=()
  trap 'rm -rf "$logs"' EXIT
  trap 'stop; exit 130' INT TERM
  local gate
  for gate in "$@"; do
    ((${#running[@]} < limit)) || reap
    (
      start=$SECONDS
      status=0
      python3 "tests/$gate/verify.py" ${argument:+"$argument"} >"$logs/$gate.log" 2>&1 </dev/null || status=$?
      echo $((SECONDS - start)) >"$logs/$gate.time"
      exit "$status"
    ) &
    running[$!]=$gate
  done
  while ((${#running[@]})); do
    reap
  done
}
stop() {
  local pid
  for pid in "${!running[@]}"; do
    pkill -TERM -P "$pid" 2>/dev/null || true
  done
  wait
}
reap() {
  local pid status=0
  wait -n -p pid "${!running[@]}" || status=$?
  local gate=${running[$pid]}
  unset "running[$pid]"
  echo "== $gate"
  cat "$logs/$gate.log"
  echo "== $gate: $(<"$logs/$gate.time") s$( ((status)) && echo ", FAILED")"
  ((status == 0)) || failed+=("$gate")
}
report_failed() {
  if ((${#failed[@]})); then
    echo "failed: ${failed[*]}" >&2
    exit 1
  fi
}

case ${1:-} in
  light)
    [[ $# -eq 1 ]] || { echo "light takes no arguments" >&2; exit 2; }
    limit=$(job_count KRS_LIGHT_JOBS 3) || exit 2
    run_pool "$limit" "" "${light[@]}"
    # The gates' temporary packages are gone now; their collectors in the shared target are garbage.
    python3 -c 'import sys; sys.path.insert(0, "tests")
from support.krs import prune_dead_collectors
from support.tools import tool_target
print(f"pruned {prune_dead_collectors(tool_target())} dead collectors")'
    report_failed
    ;;
  lint)
    [[ $# -eq 1 ]] || { echo "lint takes no arguments" >&2; exit 2; }
    exec python3 tests/package-lint/verify.py
    ;;
  tour-pages)
    [[ $# -eq 1 ]] || { echo "tour-pages takes no arguments" >&2; exit 2; }
    exec python3 tests/tour-proof-evidence/verify.py
    ;;
  ports-emit)
    shift
    exec python3 tests/ports-emit/verify.py "$@"
    ;;
  ports-rust)
    [[ $# -eq 1 ]] || { echo "ports-rust takes no arguments" >&2; exit 2; }
    limit=$(job_count KRS_PORTS_JOBS 8) || exit 2
    run_pool "$limit" --artifacts-only imp kevm kmir kwasm
    report_failed
    ;;
  imp | kevm | kmir | kwasm)
    gate=$1
    shift
    exec python3 "tests/$gate/verify.py" "$@"
    ;;
  *)
    sed -n '4,5s/^# //p' "$script" >&2
    exit 2
    ;;
esac
