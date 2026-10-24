#!/usr/bin/env bash
# Runs KRS's gates for the krs-* entries of scripts/gates.toml.
#
# usage: krs/tests/gates.sh light|lint|tour-pages
#        krs/tests/gates.sh imp|kevm|kmir|kwasm [ARG...]
#
# `light` runs every gate except the browser ones (which need a fork build, krs/README.md) and
# the four heavy ones, KRS_LIGHT_JOBS (default 4) at a time, prints each gate's output and wall time
# as it finishes, and fails when any of them fails. The gates share one Cargo target, whose lock
# serializes their builds; afterwards `light` removes the collectors of the gates' temporary
# packages from it (support/krs.py, prune_dead_collectors). `lint` runs Clippy and the MSRV check
# over the standalone test packages (tests/package-lint/verify.py), which CI runs and `light` does
# not. `tour-pages` runs tour-proof-evidence alone, the one gate that reads site pages. The heavy
# gates take the arguments after their name (`--artifacts-only`, `--java-reference`, `--record`);
# run them one at a time.
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

case ${1:-} in
  light)
    [[ $# -eq 1 ]] || { echo "light takes no arguments" >&2; exit 2; }
    limit=${KRS_LIGHT_JOBS:-4}
    [[ $limit =~ ^[1-9][0-9]?$ ]] || { echo "KRS_LIGHT_JOBS must be from 1 to 99" >&2; exit 2; }
    logs=$(mktemp -d "${TMPDIR:-/tmp}/krs-light.XXXXXX")
    declare -A running=()
    stop() {
      local pid
      for pid in "${!running[@]}"; do
        pkill -TERM -P "$pid" 2>/dev/null || true
      done
      wait
    }
    trap 'rm -rf "$logs"' EXIT
    trap 'stop; exit 130' INT TERM
    failed=()
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
    for gate in "${light[@]}"; do
      ((${#running[@]} < limit)) || reap
      (
        start=$SECONDS
        status=0
        python3 "tests/$gate/verify.py" >"$logs/$gate.log" 2>&1 </dev/null || status=$?
        echo $((SECONDS - start)) >"$logs/$gate.time"
        exit "$status"
      ) &
      running[$!]=$gate
    done
    while ((${#running[@]})); do
      reap
    done
    # The gates' temporary packages are gone now; their collectors in the shared target are garbage.
    python3 -c 'import sys; sys.path.insert(0, "tests")
from support.krs import prune_dead_collectors
from support.tools import tool_target
print(f"pruned {prune_dead_collectors(tool_target())} dead collectors")'
    if ((${#failed[@]})); then
      echo "failed: ${failed[*]}" >&2
      exit 1
    fi
    ;;
  lint)
    [[ $# -eq 1 ]] || { echo "lint takes no arguments" >&2; exit 2; }
    exec python3 tests/package-lint/verify.py
    ;;
  tour-pages)
    [[ $# -eq 1 ]] || { echo "tour-pages takes no arguments" >&2; exit 2; }
    exec python3 tests/tour-proof-evidence/verify.py
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
