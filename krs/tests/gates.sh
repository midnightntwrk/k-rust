#!/usr/bin/env bash
# Runs KRS's gates for the krs-* entries of scripts/gates.toml.
#
# usage: krs/tests/gates.sh light|lint
#        krs/tests/gates.sh imp|kevm|kmir|kwasm [ARG...]
#
# `light` runs every gate except the browser ones (which need a fork build, krs/README.md) and
# the four heavy ones, prints each gate's wall time, and fails when any of them fails. The gates
# share one Cargo target. `lint` runs Clippy and the MSRV check over the standalone test packages
# (tests/package-lint/verify.py), which CI runs and `light` does not. The heavy gates take the
# arguments after their name (`--artifacts-only`, `--java-reference`, `--record`); run them one at
# a time.
# The gates find the Z3 4.12.5 library through KRS_Z3_LIB or the Nix store, and K 7.1.337, which a
# cold reference cache needs, through KRS_K_BIN or PATH (krs/README.md, "Prerequisites").
set -euo pipefail
script=$(realpath "${BASH_SOURCE[0]}")
cd "$(dirname "$script")/.."
export PYTHONDONTWRITEBYTECODE=1

light=(
  repo-hygiene explicit-registration
  tour-minimal tour-imp tour-composition tour-negatives tour-proof-evidence
  cli precedence-associativity imp_static_semantics imp-state imp-control-flow
  builtin-domains configuration-cells grammar-lexing patterns-functions rule-forms sorts-algebra
  verification-surface
)

case ${1:-} in
  light)
    [[ $# -eq 1 ]] || { echo "light takes no arguments" >&2; exit 2; }
    failed=()
    for gate in "${light[@]}"; do
      echo "== $gate"
      start=$SECONDS
      python3 "tests/$gate/verify.py" || failed+=("$gate")
      echo "== $gate: $((SECONDS - start)) s"
    done
    if ((${#failed[@]})); then
      echo "failed: ${failed[*]}" >&2
      exit 1
    fi
    ;;
  lint)
    [[ $# -eq 1 ]] || { echo "lint takes no arguments" >&2; exit 2; }
    exec python3 tests/package-lint/verify.py
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
