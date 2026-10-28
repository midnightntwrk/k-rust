#!/usr/bin/env bash
# KEVM's accounts invariant (demos/k/kevm-inv/kevm-accounts.k, k2lean/docs/invariants.md §5.3): the
# scale test of `k2l_preserve` on KEVM's semantics. A human-run pipeline, not a gate tier: this
# script compiles the module (EVM with the invariant's functions) into $OUT/kore, and kevm.sh's
# steps do the rest on that work directory, with TARGET=evm and the invariant passed to `gen`:
#
#   k2lean/pipelines/kevm-inv.sh compile          krust kcompile of kevm-accounts.k into $OUT/kore
#   k2lean/pipelines/kevm-inv.sh gen|equations|open|build [T...]
#                                                 kevm.sh's step of that name, with TARGET=evm,
#                                                 OUT=$OUT and GEN_ARGS="--invariant acctsOk@ethereum"
#
# A first run is compile, gen, equations, open (the Equations proofs that failed become open
# obligations), gen, equations, then build KEvm.InvariantDefs KEvm.Invariants. Each step is heavy
# (minutes, several GB); run it under a memory cap. Environment: KRUST, K2LEAN, KEVM_SOURCES,
# K_BUILTIN as for kevm.sh; OUT (default target/k2lean-kevm-inv).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
KRUST=${KRUST:-$root/target/release/krust}
KEVM_SOURCES=${KEVM_SOURCES:-${EVM_SEMANTICS_CHECKOUT:-$root/evm-semantics}/kevm-pyk/src/kevm_pyk/kproj}
K_BUILTIN=${K_BUILTIN:-$root/k/result/include/kframework/builtin}
OUT=${OUT:-$root/target/k2lean-kevm-inv}
step=${1:-}
[ -n "$step" ] && shift
case $step in
  compile)
    [ -x "$KRUST" ] || { echo "kevm-inv.sh: needs krust at $KRUST" >&2; exit 2; }
    [ -f "$KEVM_SOURCES/evm-semantics/evm.md" ] || { echo "kevm-inv.sh: no KEVM sources at $KEVM_SOURCES (set KEVM_SOURCES)" >&2; exit 2; }
    mkdir -p "$OUT/logs"
    "$root/k2lean/tests/rtime.py" "$KRUST" kcompile "$root/k2lean/demos/k/kevm-inv/kevm-accounts.k" \
      --main-module KEVM-ACCOUNTS --syntax-module KEVM-ACCOUNTS --output-directory "$OUT/kore" \
      --builtin-directory "$K_BUILTIN" -I "$KEVM_SOURCES/evm-semantics" -I "$KEVM_SOURCES/plugin" \
      > "$OUT/logs/compile.log" 2>&1
    tail -n 1 "$OUT/logs/compile.log"
    ;;
  gen|equations|open|build)
    TARGET=evm OUT=$OUT GEN_ARGS="--invariant acctsOk@ethereum ${GEN_ARGS:-}" exec "$here/kevm.sh" "$step" "$@"
    ;;
  *)
    sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//'
    exit 2
    ;;
esac
