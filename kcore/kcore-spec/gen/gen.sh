#!/usr/bin/env bash
# `kcore gen KORE OUTDIR NAME [--tie] [OPTION]...` (KcoreGen.lean) under a 12 GiB memory scope: the native executable
# when built (`lake build kcore`), otherwise interpreted (`lean --run`). Run from kcore-spec after
# `lake build`; OUTDIR relative to kcore-spec.
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
cap() { systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1800 "$@"; }
if [ -x .lake/build/bin/kcore ] && [ .lake/build/bin/kcore -nt KcoreGen.lean ]; then
  cap .lake/build/bin/kcore gen "$@"
else
  LEAN_PATH=$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 cap "$TC/bin/lean" -j1 --run KcoreGen.lean gen "$@"
fi
