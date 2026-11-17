#!/usr/bin/env bash
# Why each KORE text is or is not in KCore, and its parameter symbols (test/Member.lean, compiled
# diagnostics), with the check of the frozen table `regHookNames` against the builtin texts. One
# process under a 12 GiB memory scope, one thread. Usage: test/member.sh [KORE...]
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
LEAN_PATH=$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  timeout 1200 "$TC/bin/lean" -j1 --run test/Member.lean ${@:-f2-examples/ph.kore f2-examples/prio.kore \
  f2-examples/imp.kore f2-examples/kimp.kore f2-examples/imp-sec.kore examples/peano/Peano/definition.kore}
