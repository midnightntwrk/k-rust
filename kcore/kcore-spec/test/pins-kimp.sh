#!/usr/bin/env bash
# The pin of row imp's statements (test/PinsKimp.lean): kimp's text as kompile wrote it
# (examples/ref-kimp/RefKimp/definition.kore) generated with `kcore gen --wf` under the namespace
# RefKimp into .lake/pins/kimp (ignored), built (gen/build.sh: one module a process, one thread,
# 12 GiB memory scope) with the consumer's statement (examples/ref-kimp/User/SumSpecStmt.lean, copied
# in as the module User.SumSpecStmt), then the pin file checked against it: `consistent`, `sound_at`,
# `complete_at` and `run_exact` by their types, the consumer's statement by its body. Exit 1 when
# the generated package states another text for one of them, or does not build.
# Usage: test/pins-kimp.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
P=.lake/pins/kimp
rm -rf "$P"; mkdir -p .lake/pins
gen/gen.sh examples/ref-kimp/RefKimp/definition.kore "$P" RefKimp --wf > .lake/pins/kimp-gen.log 2>&1 \
  || { cat .lake/pins/kimp-gen.log; exit 1; }
mkdir -p "$P/User" && cp examples/ref-kimp/User/SumSpecStmt.lean "$P/User/" || exit 1
gen/build.sh "$P" User.SumSpecStmt || exit 1
LEAN_PATH=$P/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) LEAN_NUM_THREADS=1 \
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1200 \
  "$TC/bin/lean" -j1 test/PinsKimp.lean || exit 1
echo "pins on kimp: ok"
