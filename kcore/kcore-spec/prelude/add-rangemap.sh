#!/usr/bin/env bash
# RANGEMAP's library data from K's own text: kompile 7.1.337 (default options, --backend haskell)
# of prelude/rangemap-probe.k, a definition that imports DOMAINS, FLOAT and RANGEMAP, into
# .lake/rangemap-probe/ (not committed); then `extract_builtin.py --add RANGEMAP` on its
# definition.kore, which adds the module's row to KcoreSpec/BuiltinData.lean and its text to
# prelude/builtin.kore and builtin-arg.kore. Usage: prelude/add-rangemap.sh (from anywhere).
# K_KOMPILE names kompile (default: the main k-rust checkout's k/result/bin/kompile; K_RUST names
# that checkout, whose crates/k-rust/builtin the extractor also reads).
set -eu
K=$(cd "$(dirname "$0")/.." && pwd)
KR=${K_RUST:-$HOME/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust}
KOMPILE=${K_KOMPILE:-$KR/k/result/bin/kompile}
O=$K/.lake/rangemap-probe
rm -rf "$O"; mkdir -p "$O"
cp "$K/prelude/rangemap-probe.k" "$O/rmp.k"
echo "add-rangemap: $(free -g | awk '/^Mem:/ {print $7}') GiB available"
cd "$O"
LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1800 \
  "$KOMPILE" --backend haskell rmp.k -o rmp-kompiled > kompile.log 2>&1 \
  || { echo "add-rangemap: kompile failed"; cat kompile.log; exit 1; }
sha256sum rmp-kompiled/definition.kore
cd "$K"
K_RUST=$KR python3 -I prelude/extract_builtin.py --add RANGEMAP "$O/rmp-kompiled/definition.kore"
