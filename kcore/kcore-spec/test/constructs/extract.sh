#!/usr/bin/env bash
# The eight key lists E1 to E8 of DONE-0 C1, extracted from K 7.1.337 (test/constructs/extract.py
# says each list's unit), with the second-method recounts, into .lake/constructs/ (E1.keys ..
# E8.keys, recount.txt). Needs E6's kompiled text (test/constructs/kompile-e6.sh). Exit 1 when a
# recount disagrees. Also writes uses-kimp.E4 and uses-kimp.E6: the E4 and E6 keys kimp's kompiled
# text (f2-examples/ref-kimp.kore) meets; and uses-kore.E4 and uses-kore.E6 for kk/kk.k's kompiled
# text when fixture kore-k has been kompiled. K_RUST names the k-rust checkout holding the reference links `k` (K's source
# checkout, whose `k/result` is the installation) and `haskell-backend` (kore-syntax.md).
set -eu
K=$(cd "$(dirname "$0")/../.." && pwd)
KR=${K_RUST:-$HOME/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust}
O=$K/.lake/constructs; mkdir -p "$O"
KOMPILE=$KR/k/result/bin/kompile
cap() { LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout "$@"; }
{ cap 300 "$KOMPILE" --help; cap 300 "$KOMPILE" --help-hidden; } > "$O/kompile-help.txt" 2>&1
TEXTS="kimp=$K/f2-examples/ref-kimp.kore"
KK=$K/.lake/kfix/kore-k/src/out/definition.kore  # kk/kk.k kompiled by test/constructs/kfix.py run kore-k
[ -f "$KK" ] && TEXTS="$TEXTS kore=$KK"
KCORE_ROW_TEXTS="$TEXTS" KOMPILE_HELP=$O/kompile-help.txt python3 -I "$K/test/constructs/extract.py" "$KR/k" "$(readlink -f "$KR/k/result")" \
  "$KR/haskell-backend/docs/kore-syntax.md" "$K/.lake/constructs-e6/all-builtins-kompiled/definition.kore" "$O"
