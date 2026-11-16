#!/usr/bin/env bash
# KEVM's `--core` package (or any large definition's): `kcore gen --core` into a directory outside
# the tree (default kcore-spec/.lake/kevm/NAME, which is ignored; KEVM_OUT overrides the parent),
# each module built in its own process, one thread, under a 12 GiB memory scope (gen/build.sh),
# then per-module wall time and peak memory, their totals, and the axioms of `coreOK_defn`,
# `sound_hyp`, `complete_hyp`, and of `fnHyp_defn`, `sound_defn`, `complete_defn` (what the deciders
# leave of `FnHyp`, `NS.FnHyp`). The package holds its input (`NAME/definition.kore`, 8 to 9 MB for
# KEVM), so it is not committed; run at a wave's end, not by examples/run.sh.
# Usage: examples/kevm.sh PATH-TO-definition.kore [NAME]   (from anywhere; kcore-spec built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd)
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
[ $# -ge 1 ] && [ -f "$1" ] || { echo "usage: examples/kevm.sh PATH-TO-definition.kore [NAME]"; exit 2; }
kore=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
ns=${2:-Kevm}
out=${KEVM_OUT:-$K/.lake/kevm}/$ns
mkdir -p "$out"
cd "$K"
t0=$(date +%s)
gen/gen.sh "$kore" "$out" "$ns" --core > "$out/gen.log" 2>&1
rc=$?
grep -v '^{"lazy' "$out/gen.log" | tail -40
[ $rc -eq 0 ] || { echo "kevm.sh: kcore gen --core failed (exit $rc), $out/gen.log"; exit 1; }
echo "generated in $(( $(date +%s) - t0 )) s: $(wc -l < "$out/modules.txt") modules"
gen/build.sh "$out" | tee "$out/build.log"
[ "$(tail -1 "$out/build.log")" = built ] || { echo "kevm.sh: a module failed, $out/build.log"; exit 1; }
awk '/: wall/ { gsub(/,/, ""); n++; t += $3; for (i = 1; i <= NF; i++) if ($i == "rss" && $(i+1) > p) p = $(i+1) }
  END { printf "total: %d modules, %.1f s wall, peak %.1f GiB\n", n, t, p / 1024 }' "$out/build.log"
printf 'import %s\n#print axioms %s.coreOK_defn\n#print axioms %s.sound_hyp\n#print axioms %s.complete_hyp\n#print axioms %s.fnHyp_defn\n#print axioms %s.sound_defn\n#print axioms %s.complete_defn\n' \
  "$ns" "$ns" "$ns" "$ns" "$ns" "$ns" "$ns" > "$out/Axioms.lean"
LP=$(lake env printenv LEAN_PATH)
LEAN_PATH=$out/.lake/build/lib/lean:$LP LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G \
  -p MemorySwapMax=0 timeout 900 "$TC/bin/lean" -j1 "$out/Axioms.lean"
