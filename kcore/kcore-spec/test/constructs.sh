#!/usr/bin/env bash
# DONE-0 C1's check: the eight key lists that test/constructs/extract.sh writes from K 7.1.337 (with
# their second-method recounts) against test/constructs/rows.toml, list by list; every row's status
# one of supported, parameter, inert, erased, refused, pending-fixture, not-handled; E4's syntax-tree keys exactly
# the strings of test/ConstructsE4.lean, whose functions match every constructor with no wildcard
# (elaborated here). Prints the eight counts, the rows per status and the not-handled rows per list. Then
# test/constructs/kfix.py check: every row of E1, E2, E3, E7, E8 points at a fixture of
# test/constructs/fixtures/ whose committed kore.txt holds the sentences the row names. Exit 1 on any
# difference. Then test/constructs/units.py: every refused row and every class R-c row names in `unit`
# a ticket or unit of progress/ (KCORE_PROGRESS), or "none (CLASS)" (rows-header.toml). Then
# test/constructs/modifiers.py check: the pair table [C3] (DONE-0 C3). Then
# test/constructs/provisional.py: no entry of ../core-manifest.toml is provisional, and each entry
# relabelled stable names the rows.toml entries it leaves refused or parameter, or the sentence "no
# construct depends on it" (DONE-0 C5 part 4). Then test/provenance.sh: the
# evidence theorems the rows name (`derived`, DONE-0 C7 check 1). Needs E6's kompiled text
# (test/constructs/kompile-e6.sh; exit 77 without it).
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
[ -f .lake/constructs-e6/all-builtins-kompiled/definition.kore ] || { echo "constructs: no E6 text (test/constructs/kompile-e6.sh)"; exit 77; }
test/constructs/extract.sh > .lake/constructs/extract.out 2>&1; rc=$?
cat .lake/constructs/recount.txt
[ $rc -eq 0 ] || { echo "constructs: extraction or a recount failed"; tail -5 .lake/constructs/extract.out; exit 1; }
LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 600 \
  lake env lean -j1 test/ConstructsE4.lean || { echo "constructs: test/ConstructsE4.lean does not elaborate"; exit 1; }
python3 -I - .lake/constructs test/constructs/rows.toml test/ConstructsE4.lean <<'PY'
import re, sys, tomllib
kd, rows, lean = sys.argv[1:4]
t = tomllib.load(open(rows, "rb"))
ST = {"supported", "parameter", "inert", "erased", "refused", "pending-fixture", "not-handled"}
bad = 0
for i in range(1, 9):
    l = f"E{i}"
    ext = [x.split("\t")[0] for x in open(f"{kd}/{l}.keys") if x.strip()]
    tab = t.get(l, {})
    miss, extra = sorted(set(ext) - set(tab)), sorted(set(tab) - set(ext))
    wrong = sorted(k for k, r in tab.items() if r.get("status") not in ST)
    nh = sum(1 for r in tab.values() if r.get("status") == "not-handled")
    print(f"{l}: {len(ext)} keys, {len(tab)} rows, not-handled {nh}"
          + (f"; extracted, no row: {len(miss)} {miss[:5]}" if miss else "")
          + (f"; row, not extracted: {len(extra)} {extra[:5]}" if extra else "")
          + (f"; bad status: {wrong[:5]}" if wrong else ""))
    sc = {}
    for r in tab.values(): sc[r.get("status")] = sc.get(r.get("status"), 0) + 1
    print(f"{l} by status: " + ", ".join(f"{s} {n}" for s, n in sorted(sc.items(), key=str)))
    bad += bool(miss or extra or wrong)
lk = set(re.findall(r'=> "(tree:[^"]+)"', open(lean).read()))
tk = {x.split("\t")[0] for x in open(f"{kd}/E4.keys") if x.startswith("tree:")}
if lk != tk:
    print(f"E4: ConstructsE4.lean's keys differ from the tree's: {sorted(lk ^ tk)}"); bad += 1
else:
    print(f"E4: ConstructsE4.lean maps the {len(lk)} constructors to their keys")
sys.exit(1 if bad else 0)
PY
rc=$?
python3 -I test/constructs/kfix.py check || rc=1
python3 -I test/constructs/units.py || rc=1
python3 -I test/constructs/modifiers.py check || rc=1
python3 -I test/constructs/provisional.py || rc=1
test/provenance.sh || rc=1
exit $rc
