#!/usr/bin/env bash
# The release run (from anywhere; run alone in its workspace): the integration run, then what it does
# not build. Prints one table (step, verdict, seconds, note); logs in .lake/release/ (ignored).
#
#   integration  test/integration.sh (its own table in .lake/integration/table.txt)
#   examples     every example package as committed, built in the kernel with its user's modules
#                (examples/run.sh --build-only): peano with its tie, the one worked example of a
#                definition read from its KORE text that `emit` gives back; ref-kimp with User.SumSpec
#                (K's claim sum-spec), User.SumN, User.SumSpecStmt and User.RunInstance (run_exact at
#                one configuration); kimp-ni's noninterference modules
#   axioms-*     `#print axioms` of the examples' statements: peano's tie, sound_hyp, complete_hyp,
#                sound, complete; ref-kimp's sum_spec, sum_spec_entailed, sum_N, run_instance; ref-kimp's row
#                statements coreOK_defn, consistent, sound_at, complete_at, run_exact and totals (every
#                [total] function is Total); the noninterference results over kimp, imp-sec,
#                imp-sec-leaky, vault, vault-leaky
#   sorry        no `sorry` in the code of KcoreSpec, KcoreGen.lean, examples (comments excluded)
#
# No step builds a KEVM or mir package: the release run builds the committed example packages only.
#
# An axioms step fails when a printed line names an axiom other than propext, Classical.choice,
# Quot.sound. Every Lean process under its own 12 GiB memory scope, one thread. Exit status 1 when a
# step is not ok. Usage: test/release.sh   (KCORE_CONE as for test/integration.sh)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
R=.lake/release; mkdir -p "$R"; rm -f "$R"/*.res "$R"/*.log
T0=$(date +%s)
echo "release: $(free -g | awk '/^Mem:/ {print $7}') GiB available ($(date +%FT%T%z))"
cap() { LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout "$@"; }
step() {
  local name=$1 t0 rc note; shift
  t0=$(date +%s)
  "$@" > "$R/$name.log" 2>&1; rc=$?
  note=$(grep -v '^\s*$' "$R/$name.log" | tail -1 | cut -c1-100 | tr '|' '/')
  [ $rc -eq 0 ] && v=ok || { v=FAIL; note="exit $rc: $note"; }
  echo "$name|$v|$(( $(date +%s) - t0 ))|$note" > "$R/$name.res"
}
# axioms NAME 'PKG...' 'IMPORT...' 'DECL...': the axioms of DECL..., over the built packages PKG...
axioms() {
  local f=$R/$1.lean lp=$LP p m d out
  for p in $2; do lp=$K/examples/$p/.lake/build/lib/lean:$lp; done
  : > "$f"; for m in $3; do echo "import $m" >> "$f"; done
  for d in $4; do echo "#print axioms $d" >> "$f"; done
  out=$(LEAN_PATH=$lp cap 1200 "$TC/bin/lean" -j1 "$f" 2>&1) || { echo "$out"; return 1; }
  echo "$out"
  [ "$(echo "$out" | grep -c 'depends on axioms\|does not depend on any axioms')" -eq "$(echo $4 | wc -w)" ] \
    || { echo "axioms: not every declaration printed"; return 1; }
  if echo "$out" | grep 'depends on axioms' | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' \
      | sed 's/^ *//' | grep -v -x -e propext -e Classical.choice -e Quot.sound | grep -q .; then
    echo "axioms: beyond propext, Classical.choice, Quot.sound"; return 1
  fi
  echo "axioms: $(echo $4 | wc -w) declarations within propext, Classical.choice, Quot.sound"
}
noSorry() {
  python3 -I - KcoreSpec KcoreGen.lean examples <<'NS'
import os, re, sys
def code(t):
    # the text without comments (nested /- -/ and --) and string literals
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith('/-', i): depth += 1; i += 2; continue
        if depth and t.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: out.append('\n' if t[i] == '\n' else ' '); i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = n if j < 0 else j; continue
        if t.startswith("'\\\"'", i) or t.startswith("'\"'", i):
            i += 4 if t[i + 1] == '\\' else 3; out.append("' '"); continue
        if t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"': j += 2 if t[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(t[i]); i += 1
    return ''.join(out)
fs = []
for r in sys.argv[1:]:
    if os.path.isfile(r): fs.append(r); continue
    for d, ds, ns in os.walk(r):
        ds[:] = [x for x in ds if x != '.lake']
        fs += [os.path.join(d, x) for x in ns if x.endswith('.lean')]
hits = [f'{f}:{k}' for f in sorted(fs) for k, l in enumerate(code(open(f).read()).split('\n'), 1)
        if re.search(r'\bsorry\b', l)]
print('\n'.join(hits + [f'sorry: {len(hits)} in the code of {len(fs)} files']))
sys.exit(1 if hits else 0)
NS
}

step integration test/integration.sh
LP=$(lake env printenv LEAN_PATH)
step examples examples/run.sh --build-only
# the axioms steps read the packages' oleans: only after every package was built by this run
if grep -q '|ok|' "$R/examples.res"; then
  step axioms-peano axioms axioms-peano peano 'Peano.Tie Peano.Sound' \
    'Peano.tied Peano.sound_hyp Peano.complete_hyp Peano.sound Peano.complete Peano.coreOK_defn'
  step axioms-sumspec axioms axioms-sumspec ref-kimp 'RefKimp.Sound User.SumSpec User.SumN User.RunInstance' \
    'RefKimp.SumSpec.sum_spec RefKimp.SumSpec.sum_spec_entailed RefKimp.SumN.sum_N RefKimp.sound_hyp RefKimp.complete_hyp RefKimp.RunInstance.run_instance'
  step axioms-refkimp axioms axioms-refkimp ref-kimp 'RefKimp.Sound RefKimp.FnHyp RefKimp.Facts.Terminates' \
    'RefKimp.coreOK_defn RefKimp.consistent RefKimp.sound_at RefKimp.complete_at RefKimp.run_exact RefKimp.totals'
  step axioms-ni axioms axioms-ni 'kimp imp-sec imp-sec-leaky kink-imp vault vault-leaky kimp-ni' \
    'NI.Leak NI.Kind NI.Keyed Kimp.Kinds.NI Vault VaultLeaky User.Leak' \
    'NI.leaky_not_ni NI.checkers_differ NI.kimpNI_of_unwinding Kimp.noninterference NI.Keyed.not_noninterference NI.Keyed.var_not_unwinds Vault.noninterference VaultLeaky.noninterference VaultLeaky.not_noninterference VaultLeaky.leak_not_unwinds'
else
  for n in axioms-peano axioms-sumspec axioms-refkimp axioms-ni; do echo "$n|not run|0|the examples step failed" > "$R/$n.res"; done
fi
step sorry noSorry

printf '%-16s %-7s %7s  %s\n' step verdict seconds note
fail=0
for n in integration examples axioms-peano axioms-sumspec axioms-refkimp axioms-ni sorry; do
  IFS='|' read -r a b c d < "$R/$n.res"
  printf '%-16s %-7s %7s  %s\n' "$a" "$b" "$c" "$d"
  [ "$b" = ok ] || fail=1
done
echo "total: $(( $(date +%s) - T0 )) s"
exit $fail
