#!/usr/bin/env bash
# The release run (from anywhere; run alone in its workspace): the integration run, then what it does
# not build. Prints one table (step, verdict, seconds, note); logs in .lake/release/ (ignored).
#
#   integration  test/integration.sh (its own table in .lake/integration/table.txt)
#   examples     every example package as committed, built in the kernel with its user's modules
#                (examples/run.sh --build-only): peano with its tie, the one worked example of a
#                definition read from its KORE text that `emit` gives back; ref-kimp with User.SumSpec
#                (K's claim sum-spec), User.SumN, User.SumSpecStmt, User.SumSpecGen (the statement
#                `k2lean kcore-claims` writes; test/pins-kimp.sh, run by the integration step,
#                regenerates and compares it), User.RunInstance (run_exact at
#                one configuration), User.SumSpecHolds (the statement proved at every H) and
#                User.SumSpecML (its matching-logic corollaries), User.SumSpecInstance (the claim
#                at N = 3, S = 0). Building SumSpecHolds, SumSpecML and SumSpecInstance runs each
#                module's own check of its theorems: axioms within propext, Classical.choice,
#                Quot.sound, and no hypothesis on the functions among their constants (`FnHyp`,
#                `fnHyp_defn`, `fnHyp_withHooks_defn`: through every definition and proof below
#                sum_spec_holds, sum_spec_kore and sum_spec_instance; named by the proofs of
#                stepDecided_all and the sum_spec_ml theorems, whose route through consistent,
#                sound_at and complete_at proves FnHyp as a theorem); a failing check fails the build;
#                kimp-ni's noninterference modules
#   pins-kk      test/pins-kk.sh: C10's statements (succs_sound, succs_stuck, succs_complete, kk_step at
#                KK.sig, sig's fields, succs_name, enc_injective, emb_injective, embSt_injective,
#                emb_sorted, embD_sorted, encDef_isSome, and KK.consistent) pinned in test/PinsKk.lean
#                on the package `kcore gen --core` writes for kore.k, with ref-kk's User modules up to
#                User.KkThree and User.Consistent
#   axioms-*     `#print axioms` of the examples' statements: ref-kk's KK.consistent (kore.k's theory
#                has a model at HookParams.none); peano's tie, sound_hyp, complete_hyp,
#                sound, complete; ref-kimp's sum_spec, sum_spec_entailed, sum_N, run_instance,
#                sum_spec_holds, sum_spec_kore, stepDecided_all, sum_spec_ml, sum_spec_ml_closure,
#                sum_spec_ml_stuck, sum_spec_instance; ref-kimp's row
#                statements coreOK_defn, consistent, sound_at, complete_at, run_exact, totals (every
#                [total] function is Total) and totals_withHooks (the same at every hook
#                interpretation H); ref-kk's coreOK_defn, sound_hyp, complete_hyp (kore.k's text);
#                C10 at kimp (User.KimpInst, built by the examples step over ref-kk and ref-kimp):
#                encDef_kimp, succs_at, step_named;
#                the noninterference results over kimp, imp-sec, imp-sec-leaky, vault, vault-leaky
#   tripwire     in the code (comments and strings removed) of KcoreSpec, KcoreGen.lean, GammaD.lean,
#                examples and test: no `sorry`, `native_decide`, `decide +native`, `bv_decide`,
#                `implemented_by`, `extern` attribute, `debug.skipKernelTC`, nor an `axiom`
#                declaration. Not the check (the axioms rows of test/integration.sh are): it covers
#                what no declaration holds, such as an `example`'s proof
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
# axioms NAME 'PKG...' 'IMPORT...' 'DECL...'...: the axioms of DECL... (every argument from the
# fourth on), over the built packages PKG...
axioms() {
  local f=$R/$1.lean lp=$LP p m d out
  for p in $2; do lp=$K/examples/$p/.lake/build/lib/lean:$lp; done
  : > "$f"; for m in $3; do echo "import $m" >> "$f"; done
  for d in ${*:4}; do echo "#print axioms $d" >> "$f"; done
  out=$(LEAN_PATH=$lp cap 1200 "$TC/bin/lean" -j1 "$f" 2>&1) || { echo "$out"; return 1; }
  echo "$out"
  [ "$(echo "$out" | grep -c 'depends on axioms\|does not depend on any axioms')" -eq "$(echo ${*:4} | wc -w)" ] \
    || { echo "axioms: not every declaration printed"; return 1; }
  if echo "$out" | grep 'depends on axioms' | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' \
      | sed 's/^ *//' | grep -v -x -e propext -e Classical.choice -e Quot.sound | grep -q .; then
    echo "axioms: beyond propext, Classical.choice, Quot.sound"; return 1
  fi
  echo "axioms: $(echo ${*:4} | wc -w) declarations within propext, Classical.choice, Quot.sound"
}
tripwire() {
  python3 -I - KcoreSpec KcoreGen.lean GammaD.lean examples test <<'NS'
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
pat = re.compile(r'\bsorry\b|\bnative_decide\b|\bdecide\s*\+\s*native\b|\bbv_decide\b|\bimplemented_by\b'
                 r'|@\[\s*extern\b|\bskipKernelTC\b'
                 r'|^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe|partial)\s+)*axiom\s')
hits = [f'{f}:{k}: {l.strip()[:80]}' for f in sorted(fs) for k, l in enumerate(code(open(f).read()).split('\n'), 1)
        if pat.search(l)]
print('\n'.join(hits + [f'tripwire: {len(hits)} in the code of {len(fs)} files']))
sys.exit(1 if hits else 0)
NS
}

step integration test/integration.sh
LP=$(lake env printenv LEAN_PATH)
step examples examples/run.sh --build-only
step pins-kk test/pins-kk.sh
# the axioms steps read the packages' oleans: only after every package was built by this run
if grep -q '|ok|' "$R/examples.res"; then
  step axioms-peano axioms axioms-peano peano 'Peano.Tie Peano.Sound' \
    'Peano.tied Peano.sound_hyp Peano.complete_hyp Peano.sound Peano.complete Peano.coreOK_defn'
  step axioms-sumspec axioms axioms-sumspec ref-kimp 'RefKimp.Sound User.SumSpec User.SumN User.RunInstance User.SumSpecHolds User.SumSpecML User.SumSpecInstance' \
    'RefKimp.SumSpec.sum_spec RefKimp.SumSpec.sum_spec_entailed RefKimp.SumN.sum_N RefKimp.sound_hyp RefKimp.complete_hyp RefKimp.RunInstance.run_instance RefKimp.Claims.sum_spec_holds RefKimp.Claims.sum_spec_kore RefKimp.stepDecided_all RefKimp.Claims.sum_spec_ml RefKimp.Claims.sum_spec_ml_closure RefKimp.Claims.sum_spec_ml_stuck RefKimp.Claims.sum_spec_instance'
  step axioms-refkimp axioms axioms-refkimp ref-kimp 'RefKimp.Sound RefKimp.FnHyp RefKimp.Facts.Terminates' \
    'RefKimp.coreOK_defn RefKimp.consistent RefKimp.sound_at RefKimp.complete_at RefKimp.run_exact RefKimp.totals RefKimp.totals_withHooks'
  step axioms-refkk axioms axioms-refkk ref-kk 'RefKk.Sound User.Consistent' KK.consistent \
    'RefKk.coreOK_defn RefKk.sound_hyp RefKk.complete_hyp'
  step axioms-kkinst axioms axioms-kkinst 'ref-kimp ref-kk' 'User.KimpInst' \
    'KCore.KK.KimpInst.encDef_kimp KCore.KK.KimpInst.succs_at KCore.KK.KimpInst.step_named'
  step axioms-ni axioms axioms-ni 'kimp imp-sec imp-sec-leaky kink-imp vault vault-leaky kimp-ni' \
    'NI.Leak NI.Kind NI.Keyed Kimp.Kinds.NI Vault VaultLeaky User.Leak' \
    'NI.leaky_not_ni NI.checkers_differ NI.kimpNI_of_unwinding Kimp.noninterference NI.Keyed.not_noninterference NI.Keyed.var_not_unwinds Vault.noninterference VaultLeaky.noninterference VaultLeaky.not_noninterference VaultLeaky.leak_not_unwinds'
else
  for n in axioms-peano axioms-sumspec axioms-refkimp axioms-refkk axioms-kkinst axioms-ni; do echo "$n|not run|0|the examples step failed" > "$R/$n.res"; done
fi
step tripwire tripwire

printf '%-16s %-7s %7s  %s\n' step verdict seconds note
fail=0
for n in integration examples pins-kk axioms-peano axioms-sumspec axioms-refkimp axioms-refkk axioms-kkinst axioms-ni tripwire; do
  IFS='|' read -r a b c d < "$R/$n.res"
  printf '%-16s %-7s %7s  %s\n' "$a" "$b" "$c" "$d"
  [ "$b" = ok ] || fail=1
done
echo "total: $(( $(date +%s) - T0 )) s"
exit $fail
