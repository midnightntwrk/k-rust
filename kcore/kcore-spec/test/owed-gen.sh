#!/usr/bin/env bash
# The generator's text for the texts whose rules leave a variable open (`kcore gen --core`), checked
# against what each text owes. Three fixtures, their kompiled texts in f2-examples, generated into
# .lake/owed (ignored); nothing is built here (test/OwedGen.lean applies the generated terms on the
# reader's semantics of the two texts that owe a condition).
# - e2-unbound (`a() => b(X)`, no condition): not `plain`, nothing owed. `owed_rules` and
#   `owed_clauses` are empty, `obl_nil` is stated, no statement takes `how`, `hw` or `hc`, and no
#   name ends in `_of`.
# - e2-rule (the `[cool]` and `[heat]` rules, closed over HOLE:K): `owed_rules` is [6, 7].
# - e2-open-genless (`a() => b() requires isMk(X:S)`): `owed_rules` is [0].
#   For both: `Owed` is `OpenDecided defn.sem`; `fnHyp_defn`, `sound_defn` and `complete_defn` take
#   `(how : Owed)`; `sound_at_of` takes the pinned `hw` and no `hc` (no clause is owed);
#   `consistent` and `complete_at` keep their names and take no owed condition.
# - e2-unbound with `--wf`: the exit status and the generator's summary line are printed, and the
#   hypothesis `sound` takes. `wf` reads `OpenDecided` through `Obligations defn`, not rule by rule.
# Usage: test/owed-gen.sh   (from anywhere; `lake build kcore` first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
O=.lake/owed; mkdir -p "$O"
fail=0
say() { echo "owed-gen: $*"; fail=1; }
gen() {  # gen TEXT DIR NAMESPACE OPTION
  rm -rf "$O/$2"
  gen/gen.sh "f2-examples/$1.kompile.kore" "$O/$2" "$3" "$4" > "$O/$2.log" 2>&1
  local rc=$?
  [ $rc = 0 ] || { cat "$O/$2.log"; say "kcore gen $4 on $1 exits $rc"; return 1; }
  cmp -s "f2-examples/$1.kompile.kore" "$O/$2/$3/definition.kore" || say "$2: definition.kore is not f2-examples/$1.kompile.kore"
}
# the list a theorem of FnHyp/Owed.lean states, its comments and line breaks removed
owed() { tr '\n' ' ' < "$1" | sed -E 's|/-[^/]*-/||g; s/ +/ /g; s/ ,/,/g; s/ \]/]/g' | sed -nE "s/.*theorem $2 : defn\.sem\.[A-Za-z]+ = (\(?\[[^]]*\]).*/\1/p"; }

gen unbound unbound OwedUnb --core
gen rulecool rulecool OwedCool --core
gen opengenless opengenless OwedGl --core
[ $fail = 0 ] || exit 1

F=$O/unbound/OwedUnb/FnHyp.lean; W=$O/unbound/OwedUnb/FnHyp/Owed.lean
[ "$(owed "$W" owed_rules)" = "([]" ] || say "unbound: owed_rules is $(owed "$W" owed_rules)"
[ "$(owed "$W" owed_clauses)" = "([]" ] || say "unbound: owed_clauses is $(owed "$W" owed_clauses)"
grep -q 'plain_defn' "$F" && say "unbound: plain_defn is stated"
grep -q 'theorem obl_nil : Obl := FnFacts.of_nil' "$F" || say "unbound: no obl_nil"
grep -q 'theorem [A-Za-z_]*_of \|(how :\|(hw :\|(hc :\|abbrev Owed' "$F" && say "unbound: an _of name, or how, hw, hc or Owed"
for t in fnHyp_defn sound_defn consistent sound_at complete_at; do
  grep -q "^theorem $t " "$F" || say "unbound: no $t"
done

for p in "rulecool OwedCool [6, 7]" "opengenless OwedGl [0]"; do
  set -- $p; d=$1; ns=$2; shift 2; want="$*"
  F=$O/$d/$ns/FnHyp.lean; W=$O/$d/$ns/FnHyp/Owed.lean
  [ "$(owed "$W" owed_rules)" = "$want" ] || say "$d: owed_rules is $(owed "$W" owed_rules), not $want"
  [ "$(owed "$W" owed_clauses)" = "([]" ] || say "$d: owed_clauses is $(owed "$W" owed_clauses)"
  grep -q '^abbrev Owed : Prop := OpenDecided defn.sem$' "$F" || say "$d: Owed is not OpenDecided defn.sem"
  grep -q '^theorem obl_nil : Obl := FnFacts.of_nil' "$F" || say "$d: no obl_nil"
  grep -q '^theorem fnHyp_defn (how : Owed) : FnHyp defn.sem ' "$F" || say "$d: fnHyp_defn does not take how"
  grep -q '^theorem sound_defn (how : Owed) : SoundC defn.sem := sound_fn .*(obl_nil.obligations how)$' "$F" || say "$d: sound_defn is not sound_fn at obl_nil.obligations how"
  grep -q '^theorem complete_defn (ref : OutFn) (how : Owed) : CompleteC defn.sem ref ' "$F" || say "$d: complete_defn does not take how"
  grep -q '^theorem sound_at_of ' "$F" || say "$d: no sound_at_of"
  grep -q '^theorem sound_at ' "$F" && say "$d: sound_at is stated without its suffix"
  [ "$(grep -c "(hw : ∀ r' ∈" "$F")" = 1 ] || say "$d: sound_at_of does not take hw once"
  grep -q '(hc : ∀ fn ∈' "$F" && say "$d: a statement takes hc though no clause is owed"
  grep -q '^theorem consistent (H : HookParams) : Consistent (defn.sem.withHooks H) :=$' "$F" || say "$d: consistent is not stated without a hypothesis"
  grep -q '^  consistent_of_fnFacts ' "$F" || say "$d: consistent is not consistent_of_fnFacts"
  grep -q '^theorem complete_at ' "$F" || say "$d: no complete_at"
  grep -q '^theorem consistent_of \|^theorem complete_at_of ' "$F" && say "$d: consistent or complete_at has the suffix _of"
  # between complete_at's name and its proof no binder is an owed condition
  sed -n '/^theorem complete_at /,/^  ⟨/p' "$F" | grep -q '(how :\|(hw :\|(hob :' && say "$d: complete_at takes an owed condition"
done
[ $fail = 0 ] || exit 1
echo "owed-gen: e2-unbound owes nothing; e2-rule owes rules [6, 7]; e2-open-genless owes rule [0]: ok"

rm -rf "$O/unbound-wf"
gen/gen.sh f2-examples/unbound.kompile.kore "$O/unbound-wf" OwedUnbWf --wf > "$O/unbound-wf.log" 2>&1
rc=$?
echo "owed-gen: kcore gen --wf on e2-unbound exits $rc: $(grep '^{"ns"' "$O/unbound-wf.log")"
[ $rc = 0 ] && grep -h '^theorem sound \|^theorem obligations_nil' "$O"/unbound-wf/OwedUnbWf/*.lean | sed 's/^/owed-gen:   /'
exit 0
