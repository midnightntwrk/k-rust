#!/usr/bin/env bash
# The generator's packages for the two texts of a `non-executable` equation beside an `[owise]` one
# (`kcore gen --core`), generated into .lake/nonexec-owise (ignored) and built (gen/build.sh: one module
# a process, one thread, 12 GiB memory scope). The kernel facts about the two texts are
# test/NonExecOwiseTie.lean's.
# - e5-owise-nonexec (f2-examples/owisenx.kompile.kore), a text with no model: `agree_named` is
#   [choose] and `namedFacts` holds the agreement of choose; `Obl` is `FnFacts`; `obl_nil` is not
#   stated; the statements of a model are stated only with the suffix `_of` (`consistent_of`,
#   `sound_at_of`, `complete_at_of`), each taking `hob`, and the statements of the semantics
#   (`fnHyp_defn`, `sound_defn`, `complete_defn` and their `_withHooks_` forms) take `hob`. That
#   fact is false of this text (test/NonExecOwiseTie.lean, `NX.not_agree`), so no statement of the
#   package claims a model.
# - e5-owise-nonexec-agree (f2-examples/owisenxagree.kompile.kore): the same lines; the fact holds
#   (test/NonExecOwiseTie.lean, `AG.facts`), so its statements hold.
# First, each f2-examples text is the fixture's kompiled text: with K's builtin directory written back
# as BUILTIN/ and the fixture's directory as FIXTURE/, its sha256 is the one the fixture's kompile.txt
# records, and `kcore account` of it prints the fixture's account.txt from its `user module` line on.
# Usage: test/nonexec-owise-gen.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
O=.lake/nonexec-owise; mkdir -p "$O"
fail=0
say() { echo "nonexec-owise-gen: $*"; fail=1; }
BI=/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/include/kframework/builtin
for p in "owisenx e5-owise-nonexec" "owisenxagree e5-owise-nonexec-agree"; do
  set -- $p; X=test/constructs/fixtures/$2
  sha=$(sed -e "s#$BI/#BUILTIN/#g" -e "s#kcore-spec/$X/#FIXTURE/#g" "f2-examples/$1.kompile.kore" | sha256sum | cut -d' ' -f1)
  grep -q "^definition.kore sha256: $sha$" "$X/kompile.txt" || say "$1: not the kompiled text of $2 (sha256 $sha)"
  diff <(.lake/build/bin/kcore account "f2-examples/$1.kompile.kore" 2>&1 | sed -n '/^user module/,$p') \
    <(sed -n '/^user module/,$p' "$X/account.txt" | grep -v '^(exit 0)$') > /dev/null || say "$1: the account differs from $2's"
done
for p in "owisenx NxOwise e5-owise-nonexec.k" "owisenxagree NxOwiseAgree e5-owise-nonexec-agree.k"; do
  set -- $p; t=$1; ns=$2; src=$3
  rm -rf "$O/$t"
  gen/gen.sh "f2-examples/$t.kompile.kore" "$O/$t" "$ns" --core > "$O/$t.log" 2>&1 \
    || { cat "$O/$t.log"; say "kcore gen --core on $t fails"; continue; }
  F=$O/$t/$ns/FnHyp.lean; A=$O/$t/$ns/FnHyp/Agree.lean
  [ "$(tr '\n' ' ' < "$A" | sed -nE 's/.*theorem agree_named : defn\.sem\.agreeObligationsI = +(\[[^]]*\]).*/\1/p')" = "[387 /- choose -/]" ] \
    || say "$t: agree_named is not [choose]"
  [ "$(sed -n '/^def namedFacts/,/\]$/p' "$F" | grep -c '"')" = 1 ] || say "$t: namedFacts does not name one fact"
  grep -q "^  \"agreement choose $src:3\"\]$" "$F" || say "$t: namedFacts does not hold the agreement of choose"
  grep -q '^abbrev Obl : Prop := FnFacts defn.sem callOrder \[\]$' "$F" || say "$t: Obl is not FnFacts"
  [ "$(tr -d ' \n' < "$O/$t/$ns/FnHyp/Order.lean" | sed -nE 's/.*defcallOrder:ListNat:=(\[[^]]*\]).*/\1/p')" = "[387]" ] \
    || say "$t: callOrder is not [387] (test/NonExecOwiseTie.lean's AG.callOrder)"
  grep -q 'obl_nil\|plain_defn' "$F" && say "$t: obl_nil or plain_defn is stated"
  for n in consistent sound_at complete_at; do
    grep -q "^theorem $n " "$F" && say "$t: $n is stated without the suffix _of"
    grep -q "^theorem ${n}_of (H : HookParams) (hob : OblH H)" "$F" || say "$t: ${n}_of does not take hob"
  done
  for n in fnHyp_defn sound_defn; do
    grep -q "^theorem $n (hob : Obl)" "$F" || say "$t: $n does not take hob"
  done
  grep -q "^theorem complete_defn (ref : OutFn) (hob : Obl)" "$F" || say "$t: complete_defn does not take hob"
  for n in fnHyp_withHooks_defn sound_withHooks_defn; do
    grep -q "^theorem $n (H : HookParams) (hob : OblH H)" "$F" || say "$t: $n does not take hob"
  done
  grep -q "^theorem complete_withHooks_defn (ref : OutFn) (H : HookParams) (hob : OblH H)" "$F" \
    || say "$t: complete_withHooks_defn does not take hob"
  # every theorem whose statement names Consistent, SoundC, CompleteC or FnHyp takes hob
  awk '/^theorem /{if (s != "") print s; s=$0; next} /^$|^\/-|^def |^abbrev /{if (s != "") print s; s=""; next} s != ""{s=s" "$0} END{if (s != "") print s}' "$F" \
    | grep -E 'Consistent|SoundC|CompleteC|FnHyp ' | grep -v '(hob : Obl' | sed 's/^/  without hob: /' | grep . \
    && say "$t: a statement of a model or of the semantics takes no hob"
  grep -rq 'run_exact\|step_iff' "$O/$t/$ns" && say "$t: run_exact or step_iff is stated"
done
[ $fail = 0 ] || exit 1
for t in owisenx owisenxagree; do gen/build.sh "$O/$t" > "$O/$t-build.log" 2>&1 || { tail -30 "$O/$t-build.log"; exit 1; }; done
echo "nonexec-owise-gen: both packages name the agreement of choose alone, state no model without it, and build: ok"
