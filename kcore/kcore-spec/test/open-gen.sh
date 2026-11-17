#!/usr/bin/env bash
# The generator's packages for the kompiled texts with an open generator (`kcore gen --core`),
# generated into .lake/open-gen (ignored) and built (gen/build.sh: one module a process, one thread,
# 12 GiB memory scope). The kernel facts about the texts at values are test/OpenKompiled.lean's.
# - e2-comm-ctor (f2-examples/commctor.kompile.kore): `and` (no law) and `or` (`assoc`);
# - e2-open-rule (f2-examples/openrule.kompile.kore): `and` (no law), a rule and a function;
# - e2-idem-ctor (f2-examples/idemctor.kompile.kore): `or` (`idem`);
# - e2-band-ctor (f2-examples/bandctor.kompile.kore): `or` (`assoc` and `idem`).
# For each: the text is the fixture's kompiled text (with K's builtin directory written back as
# BUILTIN/ and the fixture's directory as FIXTURE/, its sha256 is the one the fixture's kompile.txt
# records) and `kcore account` of it prints the fixture's account.txt from its `user module` line on;
# the package states each statement of a model or of the semantics for every H with
# `OpenLaws (defn.sem.withHooks H)` and `OpenTotal (defn.sem.withHooks H)` (`hop`, `_hot`), never at
# one fixed H; it states both obligations discharged at `lawHooks defn.sem H` for every H
# (`openLaws_lawHooks_defn`, `openTotal_lawHooks_defn`) with the library's sentences at
# `lawHooks defn.sem HookParams.lib` (`lawHooks_lib_defn`) and each statement's instance there
# (`consistent_lawHooks`, `sound_defn_lawHooks`, ...); it names both obligations among its facts;
# and it builds, with the user module test/open-gen/NS/User.lean where there is one (copied in as
# NS.User and built against the package): e2-comm-ctor's `exact_defn` (`ExactC` for every H with
# OpenLaws and OpenTotal) and e2-open-rule's `go_one` (for every H with OpenTotal, `<k> go </k>`
# has one successor), each with its instance at lawHooks, from the package's `fnHyp_defn`.
# Usage: test/open-gen.sh   (from anywhere; the library and `kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
O=.lake/open-gen; mkdir -p "$O"
fail=0
say() { echo "open-gen: $*"; fail=1; }
BI=/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406/include/kframework/builtin
all="commctor:e2-comm-ctor:OpenComm openrule:e2-open-rule:OpenRuleK idemctor:e2-idem-ctor:OpenIdem bandctor:e2-band-ctor:OpenBand"
for p in $all; do
  IFS=: read -r t x ns <<< "$p"; X=test/constructs/fixtures/$x
  sha=$(sed -e "s#$BI/#BUILTIN/#g" -e "s#kcore-spec/$X/#FIXTURE/#g" "f2-examples/$t.kompile.kore" | sha256sum | cut -d' ' -f1)
  grep -q "^definition.kore sha256: $sha$" "$X/kompile.txt" || say "$t: not the kompiled text of $x (sha256 $sha)"
  diff <(.lake/build/bin/kcore account "f2-examples/$t.kompile.kore" 2>&1 | sed -n '/^user module/,$p') \
    <(sed -n '/^user module/,$p' "$X/account.txt" | grep -v '^(exit 0)$') > /dev/null || say "$t: the account differs from $x's"
  rm -rf "$O/$t"
  gen/gen.sh "f2-examples/$t.kompile.kore" "$O/$t" "$ns" --core > "$O/$t.log" 2>&1 \
    || { tail -20 "$O/$t.log"; say "kcore gen --core on $t fails"; continue; }
  F=$O/$t/$ns/FnHyp.lean
  [ -f "$F" ] || { say "$t: no FnHyp.lean"; continue; }
  # every theorem whose statement names Consistent, SoundC, CompleteC, ExactC or FnHyp at
  # defn.sem.withHooks H takes hop and _hot
  awk '/^theorem /{if (s != "") print s; s=$0; next} /^$|^\/-|^def |^abbrev /{if (s != "") print s; s=""; next} s != ""{s=s" "$0} END{if (s != "") print s}' "$F" \
    | grep -E 'withHooks H\)' | grep -E 'Consistent|SoundC|CompleteC|ExactC|FnHyp ' \
    | grep -v '(hop : OpenLaws (defn.sem.withHooks H)) (_hot : OpenTotal (defn.sem.withHooks H))' \
    | sed 's/^/  without hop and _hot: /' | grep . && say "$t: a statement at H takes no hop or _hot"
  grep -q 'HookParams.none' "$F" && say "$t: a statement at HookParams.none"
  for n in openLaws_lawHooks_defn openTotal_lawHooks_defn libAdmitted_lawHooks_defn lawHooks_lib_defn; do
    grep -q "^theorem $n " "$F" || say "$t: no $n"
  done
  [ "$(grep -c '^def [A-Za-z_]*_lawHooks' "$F")" -ge 3 ] || say "$t: fewer than three statements instantiated at lawHooks"
  grep -q 'KCore.OpenLaws' "$F" && grep -q 'KCore.OpenTotal' "$F" || say "$t: the facts do not name OpenLaws and OpenTotal"
done
[ $fail = 0 ] || exit 1
for p in $all; do
  IFS=: read -r t x ns <<< "$p"
  u=; if [ -f "test/open-gen/$ns/User.lean" ]; then cp "test/open-gen/$ns/User.lean" "$O/$t/$ns/User.lean"; u=$ns.User; fi
  gen/build.sh "$O/$t" $u > "$O/$t-build.log" 2>&1 || { tail -30 "$O/$t-build.log"; say "$t: the package does not build"; exit 1; }
done
echo "open-gen: four packages state their statements for every H under OpenLaws and OpenTotal, discharge both at lawHooks, and build, with the user modules of e2-comm-ctor (exact) and e2-open-rule (go has one successor): ok"
