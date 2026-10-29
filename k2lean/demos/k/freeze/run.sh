#!/usr/bin/env bash
# The freeze fixture (CT-3, CT-4b): record the frozen part of this project, then check one edit at a
# time against it, each in a copy, and compare the report and the result (k2lean-result.json: the
# statuses, and the fingerprints against the unedited library's) with what the edit should give.
#   run.sh K2L_EVAL WORK      (K2L_EVAL: the built k2l-eval; WORK: an empty scratch directory)
# Exit status 0 when every edit gives its expected report.
set -euo pipefail
eval_bin=$1 work=$2
here=$(cd "$(dirname "$0")" && pwd)
lean=$(cd "$here/../../../lean" && pwd)
mkdir -p "$work"
base=$work/base rec=$work/record
rm -rf "$base" "$rec"
cp -r "$here" "$base"
sed -i "s|require k2lean from \"../../../lean\"|require k2lean from \"$lean\"|" "$base/lakefile.lean"
(cd "$base" && lake build Frz FrzTest >/dev/null)
(cd "$base" && lake env "$eval_bin" --freeze-record Frz "$rec")
fails=0
# RESULT NAME STATUS…: in the result file RESULT, the entry NAME has STATUS (pairs)
statuses() {
  python3 -I - "$@" <<'PY' || { fails=$((fails + 1)); return 0; }
import json, sys
f, pairs = sys.argv[1], sys.argv[2:]
got = {e["name"]: e["status"] for e in json.load(open(f))["entries"]}
bad = [f"{n}: {got.get(n)} (want {s})" for n, s in zip(pairs[::2], pairs[1::2]) if got.get(n) != s]
print(f"FAIL result {f}: " + "; ".join(bad) if bad else f"ok result {len(pairs) // 2}")
sys.exit(1 if bad else 0)
PY
}
# RESULT NAME FIELD same|moved…: the entry NAME's fingerprint FIELD (stmt, of its statement; spec, of
# the definitions it reaches) in RESULT, against the unedited library's result (triples)
fingerprints() {
  python3 -I - "$work/result.json" "$@" <<'PY' || { fails=$((fails + 1)); return 0; }
import json, sys
base, f, triples = sys.argv[1], sys.argv[2], sys.argv[3:]
fp = lambda p: {e["name"]: e for e in json.load(open(p))["entries"]}
was, got = fp(base), fp(f)
bad = []
for n, k, want in zip(triples[::3], triples[1::3], triples[2::3]):
    a, b = was[n][k], got[n][k]
    if a == "-" or (a == b) != (want == "same"):
        bad.append(f"{n} {k}: {a} -> {b} (want {want})")
print(f"FAIL fingerprints {f}: " + "; ".join(bad) if bad else f"ok fingerprints {len(triples) // 3}")
sys.exit(1 if bad else 0)
PY
}
# the library's result: each status once
(cd "$base" && lake env "$eval_bin" --result Frz "$work/result.json")
statuses "$work/result.json" Frz.f_double proved Frz.g_id proved Frz.two proved Frz.bound open Frz.three refuted
# EDIT NAME EXPECTED-EXIT PATTERN [FILE SED-EXPRESSION]…: check a copy of the base with the edits;
# PATTERN must match the report (or, with an empty pattern, nothing but the summary may be reported)
edit() {
  local name=$1 want=$2 pat=$3; shift 3
  local m=$work/$name
  rm -rf "$m"; cp -r "$base" "$m"
  while [ $# -gt 0 ]; do sed -i "$2" "$m/$1"; shift 2; done
  local out st=0
  out=$(cd "$m" && lake build Frz >/dev/null && lake env "$eval_bin" --freeze-check Frz "$rec") || st=$?
  if [ "$st" != "$want" ] || { [ -n "$pat" ] && ! grep -q -- "$pat" <<<"$out"; }; then
    echo "FAIL $name: exit $st (want $want), report:"; echo "$out"; fails=$((fails + 1))
  else
    echo "ok $name: exit $st"
  fi
}
# unchanged: only the open obligation is reported, and the check's result is the library's
edit unchanged 0 '"kind":"open","name":"Frz.bound"'
cmp "$work/result.json" "$rec/k2lean-result.json" || { echo "FAIL the check's result differs"; fails=$((fails + 1)); }
# a frozen theorem restated
edit statement 1 '"kind":"moved","name":"Frz.f_double"' Frz/Proofs.lean 's/f n = 2 \* n/f n = n + n/'
statuses "$rec/k2lean-result.json" Frz.f_double moved Frz.g_id proved
fingerprints "$rec/k2lean-result.json" Frz.f_double stmt moved Frz.f_double spec same Frz.g_id stmt same
# another decreasing proof: free
edit decreasing 0 '' Frz/Spec.lean 's/^decreasing_by omega$/decreasing_by (have _h : True := trivial); omega/'
fingerprints "$rec/k2lean-result.json" Frz.g_id stmt same Frz.g_id spec same Frz.bound spec same
# another measure: the definition is frozen
edit measure 1 '"kind":"spec-moved","name":"Frz.g' Frz/Spec.lean 's/^termination_by n$/termination_by n + 1/'
fingerprints "$rec/k2lean-result.json" Frz.g_id stmt same Frz.g_id spec moved Frz.bound spec moved Frz.f_double spec same
# a frozen theorem deleted: open
edit deleted 0 '"kind":"open","name":"Frz.g_id"' Frz/Proofs.lean '/^theorem g_id/,/^  | succ/d'
statuses "$rec/k2lean-result.json" Frz.g_id open
# a refutation deleted: its obligation is open again
edit unrefuted 0 '"kind":"open","name":"Frz.three.refuted"' Frz/Proofs.lean '/^theorem three.refuted/,/^  simp \[three/d'
statuses "$rec/k2lean-result.json" Frz.three open
# a definition changed
edit definition 1 '"kind":"spec-moved","name":"Frz.f' Frz/Spec.lean 's/| n + 1 => f n + 2/| n + 1 => 2 + f n/'
fingerprints "$rec/k2lean-result.json" Frz.f_double stmt same Frz.f_double spec moved Frz.two spec moved Frz.g_id spec same
# a proof on another axiom
edit axioms 1 '"kind":"axioms","name":"Frz.two"' Frz/Proofs.lean 's/^  simp \[two.statement, f\]$/  unfold two.statement; native_decide/'
statuses "$rec/k2lean-result.json" Frz.two axioms
# the kernel's check skipped
edit lint 1 '"kind":"lint"' Frz/Proofs.lean 's/^end Frz$/set_option debug.skipKernelTC true in\ntheorem extra : True := trivial\n\nend Frz/'
# the readable statements edited
cp "$rec/k2lean.frozen.md" "$work/frozen.md.orig"
echo "edited" >> "$rec/k2lean.frozen.md"
edit readable 1 '"kind":"readable"'
cp "$work/frozen.md.orig" "$rec/k2lean.frozen.md"
[ "$fails" = 0 ] && echo "freeze fixture: every edit gives its report" || { echo "freeze fixture: $fails failed"; exit 1; }
