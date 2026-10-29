#!/usr/bin/env bash
# The freeze fixture (CT-3): record the frozen part of this project, then check one edit at a time
# against it, each in a copy, and compare the report with what the edit should give.
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
# unchanged: only the open obligation is reported
edit unchanged 0 '"kind":"open","name":"Frz.bound"'
# a frozen theorem restated
edit statement 1 '"kind":"moved","name":"Frz.f_double"' Frz/Proofs.lean 's/f n = 2 \* n/f n = n + n/'
# another decreasing proof: free
edit decreasing 0 '' Frz/Spec.lean 's/^decreasing_by omega$/decreasing_by (have _h : True := trivial); omega/'
# another measure: the definition is frozen
edit measure 1 '"kind":"spec-moved","name":"Frz.g' Frz/Spec.lean 's/^termination_by n$/termination_by n + 1/'
# a frozen theorem deleted: open
edit deleted 0 '"kind":"open","name":"Frz.g_id"' Frz/Proofs.lean '/^theorem g_id/,/^  | succ/d'
# a definition changed
edit definition 1 '"kind":"spec-moved","name":"Frz.f' Frz/Spec.lean 's/| n + 1 => f n + 2/| n + 1 => 2 + f n/'
# a proof on another axiom
edit axioms 1 '"kind":"axioms","name":"Frz.two"' Frz/Proofs.lean 's/^  simp \[two.statement, f\]$/  unfold two.statement; native_decide/'
# the kernel's check skipped
edit lint 1 '"kind":"lint"' Frz/Proofs.lean 's/^end Frz$/set_option debug.skipKernelTC true in\ntheorem extra : True := trivial\n\nend Frz/'
# the readable statements edited
cp "$rec/k2lean.frozen.md" "$work/frozen.md.orig"
echo "edited" >> "$rec/k2lean.frozen.md"
edit readable 1 '"kind":"readable"'
cp "$work/frozen.md.orig" "$rec/k2lean.frozen.md"
[ "$fails" = 0 ] && echo "freeze fixture: every edit gives its report" || { echo "freeze fixture: $fails failed"; exit 1; }
