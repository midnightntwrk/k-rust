#!/usr/bin/env bash
# Row imp, read (DONE-0 C9 parts 1 and 6): `kcore account` on ref-kimp's text, kompile's own KORE of
# kimp (examples/ref-kimp/RefKimp/definition.kore), compared with test/imp-account.expected. Exit 1
# when the output differs from the expected one, or when any of these does not hold of it:
#   - no sentence classified refused, no stage refusal, no read sentence left unaccounted, no
#     refusal by the account, `parse: ok`, `coreOK: true`;
#   - the constructor the text does not declare is gone: the reading holds no constructor of the
#     library's data that the text does not state (`sentences the library's data induces that the
#     text does not hold: 0`, `libraryUnstated`: every library constructor's declaration and axioms
#     `emit` writes from the data the text holds), and the text names no `#KConfigValue`
#     (`Lbl'Hash'KConfigValue`, the registry constructor the reading once held: triage IMP-ctor).
#     The other constructors are the text's own (its user module's symbols) or KSEQ's kseq and dotk,
#     which the text's module KSEQ declares (`kernelAbsent` lists only the four projection
#     sentences below, no constructor).
# Prints the readings the text uses: the reading notes (sentences classified `read NOTE`, the
# connective readings, and the counts of the readings no sentence is classified as:
# ruleRightDefined, keyFunctionAsMember, equationPriority, owiseAsPriority,
# owiseDisjunctNarrower), then the inert and unread classes. Run after `lake build kcore`.
# Usage: test/imp-account.sh
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
KORE=examples/ref-kimp/RefKimp/definition.kore
EXP=test/imp-account.expected
[ -x .lake/build/bin/kcore ] || { echo "imp-account: no .lake/build/bin/kcore (lake build kcore)"; exit 2; }
out=$(mktemp); trap 'rm -f "$out"' EXIT
LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  timeout 600 .lake/build/bin/kcore account "$KORE" > "$out" 2>&1 || { echo "imp-account: kcore account failed"; tail -3 "$out"; exit 1; }
fail=0
need() { grep -qxF -- "$1" "$out" || { echo "imp-account: missing line: $1"; fail=1; }; }
need "stage refusals (of sentences classified read): 0"
need "read and not accounted for: 0"
need "refused by the account: 0"
need "parse: ok; wf true; failing: []"
need "coreOK: true; failing: []"
need "sentences the library's data induces that the text does not hold: 0"
need "library sentences of the modules held that the text does not hold: 0"
if grep -qE '^  [0-9]+ refused' "$out"; then echo "imp-account: sentences classified refused:"; grep -E '^  [0-9]+ refused' "$out"; fail=1; fi
if grep -q "KConfigValue" "$KORE"; then echo "imp-account: the text names #KConfigValue"; fail=1; fi
if ! diff -u "$EXP" "$out" > /dev/null; then
  echo "imp-account: the account differs from $EXP:"; diff -u "$EXP" "$out" | head -40; fail=1
fi

echo "reading notes the text uses:"
grep -E '^  [0-9]+ read [a-zA-Z]+ ' "$out" | sed 's/^ */  /'
sed -n '/^connective readings per sentence/p' "$out" | sed 's/^/  /'
grep -E '\((ruleRightDefined|keyFunctionAsMember|equationPriority|owiseAsPriority|owiseDisjunctNarrower)\)' "$out" \
  | sed -E 's/^(.*) \(([A-Za-z]+)\): ([0-9]+)$/  \2: \3  (\1)/'
echo "inert and unread classes:"
grep -E '^  [0-9]+ (inert|unread) ' "$out" | sed 's/^ */  /'
[ $fail -eq 0 ] && echo "imp-account: ok (refuses nothing; no constructor the text does not declare)" || echo "imp-account: FAIL"
exit $fail
