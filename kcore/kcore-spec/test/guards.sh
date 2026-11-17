#!/usr/bin/env bash
# The table of readings (DONE-0 C6) of test/Guards.lean, checked. Exit 1 when:
#   - the file does not elaborate: among the causes, a constructor of ReadingNote, InertReason or
#     UnreadReason with no entry (its `match` misses a case), a name literal of a guard that no
#     longer exists, a constructor list that is not the inductive's, or an entry marked guarded none
#     of whose guards is a declaration quantified over H : HookParams that states something about
#     Semantics.withHooks (C6's form; the file's `run_cmd`s);
#   - a wildcard arm stands between the file's `-- table:begin` and `-- table:end` lines (it would
#     give a new constructor an entry nobody wrote);
#   - a pointer into another test file names a file that does not exist or a text it does not hold;
#   - no entry is printed.
# Prints every pending entry with the ticket that owes it, and the counts. Pending entries do not
# fail the check (GUARD.final asks for none on the INT-D line).
# Lean runs under a 12 GiB memory scope, one thread. Run from anywhere; after `lake build`.
# Usage: test/guards.sh [FILE]      (FILE defaults to test/Guards.lean; another copy for a probe)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
F=${1:-test/Guards.lean}
[ -f "$F" ] || { echo "guards: no file $F"; exit 2; }
out=$(mktemp); trap 'rm -f "$out"' EXIT
fail=0

LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  timeout 2400 lake env lean -j1 "$F" > "$out" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  echo "guards: $F does not elaborate (exit $rc):"
  grep -E 'error' "$out" | head -20
  fail=1
fi

wild=$(awk '/^-- table:begin/{t=1; next} /^-- table:end/{t=0} t && /^[[:space:]]*\|[[:space:]]*_[[:space:]]*=>/' "$F")
if [ -n "$wild" ]; then echo "guards: a wildcard arm in the table:"; echo "$wild"; fail=1; fi
grep -q '^-- table:begin' "$F" && grep -q '^-- table:end' "$F" || { echo "guards: no table:begin / table:end lines"; fail=1; }

lines=$(grep -o 'GUARD|.*' "$out")
n=$(printf '%s\n' "$lines" | grep -c '^GUARD|')
[ "$n" -gt 0 ] || { echo "guards: no entry printed"; fail=1; }

declare -A count
pending=()
while IFS='|' read -r _ ctor status guard comp inv note; do
  [ -n "$ctor" ] || continue
  count[${status%% *}]=$(( ${count[${status%% *}]:-0} + 1 ))
  for r in ${guard//;/ } ${comp//;/ }; do
    case $r in
      test/*#*)
        file=${r%%#*}; needle=${r#*#}
        if [ ! -f "$file" ]; then echo "guards: $ctor: no file $file"; fail=1
        elif ! grep -qF -- "$needle" "$file"; then echo "guards: $ctor: $file holds no '$needle'"; fail=1; fi;;
    esac
  done
  case $status in
    pending*) pending+=("  $ctor  [${status#pending }]  $note");;
  esac
done <<< "$lines"

echo "guards: $n entries: ${count[guarded]:-0} guarded, ${count[reader-test]:-0} reader-test, ${count[pending]:-0} pending"
if [ ${#pending[@]} -gt 0 ]; then
  echo "pending (ticket that owes the entry):"
  printf '%s\n' "${pending[@]}"
fi
grep -o 'GUARD-UNNOTED|.*' "$out" | while IFS='|' read -r _ what ctor; do
  echo "un-noted reading (REVIEW-RN finding 7) $what: $ctor"
done
[ $fail -eq 0 ] && echo "guards: ok" || echo "guards: FAIL"
exit $fail
