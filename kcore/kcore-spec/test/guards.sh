#!/usr/bin/env bash
# The tables of test/Guards.lean, checked: the table of readings (DONE-0 C6), the families table (the
# pieces of Γ, Γcl and Γstep, DONE-0 C14 part 2 "more, with its note") and the table of the tie
# classes whose direction is not the default (C14 closure (c)). Exit 1 when:
#   - the file does not elaborate: among the causes, a constructor of ReadingNote, InertReason,
#     UnreadReason or GammaFamily with no entry (its `match` misses a case), a name literal of a guard
#     that no longer exists, a constructor list that is not the inductive's, an entry marked guarded
#     none of whose guards is a declaration quantified over H : HookParams that states something
#     about Semantics.withHooks (C6's form; the file's `run_cmd`s), a guard of the minimum (REVIEW-RN
#     section 3: G1, G2, G3, G5, G6, G7, rest_undetermined) that is missing or not of that form, a
#     part of Γ, a disjunct, an item kind of `sigItems` or a list of `distinctSorts` that no piece
#     holds (`families_cover`), a
#     non-default class of `tieClassesOvl` without its row (`tieClassRows_exhaustive`), or a pending
#     entry of the families or class table;
#   - a wildcard arm stands between the file's `-- table:begin` and `-- table:end` lines (it would
#     give a new constructor an entry nobody wrote);
#   - a pointer into another test file names a file that does not exist or a text it does not hold;
#   - an entry of any of the three tables is pending;
#   - no entry of a table is printed.
# Prints every pending entry with the ticket that owes it, the counts of each table, and the
# minimum's guards.
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
  fail=1
fi

# The families table and the class table: the same fields under their own prefixes.
for tbl in FAMILY CLASS; do
  rows=$(grep -o "GUARD-$tbl|.*" "$out")
  m=$(printf '%s\n' "$rows" | grep -c "^GUARD-$tbl|")
  [ "$m" -gt 0 ] || { echo "guards: no $tbl entry printed"; fail=1; }
  declare -A tc=()
  while IFS='|' read -r _ name status guard comp inv note; do
    [ -n "$name" ] || continue
    tc[${status%% *}]=$(( ${tc[${status%% *}]:-0} + 1 ))
    for r in ${guard//;/ } ${comp//;/ }; do
      case $r in
        test/*#*)
          file=${r%%#*}; needle=${r#*#}
          if [ ! -f "$file" ]; then echo "guards: $tbl $name: no file $file"; fail=1
          elif ! grep -qF -- "$needle" "$file"; then echo "guards: $tbl $name: $file holds no '$needle'"; fail=1; fi;;
      esac
    done
    case $status in
      pending*) echo "guards: $tbl $name is pending"; fail=1;;
    esac
    echo "  ${tbl,,} $name: $status: $guard"
  done <<< "$rows"
  echo "guards: $m ${tbl,,} entries: ${tc[guarded]:-0} guarded, ${tc[stated]:-0} stated, ${tc[reader-test]:-0} reader-test, ${tc[pending]:-0} pending"
  unset tc
done
grep -o 'GUARD-UNNOTED|.*' "$out" | while IFS='|' read -r _ what ctor; do
  echo "un-noted reading (REVIEW-RN finding 7) $what: $ctor"
done
grep -o 'GUARD-MINIMUM|.*' "$out" | while IFS='|' read -r _ g names; do
  echo "minimum (REVIEW-RN section 3) $g: ${names//;/, }"
done
[ $fail -eq 0 ] && echo "guards: ok" || echo "guards: FAIL"
exit $fail
