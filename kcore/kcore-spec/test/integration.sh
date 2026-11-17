#!/usr/bin/env bash
# The integration run, once per merged batch (from anywhere; run alone in its workspace). Prints one
# table: check, kind, verdict, seconds, note; logs in .lake/integration/NAME.log (ignored).
#
# required (the exit status is 1 when one of these is not ok):
#   library     the KcoreSpec modules, built one at a time (test/lake-serial.sh)
#   kcore       the native executable (`lake build kcore`)
#   pins        test/Pins.lean: the headline statements restated, their axioms
#   pins-peano  test/pins-peano.sh: the statements a generated package states, on peano
#   axioms      test/Axioms.lean: every declaration of the library within propext, Classical.choice, Quot.sound
#   witnesses   test/Witnesses.lean: the witness modules' theorems, and their axioms
#   cone        the review cone (v) (test/ConeV.lean, computed from the root list test/roots.toml) against the
#               committed one, kcore/core-cone.txt at the main revision the tree is on (or $KCORE_CONE), its
#               texts read at the revision its `# computed at git REV` line names, which must be the last
#               entry of core-manifest.toml's [tree].frozen_at once that is not empty (test/cone-row.sh): that it
#               was computed from test/roots.toml, declaration names, line count, each declaration's own line
#               count and each declaration's text (test/cone.py); never rewritten
# scoreboard (red allowed; each compares with its expected values, so a lane that changes them
# updates one file):
#   regen       every example package regenerated natively from its own NAME/definition.kore,
#               compared with the committed package (test/regen.sh): all identical
#   roundtrip   `kcore roundtrip` over the f2-examples and the package inputs (test/roundtrip.sh,
#               test/roundtrip.expected)
#   corpus      the reference cache's kompiled texts through `kcore gen --core` (test/corpus.py,
#               test/corpus.expected): read clean, coreOK
#   agree       `kcore agree` over test/agree.jsonl, the cases built from the reference backends' cached
#               results (test/agree.sh, test/agree.expected; after corpus, whose extraction holds
#               the cases' definitions)
#   agree-kore-in-k  `kcore agree` over test/agree-kore-in-k.jsonl, the kore-in-k corpus's 49 cases
#               against each backend's recorded finals (test/agree-kore-in-k.py builds the case file
#               and the kompiled texts in .lake/kore-in-k; test/agree-kore-in-k.expected);
#               `skipped` (neither ok nor red) when .lake/kore-in-k is absent: the texts are built
#               from a corpus outside this tree (test/README.md, "The kore-in-k corpus")
#   member      test/member.sh: why each text is or is not tied, the frozen registry table
#   not-plain   test/not-plain.sh: the generator's text for a definition that is not `plain`
#               (`kcore gen --as-not-plain`), on peano (--core) and prio (--wf), built
#   pred-sorted test/PredSorted.lean over the regenerated peano package, built without the tie
#   user        the hand-written modules over the committed packages (User.*, kimp-ni's NI.*):
#               `examples/run.sh --build-only` over the packages that have them, and ref-peano
#   cs2         the CS-2 consumer (../consumer/cs2/build.sh), every module of CS2/ named (there is no
#               root module CS2), their oleans removed first (build.sh compares a module's olean with
#               its source only); after user, whose ref-kimp and
#               ref-peano it reads; `skipped` when the k2lean directory ($K2LEAN) is absent
#   test/X      every other test/*.lean checked by `lean`: the kompiled text per K construct and the
#               library's small cores (not ReviewCone, which writes the committed cones, nor
#               PrintNames, a command-line tool)
#
# The native checks run first, then the Lean checks, JOBS at once: JOBS is the available memory
# (`free -g` at start) over 12 GiB, between 1 and 8, or $INTEGRATION_JOBS. Every Lean and `kcore`
# process runs under its own 12 GiB memory scope, one thread.
# Usage: test/integration.sh
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
R=.lake/integration; mkdir -p "$R"; rm -f "$R"/*.res "$R"/*.log
avail=$(free -g | awk '/^Mem:/ {print $7}')
J=${INTEGRATION_JOBS:-$(( avail / 12 ))}; [ "$J" -lt 1 ] && J=1; [ "$J" -gt 8 ] && J=8
T0=$(date +%s)
echo "integration: $avail GiB available, $J at once ($(date +%FT%T%z))"
cap() { LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout "$@"; }

# check NAME KIND CMD...: CMD's output in $R/NAME.log, its line in $R/NAME.res
# (name|kind|verdict|seconds|note); the note is the log's last line. Exit status 77 is `skipped`:
# the check's inputs are not present.
check() {
  local name=$1 kind=$2; shift 2
  local f=${name//\//_} t0 rc v note
  t0=$(date +%s)
  "$@" > "$R/$f.log" 2>&1; rc=$?
  if [ $rc -eq 0 ] && grep -q "declaration uses 'sorry'" "$R/$f.log"; then rc=99; fi
  if [ $rc -eq 0 ]; then v=ok; elif [ $rc -eq 77 ] && [ "$kind" = scoreboard ]; then v=skipped
  elif [ "$kind" = required ]; then v=FAIL; else v=red; fi
  note=$(grep -v '^\s*$' "$R/$f.log" | tail -1 | cut -c1-90 | tr '|' '/')
  [ $rc -ne 0 ] && [ "$v" != skipped ] && note="exit $rc: $note"
  echo "$name|$kind|$v|$(( $(date +%s) - t0 ))|$note" > "$R/$f.res"
}
# pool: run `check` in the background, at most J at once
pool() { while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do wait -n; done; check "$@" & }
lean1() { LEAN_PATH=$LP cap 2400 "$TC/bin/lean" -j1 "$1"; }
cone() { lean1 test/ConeV.lean && test/cone-row.sh .lake/cone-v.txt; }
agreeKoreInK() {
  [ -d .lake/kore-in-k ] || { echo "texts not built"; return 77; }
  test/agree.sh test/agree-kore-in-k.jsonl test/agree-kore-in-k.expected
}
predSorted() {
  [ -d .lake/regen/peano ] || { echo "no regenerated peano (test/regen.sh)"; return 1; }
  gen/build.sh .lake/regen/peano > "$R/pred-sorted-build.log" 2>&1 \
    || { tail -5 "$R/pred-sorted-build.log"; return 1; }
  LEAN_PATH=.lake/regen/peano/.lake/build/lib/lean:$LP cap 1200 "$TC/bin/lean" -j1 test/PredSorted.lean
}
userModules() {
  examples/run.sh --build-only peano prio kink-imp kimp imp-sec imp-sec-leaky ph kimp-ni colls-list \
    lazy fprio colls ref-peano ref-fprio ref-kimp vault-leaky
}
# the k2lean directory: $K2LEAN, or k2lean/ in the nearest directory above kcore-spec holding one
# with lean/prelude (the k-rust checkout); exported for ../consumer/cs2/build.sh
k2lean() {
  local d=$K
  while [ "$d" != / ]; do d=$(dirname "$d"); [ -d "$d/k2lean/lean/prelude" ] && { echo "$d/k2lean"; return; }; done
}
cs2() {
  export K2LEAN=${K2LEAN:-$(k2lean)}
  [ -n "$K2LEAN" ] && [ -d "$K2LEAN" ] || { echo "no k2lean directory"; return 77; }
  [ -d ../consumer/cs2/.lake/build/lib/lean/CS2 ] && find ../consumer/cs2/.lake/build/lib/lean/CS2 -name '*.olean' -delete
  rm -f ../consumer/cs2/.lake/build/lib/lean/CS2.olean
  ../consumer/cs2/build.sh $(cd ../consumer/cs2/CS2 && ls *.lean | sed 's/\.lean$//; s/^/CS2./')
}
table() {
  local order=$1 fail=0 l
  printf '%-26s %-10s %-7s %7s  %s\n' check kind verdict seconds note
  for n in $order; do
    l=$(cat "$R/${n//\//_}.res" 2>/dev/null) || l="$n|?|not run|-|"
    IFS='|' read -r a b c d e <<< "$l"
    printf '%-26s %-10s %-7s %7s  %s\n' "$a" "$b" "$c" "$d" "$e"
    [ "$b" = required ] && [ "$c" != ok ] && fail=1
  done
  echo "total: $(( $(date +%s) - T0 )) s"
  return $fail
}

order="library kcore"
check library required test/lake-serial.sh
check kcore required cap 1800 lake build kcore
if grep -q '|FAIL|' "$R/library.res" "$R/kcore.res"; then
  table "$order" > "$R/table.txt"; cat "$R/table.txt"; exit 1
fi
LP=$(lake env printenv LEAN_PATH)

# native checks
order="$order regen roundtrip corpus agree agree-kore-in-k"
check regen scoreboard test/regen.sh -j "$J"
check roundtrip scoreboard test/roundtrip.sh
check corpus scoreboard python3 -I test/corpus.py -j "$J" --expected test/corpus.expected
check agree scoreboard test/agree.sh
check agree-kore-in-k scoreboard agreeKoreInK

# Lean checks, the longest first
order="$order pins pins-peano axioms witnesses cone member not-plain pred-sorted user cs2"
while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do wait -n; done
{ check user scoreboard userModules; check cs2 scoreboard cs2; } &
pool pred-sorted scoreboard predSorted
pool pins-peano required test/pins-peano.sh
pool member scoreboard test/member.sh
pool not-plain scoreboard test/not-plain.sh
pool pins required lean1 test/Pins.lean
pool axioms required lean1 test/Axioms.lean
pool witnesses required lean1 test/Witnesses.lean
pool cone required cone
for f in test/*.lean; do
  case $(basename "$f" .lean) in
    Pins|PinsPeano|Axioms|Witnesses|ConeV|ReviewCone|PrintNames|Member|PredSorted) continue;;
  esac
  order="$order ${f%.lean}"
  pool "${f%.lean}" scoreboard lean1 "$f"
done
wait
table "$order" > "$R/table.txt"; rc=$?
cat "$R/table.txt"
exit $rc
