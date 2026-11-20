#!/usr/bin/env bash
# Row KORE in K, the tie statements that read the generated package (test/kk-tie.toml): copies the
# committed package examples/ref-kk into .lake/pins/kk-tie (ignored; apart from the package's
# own build, which examples/run.sh writes), builds it there with gen/build.sh when its oleans are
# missing or older than the library's or than its sources, then checks against it, each in its own
# process, one thread, under a 12 GiB memory scope (no swap):
#   test/TieKkAtValues.lean    function functional, hooked functional, collection law and library,
#                              at values, every H or every H meeting libAdmitted;
#   test/TieKkRefuted.lean     set idempotence and the set-variable lemmas, refuted, every H;
#   test/TieKkCountEmpty.lean  the library's 521 (domains.md 1898), refuted with 202, every H.
# Each file is checked from a copy in .lake/axioms-tests with the import of KcoreSpec.AxiomsCheck put
# first and `#axioms_here` appended, as integration's test/X rows are: every declaration of the file
# depends on no axiom but propext, Classical.choice, Quot.sound, and a run without that verdict fails.
# Per file: wall time and peak RSS (k2lean/tests/rtime.py). Exit 1 at the first failure.
# Usage: test/kk-tie-atvalues.sh   (from anywhere; the library built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0
if [ -n "${K_RUST:-}" ]; then RT=$K_RUST/k2lean/tests/rtime.py
else RT=; d=$K; while [ "$d" != / ]; do d=$(dirname "$d")
  [ -f "$d/k2lean/tests/rtime.py" ] && { RT=$d/k2lean/tests/rtime.py; break; }; done; fi
[ -f "$RT" ] || { echo "kk-tie-atvalues: no k2lean/tests/rtime.py above $K: set K_RUST"; exit 1; }
P=.lake/pins/kk-tie; O=$P/.lake/build/lib/lean/RefKk.olean
mkdir -p "$P"
rsync -a --checksum --delete --exclude=.lake examples/ref-kk/ "$P/" || exit 1
if [ ! -f "$O" ] || [ -n "$(find .lake/build/lib/lean "$P/RefKk" "$P/RefKk.lean" -newer "$O" \
    \( -name '*.olean' -o -name '*.lean' -o -name '*.kore' \) -print -quit)" ]; then
  gen/build.sh "$P" > .lake/pins/kk-tie-build.log 2>&1 || { tail -40 .lake/pins/kk-tie-build.log; exit 1; }
fi
LP=$K/$P/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)
mkdir -p .lake/axioms-tests
for f in TieKkAtValues TieKkRefuted TieKkCountEmpty; do
  w=.lake/axioms-tests/$f.lean
  { echo "import KcoreSpec.AxiomsCheck"; cat "test/$f.lean"; printf '\n#axioms_here\n'; } > "$w"
  out=$(LEAN_PATH=$LP LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
    timeout 1200 python3 "$RT" "$TC/bin/lean" -j1 "$w" 2>&1 < /dev/null)
  r=$(echo "$out" | grep -o 'wall [0-9.]* s.*exit [0-9-]*' | sed 's/max child //')
  v=$(echo "$out" | grep -o 'axioms: [0-9]* declarations of this file')
  echo "test/$f.lean: ${r:-killed (no rtime line: the memory scope or the timeout)}; ${v:-no axioms verdict}"
  case "$r" in *"exit 0") [ -n "$v" ] || { echo "$out" | grep -v '^rtime' | head -40; exit 1; } ;;
    *) echo "$out" | grep -v '^rtime' | head -40; exit 1;; esac
done
echo "kk-tie-atvalues: ok"
