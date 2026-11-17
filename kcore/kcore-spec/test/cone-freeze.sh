#!/usr/bin/env bash
# Writes the committed review cone (v), kcore/core-cone.txt. Computes it first (test/lake-par.py,
# then test/ConeV.lean, which writes .lake/cone-v.txt from the root list test/roots.toml), then
# writes that cone with two lines added after its own header: the files that compute it, and
# `# computed at git REV`, the git revision whose sources the declarations' texts are read at
# (test/cone-row.sh reads its texts there, so an edit of the header alone changes nothing it reads).
#
# REV is `git merge-base HEAD main`, or $KCORE_CONE_REV. The script refuses, writing nothing, when a
# Lean source or a lake file of the package, ../aml-port or ../kore-lean differs from REV (committed
# since, staged, unstaged or untracked): the cone would then not be REV's. Last, test/cone.py compares
# the written file with the computed cone, its texts read at REV; the exit status is cone.py's.
# Commit the written file in a commit that changes no such source, so that REV's sources are the
# commit's own.
# Usage: test/cone-freeze.sh          (run from anywhere)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
rev=${KCORE_CONE_REV:-$(git merge-base HEAD main 2>/dev/null)}
[ -n "$rev" ] || { echo "cone-freeze: no revision (git merge-base HEAD main, or KCORE_CONE_REV)"; exit 1; }
rev=$(git rev-parse --verify -q "$rev^{commit}") || { echo "cone-freeze: $rev is not a commit"; exit 1; }
src='\.lean$|(^|/)(lakefile\.(lean|toml)|lake-manifest\.json|lean-toolchain)$'
moved=$( { git diff --name-only "$rev" -- . ../aml-port ../kore-lean
           git ls-files --others --exclude-standard -- . ../aml-port ../kore-lean; } | grep -E "$src")
if [ -n "$moved" ]; then
  echo "cone-freeze: sources differ from $rev, nothing written:"; echo "$moved" | sed 's/^/  /'; exit 1
fi
python3 -I test/lake-par.py || { echo "cone-freeze: the library does not build"; exit 1; }
LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
  timeout 1800 lake env lean -j1 test/ConeV.lean || { echo "cone-freeze: test/ConeV.lean failed"; exit 1; }
awk -v rev="$rev" '
  h == 0 && !/^#/ {
    print "# written by kcore-spec/test/ConeV.lean to kcore-spec/.lake/cone-v.txt and by kcore-spec/test/ReviewCone.lean to kcore-spec/.lake/review-cone-core-hyp.txt; kcore-spec/test/cone.py compares either with this file"
    print "# computed at git " rev " (written by kcore-spec/test/cone-freeze.sh): the sources its declarations'"'"' texts are read at"
    h = 1
  }
  { print }' .lake/cone-v.txt > ../core-cone.txt
echo "cone-freeze: wrote kcore/core-cone.txt, computed at $rev"
python3 -I test/cone.py ../core-cone.txt .lake/cone-v.txt --old-git "$rev" --roots test/roots.toml
