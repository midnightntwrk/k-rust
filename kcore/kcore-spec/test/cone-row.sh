#!/usr/bin/env bash
# integration's cone row (test/integration.sh): the review cone NEW (default .lake/cone-v.txt, which
# test/ConeV.lean writes; computing it is the caller's) against the committed one, by test/cone.py
# with --roots test/roots.toml: the roots, the declaration names, the line count, each declaration's
# own line count and each declaration's text. Never rewrites either file.
#
# The committed cone is `kcore/core-cone.txt` at BASE, the main revision the tree is on
# (`git merge-base HEAD main`, or $KCORE_CONE_BASE). Its declarations' texts are read from the tree
# it was computed at: the last commit at or before BASE that changed kcore/core-cone.txt (a refreeze
# commits the cone with the sources it was computed from), or $KCORE_CONE_REV.
# $KCORE_CONE names another committed cone file; then $KCORE_CONE_REV, the revision it was computed
# at, is required.
#
# Exit 0 when the cones agree, 1 when they differ or when the committed cone or its revision cannot
# be found (cone.py's own exit status otherwise, 2 when a source cannot be read).
# Usage: test/cone-row.sh [NEW]          (run from anywhere)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
new=${1:-.lake/cone-v.txt}
[ -f "$new" ] || { echo "cone: no computed cone at $new"; exit 1; }
if [ -n "${KCORE_CONE:-}" ]; then
  ref=$KCORE_CONE
  [ -f "$ref" ] || { echo "cone: no committed cone at $ref"; exit 1; }
  rev=${KCORE_CONE_REV:-}
  [ -n "$rev" ] || { echo "cone: KCORE_CONE=$ref without KCORE_CONE_REV, the revision it was computed at"; exit 1; }
else
  base=${KCORE_CONE_BASE:-$(git merge-base HEAD main 2>/dev/null)}
  [ -n "$base" ] || { echo "cone: no main revision the tree is on (git merge-base HEAD main)"; exit 1; }
  ref=$(mktemp); trap 'rm -f "$ref"' EXIT
  git show "$base:./../core-cone.txt" > "$ref" 2>/dev/null \
    || { echo "cone: no kcore/core-cone.txt at $base"; exit 1; }
  rev=${KCORE_CONE_REV:-$(git log -1 --format=%H "$base" -- ../core-cone.txt)}
  [ -n "$rev" ] || { echo "cone: no commit at or before $base changed kcore/core-cone.txt"; exit 1; }
  echo "cone: committed cone kcore/core-cone.txt at $base"
fi
echo "cone: its texts read at $rev"
python3 -I test/cone.py "$ref" "$new" --old-git "$rev" --roots test/roots.toml
