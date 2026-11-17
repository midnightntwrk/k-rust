#!/usr/bin/env bash
# integration's cone row (test/integration.sh): the review cone NEW (default .lake/cone-v.txt, which
# test/ConeV.lean writes; computing it is the caller's) against the committed one, by test/cone.py
# with --roots test/roots.toml: the roots, the declaration names, the line count, each declaration's
# own line count and each declaration's text. Never rewrites either file.
#
# The committed cone is `kcore/core-cone.txt` at BASE, the main revision the tree is on
# (`git merge-base HEAD main`, or $KCORE_CONE_BASE). Its declarations' texts are read from the tree
# it was computed at: the revision its `# computed at git REV` line names (test/cone-freeze.sh writes
# it), or $KCORE_CONE_REV, which takes precedence. Neither the commit that last changed the file nor
# any other header line is read, so an edit of the header alone does not change the verdict.
# $KCORE_CONE names another committed cone file, read the same way.
# The freeze: `[tree].frozen_at` of kcore/core-manifest.toml at BASE lists the trees the cone was
# frozen at. When it is not empty, its last entry must be the revision of core-cone.txt's
# `# computed at git` line (exit 1 otherwise), so the comparison is with the last freeze; when it is
# empty, the committed cone is a baseline and the script says so. Not read with $KCORE_CONE.
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
  what=$ref
else
  base=${KCORE_CONE_BASE:-$(git merge-base HEAD main 2>/dev/null)}
  [ -n "$base" ] || { echo "cone: no main revision the tree is on (git merge-base HEAD main)"; exit 1; }
  ref=$(mktemp); trap 'rm -f "$ref"' EXIT
  git show "$base:./../core-cone.txt" > "$ref" 2>/dev/null \
    || { echo "cone: no kcore/core-cone.txt at $base"; exit 1; }
  what="kcore/core-cone.txt at $base"
  echo "cone: committed cone $what"
fi
stamp=$(sed -n 's/^# computed at git \([0-9a-f]\{7,40\}\)\( .*\)\{0,1\}$/\1/p' "$ref" | head -1)
if [ -z "${KCORE_CONE:-}" ]; then
  frozen=$(git show "$base:./../core-manifest.toml" 2>/dev/null | python3 -I -c '
import sys, tomllib
f = tomllib.loads(sys.stdin.read()).get("tree", {}).get("frozen_at")
if not isinstance(f, list) or not all(isinstance(x, str) for x in f): sys.exit(1)
print(f[-1] if f else "")') \
    || { echo "cone: kcore/core-manifest.toml at $base has no [tree].frozen_at list"; exit 1; }
  if [ -z "$frozen" ]; then
    echo "cone: not frozen ([tree].frozen_at is empty): the committed cone is a baseline"
  else
    a=$(git rev-parse --verify -q "$frozen^{commit}") || { echo "cone: $frozen, the last entry of [tree].frozen_at, is not a commit here"; exit 1; }
    b=$(git rev-parse --verify -q "${stamp:-none}^{commit}")
    [ "$a" = "$b" ] || { echo "cone: $what was computed at ${stamp:-no stated revision}, not at $frozen, the last entry of [tree].frozen_at"; exit 1; }
    echo "cone: frozen at $frozen, the last entry of [tree].frozen_at"
  fi
fi
rev=${KCORE_CONE_REV:-$stamp}
[ -n "$rev" ] || { echo "cone: $what has no '# computed at git REV' line; give KCORE_CONE_REV, the revision it was computed at"; exit 1; }
git rev-parse --verify -q "$rev^{commit}" > /dev/null || { echo "cone: $rev, the revision $what was computed at, is not a commit here"; exit 1; }
echo "cone: its texts read at $rev"
python3 -I test/cone.py "$ref" "$new" --old-git "$rev" --roots test/roots.toml
