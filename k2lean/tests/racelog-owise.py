#!/usr/bin/env python3
"""Write the fixture racelog with an `owise` rule, for `k2lean confluence --equiv` with priority ranks.

usage: racelog-owise.py RACELOG_K OUT_K

Writes tests/fixtures/racelog/racelog.k with `spawn` for a positive amount of work only
(`requires N >Int 0`) and a spawn of no work skipped by an `owise` rule at priority 200, after the
default 50: `<k> spawn ( _ ) ; P => P ... </k> [owise]`, labelled `skip`. The cells and the other
rules are the fixture's, so `--equiv log=perm,last=any` reads them unchanged
(`demos/RaceLogOwConf`, `docs/design.md`, section 3.6). The script fails if the file does not
contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("""       <next> I => I +Int 1 </next> [label(spawn)]
""", """       <next> I => I +Int 1 </next> requires N >Int 0 [label(spawn)]
  rule <k> spawn ( _ ) ; P => P ... </k> [owise, label(skip)]
"""),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"racelog-owise.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
