#!/usr/bin/env python3
"""Write kimp with `owise` rules, for `k2lean noninterference` with priority ranks.

usage: kimp-owise.py KIMP_DIR OUT_DIR

Copies kimp's `calc.k` and writes its `expr.k` and `imp.k` with the second rule of each pair of
`&&`, `||` and the two-armed `if` as the `owise` rule over any Boolean: `false && _ => false` and
`_:Bool && B => B [owise]`, `true || _ => true` and `_:Bool || B => B [owise]`, `if-true` and
`if ( _:Bool ) _ else S2 => S2 [owise]`. The language is kimp's, and its syntax too, so
`demos/k/imp-sec.k` checks it unchanged; the `owise` rules are at priority 200, after the default
50 (`demos/ImpOwiseNI`, `docs/design.md`, section 3.7). The script fails if a file does not
contain exactly the text it rewrites.
"""
import os
import shutil
import sys

src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
shutil.copy(os.path.join(src, "calc.k"), os.path.join(dst, "calc.k"))
edits = {
    "expr.k": [
        ("""  rule true  && B => B
  rule false && _ => false
""", """  rule false && _ => false
  rule _:Bool && B => B [owise]
"""),
        ("""  rule false || B => B
""", """  rule _:Bool || B => B [owise]
"""),
    ],
    "imp.k": [
        ("""  rule [if-false]: <k> if ( false ) _  else S2 => S2 ... </k>
""", """  rule [if-false]: <k> if ( _:Bool ) _  else S2 => S2 ... </k> [owise]
"""),
    ],
}
for f, es in edits.items():
    text = open(os.path.join(src, f)).read()
    for old, new in es:
        if text.count(old) != 1:
            sys.exit(f"kimp-owise.py: expected exactly one occurrence of {old!r} in {f}")
        text = text.replace(old, new)
    open(os.path.join(dst, f), "w").write(text)
