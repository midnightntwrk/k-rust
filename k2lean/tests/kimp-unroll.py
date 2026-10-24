#!/usr/bin/env python3
"""Write a variant of kimp's `imp.k` whose `while` unrolls in one step less, for `k2lean refine`.

usage: kimp-unroll.py IN/imp.k OUT/imp.k

kimp's `while ( C ) S` rewrites to the one-armed `if ( C ) { S while ( C ) S }`, which the rule
`if-else` then completes with an empty `else {}`; in the variant, `while` rewrites to the
two-armed form directly. Every other rule is unchanged, so the two definitions take the same
steps except at a loop, where kimp takes two steps for the variant's one: the demonstration
`demos/ImpUnroll` relates them by a stuttering bisimulation (`docs/design.md`, section 3.5).
The script fails if the source does not contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
old = """      if ( C ) {
        S
        while ( C ) S
      }
"""
new = """      if ( C ) {
        S
        while ( C ) S
      } else {}
"""
if text.count(old) != 1:
    sys.exit(f"kimp-unroll.py: expected exactly one occurrence of {old!r}")
open(dst, "w").write(text.replace(old, new))
