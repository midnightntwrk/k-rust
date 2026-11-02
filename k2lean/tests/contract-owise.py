#!/usr/bin/env python3
"""Write the fixture contract with `owise` rules, for `k2lean noninterference` with priority ranks.

usage: contract-owise.py CONTRACT_K OUT_K

Writes tests/fixtures/contract/contract.k with the second rule of each pair of the two-armed `if`
and of `repeat` as the `owise` rule: `if-true` and `if (_:Bool) _ else S => S [owise]`, `repeat`
(`requires N >Int 0`) and `repeat(_) _ => .K [owise]`. The language is the fixture's, and its
syntax too, so the fixture contractsec checks it unchanged; the `owise` rules are at priority 200,
after the default 50 (`demos/ContractOwiseNI`, `docs/design.md`, section 3.7). The script fails if
the file does not contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("""  rule [if-false]: <k> if (false) _ else S => S ... </k>
""", """  rule [if-false]: <k> if (_:Bool) _ else S => S ... </k> [owise]
"""),
    ("""  rule [repeat-done]: <k> repeat(N) _ => .K ... </k> requires N <=Int 0
""", """  rule [repeat-done]: <k> repeat(_) _ => .K ... </k> [owise]
"""),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"contract-owise.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
