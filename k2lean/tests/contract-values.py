#!/usr/bin/env python3
"""Write the fixture contract with its values two sorts below `KResult`, for `k2lean noninterference`
with several sorts of values.

usage: contract-values.py CONTRACT_K OUT_K

Writes tests/fixtures/contract/contract.k with `syntax KResult ::= Int | Bool` for
`syntax KResult ::= Value`, as K's tutorial languages declare their results: the sort `Value` stays
(`Value ::= Int | Bool`, the rules' `V:Value`), but it is no longer below `KResult`, so the values
of the holes are two sorts, `Int` and `Bool`. The rules are the fixture's, and its syntax but for
that one declaration, so the fixture contractsec checks it unchanged (`demos/ContractValsNI`,
`docs/design.md`, section 3.7). The script fails if the file does not contain exactly the text it
rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("  syntax KResult ::= Value\n", "  syntax KResult ::= Int | Bool\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"contract-values.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
