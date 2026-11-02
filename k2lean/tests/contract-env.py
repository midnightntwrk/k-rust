#!/usr/bin/env python3
"""Write the fixture contract with its store an input, for `k2lean noninterference --disclosed` with
a related store input.

usage: contract-env.py CONTRACT_K OUT_K

Writes tests/fixtures/contract/contract.k with `<env> $ENV:Map </env>` for `<env> .Map </env>`: the
two runs start from stores related by the store's relation (`lowEq G`, low-equal stores). The
language is the fixture's, and its syntax too, so the fixture contractsec checks it unchanged
(`demos/ContractEnvNI`, `docs/design.md`, section 3.7). The script fails if the file does not
contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("    <env> .Map </env>\n", "    <env> $ENV:Map </env>\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"contract-env.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
