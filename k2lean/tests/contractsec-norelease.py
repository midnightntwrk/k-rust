#!/usr/bin/env python3
"""Write the checker of the fixture contract that releases nothing (tests/fixtures/contractsec).

usage: contractsec-norelease.py CONTRACTSEC_K OUT_FILE

`disclose(E)` has `E`'s level, where the fixture's checker makes it low (the release that
noninterference up to disclosure assumes). With every cell an observer sees compared by equality,
`<disclosed>` included, the statement is plain noninterference, `demos/ContractObsNI`
(`docs/design.md`, section 3.7). The written file requires `contract.k` from the include path (the
fixture contract's directory). The script fails if the file does not contain exactly the text it
rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ('requires "../contract/contract.k"\n', 'requires "contract.k"\n'),
    ("  rule lev(disclose(E), G) => lo requires lev(E, G) ==K lo orBool quiet(E, G)\n",
     "  rule lev(disclose(E), G) => lev(E, G)\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"contractsec-norelease.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
