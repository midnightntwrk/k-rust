#!/usr/bin/env python3
"""Write a checker of the fixture contract that misses a flow (tests/fixtures/contractsec).

usage: contractsec-leaky.py CONTRACTSEC_K OUT_FILE

`conf` accepts `emit(E);` under a private branch when `E` is quiet, though `emit` appends to the
public `<transcript>`: the implicit flow `if (h < 5) { emit(1); } else { }` leaks whether `h < 5`.
So noninterference does not hold, the per-rule case of the confined `emit` step does not either
(listed open), and two runs refute the open cases (`demos/ContractLeakNI`, `docs/design.md`,
section 3.7). The written file requires `contract.k` from the include path (the fixture contract's
directory). The script fails if the file does not contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ('requires "../contract/contract.k"\n', 'requires "contract.k"\n'),
    ("  rule conf(repeat(_) S, G) => conf(S, G)\n",
     "  rule conf(repeat(_) S, G) => conf(S, G)\n  rule conf(emit(E) ;, G) => quiet(E, G)\n"),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"contractsec-leaky.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
