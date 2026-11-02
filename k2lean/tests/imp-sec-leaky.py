#!/usr/bin/env python3
"""Write a security checker for kimp that misses a flow (demos/k/imp-sec.k).

usage: imp-sec-leaky.py IMP_SEC_K OUT_FILE

`conf` accepts an assignment to any identifier under a high branch, a low one included: the
implicit flow `if (h > 0) l = 1;` leaks whether `h > 0`. So noninterference does not hold, the
per-rule case of the confined assignment does not either (listed open), and two runs refute the
open cases (`demos/ImpLeakNI`, `docs/design.md`, section 3.7). The script fails if the file does
not contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
old = "  rule conf(X:Id = _ ;, G) => lev(X, G) ==K hi\n"
new = "  rule conf(_:Id = _ ;, _) => true\n"
if text.count(old) != 1:
    sys.exit(f"imp-sec-leaky.py: expected exactly one occurrence of {old!r}")
open(dst, "w").write(text.replace(old, new))
