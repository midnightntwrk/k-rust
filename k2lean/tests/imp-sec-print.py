#!/usr/bin/env python3
"""Write the security checker demos/k/imp-sec.k for kimp with `print ( E ) ;` (tests/kimp-print.py).

usage: imp-sec-print.py IMP_SEC_K OUT_FILE

Adds one equation: `sec` accepts `print ( E ) ;` at a low program counter when `E` is low, since
the output is observed. `conf` refuses it by its `owise` equation (a confined branch prints
nothing), and `lev` is unchanged. Compiled over the sources tests/kimp-print.py writes, as the
checker of `demos/ImpOutNI` (`docs/design.md`, section 3.7). The script fails if the file does not
contain exactly the text it extends.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
old = '''  rule sec(while (C) S, G) => conf(S, G) requires lev(C, G) ==K hi
'''
new = old + '''  rule sec(print ( E ) ;, G) => lev(E, G) ==K lo
'''
if text.count(old) != 1:
    sys.exit(f"imp-sec-print.py: expected exactly one occurrence of {old!r}")
open(dst, "w").write(text.replace(old, new))
