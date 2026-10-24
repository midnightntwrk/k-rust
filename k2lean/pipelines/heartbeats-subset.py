#!/usr/bin/env python3
"""heartbeats-subset.py HEARTBEATS.txt OUT.txt GEN.log: the heartbeat overrides file without the
entries that `gen` names as naming no generated theorem in GEN.log (kevm.sh, TARGET=evm: the
equations of the functions that only KEVM's driver defines, which the compiled `EVM` module does
not generate)."""
import ast, re, sys
src, out, log = sys.argv[1:4]
m = re.search(r"names no generated theorem: (\[.*\])$", open(log).read(), re.M)
drop = set(ast.literal_eval(m.group(1))) if m else set()
lines = open(src).read().splitlines(True)
keep = [l for l in lines if l.strip().startswith("#") or not l.strip() or l.split()[0] not in drop]
open(out, "w").write("".join(keep))
print(f"{len(lines) - len(keep)} entries dropped")
sys.exit(0 if drop else 1)
