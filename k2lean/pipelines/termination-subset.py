#!/usr/bin/env python3
"""termination-subset.py TERMINATION.toml OUT.toml LABEL...: the termination file without the
entries of LABEL... (kevm.sh, TARGET=evm: the functions that only KEVM's driver uses, which the
compiled `EVM` module does not generate; `gen` names them when it refuses the file)."""
import re, sys
src, out, drop = sys.argv[1], sys.argv[2], set(sys.argv[3:])
parts = re.split(r'(?m)^(?=\[functions\.)', open(src).read())
keep = [parts[0]] + [p for p in parts[1:] if re.match(r'\[functions\."(.*)"\]', p).group(1) not in drop]
open(out, "w").write("".join(keep))
print(f"{len(keep) - 1} of {len(parts) - 1} entries")
