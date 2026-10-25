#!/usr/bin/env python3
"""Split a generated Rules.lean into modules, so that Lake builds the matchers in parallel and each
module has its own time and memory (kevm.sh).

usage: split-rules.py PROJECT_DIR NS [CHUNKS]

Writes NS/RulesRel.lean (header and the App/Step0/Step relations), NS/RulesM<i>.lean (the matchers
`Rules.x`, CHUNKS files, default 4), and replaces NS/Rules.lean by the rest (rule records, the
index, `step`, `run`), importing them. Adequacy.lean and later modules import NS.Rules unchanged."""
import re, sys, os
proj, ns = sys.argv[1], sys.argv[2]
chunks = int(sys.argv[3]) if len(sys.argv) > 3 else 4
p = os.path.join(proj, ns, 'Rules.lean')
src = open(p).read()
i = src.index('\nnamespace Rules\n')
j = src.index('\nend Rules\n', i)
head = src[:i]
body = src[i + len('\nnamespace Rules\n'):j]
tail = src[j + len('\nend Rules\n'):]
# header lines (imports, options, namespace, variable, open) up to the first inductive
k = head.index('\ninductive ')
pre = head[:k]
imports = [l for l in pre.splitlines() if l.startswith('import ')]
rest_pre = '\n'.join(l for l in pre.splitlines() if not l.startswith('import '))
open(os.path.join(proj, ns, 'RulesRel.lean'), 'w').write(head + f"\nend {ns}\n")
defs = re.split(r'\n(?=def «)', body)
lead, defs = (defs[0], defs[1:]) if not defs[0].startswith('def «') else ('', defs)
n = len(defs)
names = []
for c in range(chunks):
    part = defs[c * n // chunks:(c + 1) * n // chunks]
    name = f"RulesM{c + 1}"
    names.append(name)
    open(os.path.join(proj, ns, name + '.lean'), 'w').write(
        f"import {ns}.RulesRel\n{rest_pre}\nnamespace Rules\n{lead}\n" + '\n'.join(part) + f"\nend Rules\n\nend {ns}\n")
open(p, 'w').write('\n'.join(f"import {ns}.{m}" for m in names) + "\n" + rest_pre + "\n" + tail)
print(n, "matchers in", chunks, "modules")
