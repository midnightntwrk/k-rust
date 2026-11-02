#!/usr/bin/env python3
"""Write the fixture utxo with two cells its processes write and no rule reads, for
`k2lean confluence --threads procs --equiv`.

usage: utxo-relaxed.py UTXO_K OUT_K

Writes tests/fixtures/utxo/utxo.k with, beside the ledger, `<last>`, the process that created an
output last (`create` writes it), and `<log>`, the outputs created and spent in order (`create` and
`spend` append one). Two processes' creations and spends write both, so the configurations their
schedules reach differ there; modulo `--equiv last=any,log=perm` they commute, at two keys of the
ledger (`demos/UtxoRelConf`, `docs/design.md`, section 3.6). The script fails if the file does not
contain exactly the text it rewrites.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
edits = [
    ("  imports MAP\n", "  imports MAP\n  imports LIST\n"),
    (
        "      <ledger> .Map </ledger>\n",
        "      <ledger> .Map </ledger>\n      <last> root </last> <log> .List </log>\n",
    ),
    (
        "       <ledger> ... .Map => oid(P, N) |-> out(Q, V) ... </ledger> [label(create)]\n",
        "       <ledger> ... .Map => oid(P, N) |-> out(Q, V) ... </ledger>\n"
        "       <last> _ => P </last> <log> ... (.List => ListItem(oid(P, N))) </log> [label(create)]\n",
    ),
    (
        "       <ledger> ... I |-> out(P, _) => .Map ... </ledger> [label(spend)]\n",
        "       <ledger> ... I |-> out(P, _) => .Map ... </ledger>\n"
        "       <log> ... (.List => ListItem(I)) </log> [label(spend)]\n",
    ),
]
for old, new in edits:
    if text.count(old) != 1:
        sys.exit(f"utxo-relaxed.py: expected exactly one occurrence of {old!r}")
    text = text.replace(old, new)
open(dst, "w").write(text)
