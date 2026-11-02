#!/usr/bin/env python3
"""Write a mutant of one side of a `k2lean refine` demonstration, for its refutation by two runs.

usage: refine-mutant.py MODE IN OUT

Modes:
- `imp-le`: IN and OUT are directories of kimp's sources (`imp.k`, `calc.k`, `expr.k`); OUT gets
  them all, with `<=` read as `<` in `expr.k` (an off-by-one). With `tests/kimp-unroll.py`'s
  `while` applied to OUT's `imp.k`, it is the other side of `demos/ImpUnrollMut`, against kimp.
- `vm-pop-skip`: IN and OUT are files; the fixture `vmpop1`'s `pop` on an empty stack does nothing
  instead of halting with `underflow`. It is the other side of `demos/VmPopMut`, against `vmpop`.

Each mutated rule has no counterpart on the other side, so `refine` lists its parts open, and a
program on which the two sides disagree refutes them (`refine --witnesses`, `docs/design.md`,
section 3.5). The script fails if a source does not contain exactly the text it rewrites.
"""
import os
import shutil
import sys

mode, src, dst = sys.argv[1], sys.argv[2], sys.argv[3]


def rewrite(path_in, path_out, old, new):
    text = open(path_in).read()
    if text.count(old) != 1:
        sys.exit(f"refine-mutant.py: expected exactly one occurrence of {old!r} in {path_in}")
    open(path_out, "w").write(text.replace(old, new))


if mode == "imp-le":
    os.makedirs(dst, exist_ok=True)
    for f in ("imp.k", "calc.k", "expr.k"):
        shutil.copyfile(os.path.join(src, f), os.path.join(dst, f))
    rewrite(os.path.join(src, "expr.k"), os.path.join(dst, "expr.k"),
            "rule I1 <= I2 => I1 <=Int I2", "rule I1 <= I2 => I1 <Int I2")
elif mode == "vm-pop-skip":
    rewrite(src, dst,
            "rule <k> pop => #halt(underflow) ... </k> [label(pop-underflow), owise]",
            "rule <k> pop => .K ... </k> [label(pop-underflow), owise]")
else:
    sys.exit(f"refine-mutant.py: unknown mode {mode!r} (imp-le, vm-pop-skip)")
