#!/usr/bin/env python3
"""Write a mutant of one side of a `k2lean refine` demonstration, for its refutation by two runs.

usage: refine-mutant.py MODE IN OUT

Modes:
- `imp-le`: IN and OUT are directories of kimp's sources (`imp.k`, `calc.k`, `expr.k`); OUT gets
  them all, with `<=` read as `<` in `expr.k` (an off-by-one). With `tests/kimp-unroll.py`'s
  `while` applied to OUT's `imp.k`, it is the other side of `demos/ImpUnrollMut`, against kimp.
- `vm-pop-skip`: IN and OUT are files; the fixture `vmpop1`'s `pop` on an empty stack does nothing
  instead of halting with `underflow`. It is the other side of `demos/VmPopMut`, against `vmpop`.
- `vm-empty`: IN and OUT are files; the fixture `vmpri` with a cell `<empty>` that caches whether
  the stack is empty, kept by every rule that changes the stack (`pop` writes `isEmpty` of what is
  left), and the invariant `emptyOk` (the cache is right, `gen --invariant
  emptyOk@T`). The first side of `demos/VmEmptyRefine`.
- `vm-empty-opt`: `vm-empty` whose underflow rules on an empty stack read the cache instead of the
  stack: the other side of `demos/VmEmptyRefine`, an optimization that holds only where the cache
  is right, so `refine` relates the two under the invariant (`--assume-invariant`).
- `vm-empty-stale`: `vm-empty-opt` whose `pop` leaves the cache as it was: a wrong
  optimization, the other side of `demos/VmEmptyMut`, which a program refutes under the invariant
  (`push(1); pop; pop` underflows against getting stuck).
- `vm-guard`: IN and OUT are files; the fixture `vmpri` whose `pop` holds a guard that always holds
  (`requires X ==Int X`): `pop` has no counterpart, but a namesake, so its parts and the priority
  lemmas of `pop-underflow` (its `owise` rule) are attempted generically (REL-10), with no legality.
  The other side of `demos/VmGuardRefine`, against `vmpri`.
- `range-inc`: IN and OUT are files; the fixture `range` with `inc(L)`, which adds one to the value
  stored at `L` where it is nonnegative. The first side of `demos/RangeIncRefine`.
- `range-inc-opt`: `range-inc` without the check, which the fixture's invariant (`storeNat`, every
  stored value is a nonnegative integer) makes redundant: the other side of `demos/RangeIncRefine`.

In the mutants, each mutated rule has no counterpart on the other side, so `refine` lists its parts open, and a
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
elif mode in ("vm-empty", "vm-empty-opt", "vm-empty-stale"):
    text = open(src).read()
    edits = [
        ("<stack> .Stack </stack> </T>", "<stack> .Stack </stack> <empty> true </empty> </T>"),
        ("<stack> S => I : S </stack> [label(push)]",
         "<stack> S => I : S </stack> <empty> _ => false </empty> [label(push)]"),
        ("rule <k> pop => .K ... </k> <stack> _ : S => S </stack> [label(pop)]",
         "rule <k> pop => .K ... </k> <stack> _ : S => S </stack> <empty> _ => isEmpty(S) </empty>"
         " [label(pop)]"),
        ("  rule halted(_) => false [owise]\n", """  rule halted(_) => false [owise]
  // the cache is right: `<empty>` says whether the stack is empty
  syntax Bool ::= isEmpty(Stack) [function, total]
                | emptyOk(TCell) [function, total]
  rule isEmpty(.Stack) => true
  rule isEmpty(_ : _) => false
  rule emptyOk(<T> <k> _ </k> <stack> S </stack> <empty> E </empty> </T>) => E ==Bool isEmpty(S)
"""),
    ]
    if mode == "vm-empty-stale":
        edits[2] = (edits[2][0], edits[2][1].replace(" <empty> _ => isEmpty(S) </empty>", ""))
    if mode in ("vm-empty-opt", "vm-empty-stale"):
        edits += [
            ("<k> add => #halt(underflow) ... </k> <stack> .Stack </stack>",
             "<k> add => #halt(underflow) ... </k> <empty> true </empty>"),
            ("<k> div => #halt(underflow) ... </k> <stack> .Stack </stack>",
             "<k> div => #halt(underflow) ... </k> <empty> true </empty>"),
            ("rule <k> pop => #halt(underflow) ... </k> [label(pop-underflow), owise]",
             "rule <k> pop => #halt(underflow) ... </k> <empty> true </empty> [label(pop-underflow), owise]"),
        ]
    for old, new in edits:
        if text.count(old) != 1:
            sys.exit(f"refine-mutant.py: expected exactly one occurrence of {old!r} in {src}")
        text = text.replace(old, new)
    open(dst, "w").write(text)
elif mode == "vm-guard":
    text = open(src).read()
    old = "rule <k> pop => .K ... </k> <stack> _ : S => S </stack> [label(pop)]"
    if text.count(old) != 1:
        sys.exit(f"refine-mutant.py: expected exactly one occurrence of {old!r} in {src}")
    text = text.replace(
        old, "rule <k> pop => .K ... </k> <stack> X : S => S </stack> requires X ==Int X [label(pop)]")
    open(dst, "w").write(text)
elif mode in ("range-inc", "range-inc-opt"):
    text = open(src).read()
    check = " requires V >=Int 0" if mode == "range-inc" else ""
    edits = [
        ("               | seq(Cmd, Cmd)\n",
         "               | seq(Cmd, Cmd)\n               | inc(Int)       // add one to the value at L\n"),
        ("    requires V >=Int 0 [label(set)]\n",
         "    requires V >=Int 0 [label(set)]\n"
         "  rule <k> inc(L) => .K ... </k>\n"
         "       <store> ... L |-> (V:Int => V +Int 1) ... </store>\n"
         f"   {check} [label(inc)]\n"),
    ]
    for old, new in edits:
        if text.count(old) != 1:
            sys.exit(f"refine-mutant.py: expected exactly one occurrence of {old!r} in {src}")
        text = text.replace(old, new)
    open(dst, "w").write(text)
else:
    sys.exit(f"refine-mutant.py: unknown mode {mode!r} (imp-le, vm-pop-skip, vm-empty, vm-empty-opt, vm-empty-stale, vm-guard, range-inc, range-inc-opt)")
