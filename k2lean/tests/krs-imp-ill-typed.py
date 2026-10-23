#!/usr/bin/env python3
"""Write the ill-typed `assign` variant of the recorded KRS IMP KORE (the gate's negative check).

usage: krs-imp-ill-typed.py IN/definition.kore OUT/definition.kore

The variant is KRS IMP with its `assign` rule changed to
`env: map::update(map::update(e, name, value), name, Block(Sequence(EmptyBlock(), EmptyBlock())))`,
which binds a variable to a statement and so breaks the declared cell type `env: Map<Id, Value>`.
This script makes that change in the KORE that `krs build` recorded for the unchanged definition
(`demos/k/krs-imp/definition.kore`): the right-hand side's `<env>` update of the rule labelled
`KRS-IMP.assign` gets a second update that binds the same name to a statement. This is the rule
term krust compiles from the changed KRS source, so the check does not depend on rebuilding KRS;
every other axiom is byte-identical.
"""
import sys

src, dst = sys.argv[1], sys.argv[2]
text = open(src).read()
label = 'label{}("KRS-IMP.assign")'
end = text.index(label)
start = text.rindex("axiom{}", 0, end)
rule = text[start:end]
old = """LblMap'Coln'update{}(
              VarE:SortMap{},
              inj{SortId{}, SortKItem{}}(VarName:SortId{}),
              inj{SortValue{}, SortKItem{}}(VarValue:SortValue{})
            )"""
new = """LblMap'Coln'update{}(
              LblMap'Coln'update{}(
                VarE:SortMap{},
                inj{SortId{}, SortKItem{}}(VarName:SortId{}),
                inj{SortValue{}, SortKItem{}}(VarValue:SortValue{})
              ),
              inj{SortId{}, SortKItem{}}(VarName:SortId{}),
              inj{SortStmt{}, SortKItem{}}(
                LblstmtSyntaxBlock{}(
                  LblstmtSyntaxSequence{}(LblstmtSyntaxEmptyBlock{}(), LblstmtSyntaxEmptyBlock{}())
                )
              )
            )"""
if rule.count(old) != 1:
    sys.exit("krs-imp-ill-typed.py: the assign rule does not have the expected <env> update")
open(dst, "w").write(text[:start] + rule.replace(old, new) + text[end:])
