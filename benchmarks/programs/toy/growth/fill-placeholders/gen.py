# Usage: gen.py abs|plus N
# abs: X /\ absInt^N(X) >=Int 0, whose smt-hook is a list template at every level.
# plus: X /\ (X +Int 1 ... +Int 1) >=Int 0 (N levels), whose smt-hook is an atom (the control).
import sys
shape, n = sys.argv[1], int(sys.argv[2])
t = "X:SortInt{}"
for _ in range(n):
    t = ("LblabsInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int{}(%s)" % t) if shape == "abs" \
        else ("Lbl'UndsPlus'Int'Unds'{}(%s, \\dv{SortInt{}}(\"1\"))" % t)
print("\\and{SortInt{}}(X:SortInt{}, \\equals{SortBool{}, SortInt{}}(\\dv{SortBool{}}(\"true\"), Lbl'Unds-GT-Eqls'Int'Unds'{}(%s, \\dv{SortInt{}}(\"0\"))))" % t)
