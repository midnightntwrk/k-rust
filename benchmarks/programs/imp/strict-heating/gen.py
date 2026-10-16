# Usage: gen.py two|one K
# Prints a straight-line IMP program (imp-llvm/imp.k syntax): `int a, s; a = 1;` then K copies of
#   two: `s = s + a;`  both `+` operands are unevaluated identifiers, so `+` has two heating orders
#   one: `s = s + 1;`  one unevaluated operand, one heating order (the control)
# Either way the final state binds s to K.
import sys
shape, k = sys.argv[1], int(sys.argv[2])
line = "s = s + a;" if shape == "two" else "s = s + 1;"
print("int a, s;\na = 1;\n" + "\n".join([line] * k))
