# Usage: gen-wide.py W R
# Prints the synthetic program wide<W>r<R> of the KINK-16/2 measurement (W = 2, 4 or 8):
# R copies of `x = E;` where E is a balanced strict sum of W operands over a, b, c, d
# (wide2: a + b; wide4: (a + b) + (c + d); wide8: two copies of the wide4 sum).
# Every `+` has two unevaluated operands, so searched executions rejoin often.
import sys
w, r = int(sys.argv[1]), int(sys.argv[2])
expr = {2: "a + b", 4: "(a + b) + (c + d)", 8: "((a + b) + (c + d)) + ((a + b) + (c + d))"}[w]
print("// Synthetic (not kink's corpus): %d assignments of a strict sum, whose operands" % r)
print("// evaluate in any order, so state-set arrivals rejoin often.")
print("int a, b, c, d, x;\na = 1; b = 2; c = 3; d = 4;")
print("\n".join(["x = %s;" % expr] * r))
