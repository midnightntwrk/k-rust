# Usage: gen.py amb|ctl N
# amb: 0 + 1 + ... + (N-4) + 1 - 2 - 3, a chain whose `+` and `-` have no relation (ambiguous).
# ctl: 0 + 1 + ... + (N-1), the unambiguous all-`+` chain of N operands.
import sys
shape, n = sys.argv[1], int(sys.argv[2])
if shape == "amb":
    print(" + ".join(str(i) for i in range(n - 3)) + " + 1 - 2 - 3")
else:
    print(" + ".join(str(i) for i in range(n)))
