# Usage: gen.py N
# Prints the KORE antecedent c^N(z) over fn.k's definition (toy/growth/fn-recursion/fn.k).
import sys
n = int(sys.argv[1])
print("Lblc{}(" * n + "Lblz{}()" + ")" * n)
