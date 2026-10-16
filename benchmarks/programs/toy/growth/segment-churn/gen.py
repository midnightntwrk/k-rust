# Usage: gen.py M
# Prints p(C, p(C, ... C)) with M copies of C = c^20000(a): each copy is deeper than the
# 8 MiB main stack allows for the parser's guarded recursions.
import sys
m, d = int(sys.argv[1]), 20000
chain = "c(" * d + "a" + ")" * d
t = chain
for _ in range(m - 1):
    t = "p(" + chain + ", " + t + ")"
print(t)
