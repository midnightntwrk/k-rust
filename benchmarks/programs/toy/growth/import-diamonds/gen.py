# Usage: gen.py D
# Prints D import diamonds stacked above module MAIN and a module TOP importing the last one,
# to be appended to the compiled main.k definition. Every module holds the same axioms whatever
# D is; only the number of import paths from TOP to MAIN (2^D) grows.
import sys
d = int(sys.argv[1])
prev = "MAIN"
for i in range(1, d + 1):
    sys.stdout.write("module L%dA\n  import %s []\nendmodule []\nmodule L%dB\n  import %s []\nendmodule []\n" % (i, prev, i, prev))
    sys.stdout.write("module L%d\n  import L%dA []\n  import L%dB []\nendmodule []\n" % (i, i, i))
    prev = "L%d" % i
sys.stdout.write("module TOP\n  import %s []\nendmodule []\n" % prev)
