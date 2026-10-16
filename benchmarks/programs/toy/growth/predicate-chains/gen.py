# Generator for predicate-chains.sh: SHAPE DEPTH -> a constrained KORE pattern over the PRED definition.
import sys
shape, d = sys.argv[1], int(sys.argv[2])
S = "SortInt{}"
X = "X:SortInt{}"
f = "Lblf'LParUndsRParUnds'PRED'Unds'Int'Unds'Int{}(X:SortInt{})"
g = "Lblg'LParUndsRParUnds'PRED'Unds'Int'Unds'Int{}(X:SortInt{})"
ceil = lambda t: "\\ceil{SortInt{}, SortInt{}}(%s)" % t
floor = "\\floor{SortInt{}, SortInt{}}(%s)" % f
p = ceil(f)
opens, closes = [], []
for i in range(d):
    if shape in ("exists", "forall"):
        opens.append("\\%s{SortInt{}}(Y%d:SortInt{}, " % (shape, i)); closes.append(")")
    elif shape == "implies":
        opens.append("\\implies{SortInt{}}(%s, " % ceil(g)); closes.append(")")
    elif shape == "ornot":
        opens.append("\\or{SortInt{}}(%s, \\not{SortInt{}}(" % ceil(g)); closes.append("))")
    elif shape == "not":
        opens.append("\\not{SortInt{}}("); closes.append(")")
chain = "".join(opens) + p + "".join(reversed(closes))
sys.stdout.write("\\and{SortInt{}}(X:SortInt{}, \\and{SortInt{}}(%s, %s))\n" % (floor, chain))
