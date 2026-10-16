# Usage: gen4.py SHAPE N
# Prints a one-module definition whose single rule (or nesting) grows with N.
# Reconstructed from the shape descriptions of the fu-compile-scaling unit; the scratch original
# was never committed.
#   kseqrule  rule <k> foo(0) ~> foo(1) ~> ... ~> foo(N-1) => .K </k>
#   pluskseq  rule <k> 0 +Int 1 +Int ... +Int (N-1) => .K ~> foo(0) ... </k>, a `+Int` chain beside a
#             second `~>`; the compile refuses it afterwards (a function symbol on the left-hand side)
#   listlit   rule <k> foo(0, 1, ..., N-1) => .K </k> over a List{Int, ","} argument
#   inj       rule bar(z) => hn(s(s(...s(z)...))) with N levels, each level a subsort injection
import sys
shape, n = sys.argv[1], int(sys.argv[2])
head = "module MAIN\n  imports INT\n"
if shape == "kseqrule":
    body = "  syntax KItem ::= foo(Int) [symbol(foo)]\n  configuration <k> $PGM:K </k>\n"
    body += "  rule <k> " + " ~> ".join("foo(%d)" % i for i in range(n)) + " => .K </k>\n"
elif shape == "pluskseq":
    body = "  syntax KItem ::= foo(Int) [symbol(foo)]\n  configuration <k> $PGM:K </k>\n"
    body += "  rule <k> " + " +Int ".join(str(i) for i in range(n)) + " => .K ~> foo(0) ... </k>\n"
elif shape == "listlit":
    body = "  syntax Ints ::= List{Int, \",\"}\n  syntax KItem ::= foo(Ints) [symbol(foo)]\n  configuration <k> $PGM:K </k>\n"
    body += "  rule <k> foo(" + ", ".join(str(i) for i in range(n)) + ") => .K </k>\n"
elif shape == "inj":
    body = ("  syntax N ::= \"z\" [symbol(z)] | s(M) [symbol(s)]\n  syntax M ::= N\n"
            "  syntax KItem ::= bar(N) [symbol(bar)] | hn(N) [symbol(hn)]\n  configuration <k> $PGM:K </k>\n")
    body += "  rule bar(z) => hn(" + "s(" * n + "z" + ")" * n + ")\n"
else:
    sys.exit("unknown shape " + shape)
print(head + body + "endmodule")
