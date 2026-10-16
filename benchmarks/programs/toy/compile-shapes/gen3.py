import sys
shape, n = sys.argv[1], int(sys.argv[2])
base = '''module MAIN-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax KItem ::= a() [symbol(a)] | g(Int) [symbol(g)] | st(String) [symbol(st)]
  syntax Int ::= f(Int) [function, symbol(f)]
endmodule
'''
main_head = '''module MAIN
  imports MAIN-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:K </k>
'''
out = []
if shape == "modchain":
    out.append(base)
    out.append("module M0\n  imports MAIN-SYNTAX\nendmodule\n")
    for i in range(1, n):
        out.append("module M%d\n  imports M%d\nendmodule\n" % (i, i - 1))
    out.append(main_head.replace("imports MAIN-SYNTAX", "imports M%d" % (n - 1)) + "endmodule\n")
elif shape == "subsorts":
    s = base.replace("endmodule\n", "") + "  syntax S0 ::= \"s0\" [symbol(s0)]\n"
    for i in range(1, n):
        s += "  syntax S%d ::= S%d\n" % (i, i - 1)
    s += "  syntax KItem ::= S%d\nendmodule\n" % (n - 1)
    out.append(s + main_head + "endmodule\n")
elif shape == "owise":
    out.append(base + main_head + "".join("  rule f(%d) => %d\n" % (i, i) for i in range(n)) + "  rule f(_) => 0 [owise]\nendmodule\n")
elif shape == "arity":
    s = base.replace("endmodule\n", "") + "  syntax Int ::= h(" + ", ".join("Int" for _ in range(n)) + ") [function, symbol(h)]\nendmodule\n"
    out.append(s + main_head + "  rule h(" + ", ".join("X%d" % i for i in range(n)) + ") => X0\nendmodule\n")
elif shape == "kseq":
    out.append(base + main_head + "  rule g(0) => " + " ~> ".join("a()" for _ in range(n)) + "\nendmodule\n")
elif shape == "cells":
    out.append(base + "module MAIN\n  imports MAIN-SYNTAX\n  imports INT\n  configuration <k> $PGM:K </k> " + " ".join("<c%d> 0 </c%d>" % (i, i) for i in range(n)) + "\n  rule <k> g(X) => .K ... </k> <c0> _ => X </c0>\nendmodule\n")
elif shape == "nestcells":
    out.append(base + "module MAIN\n  imports MAIN-SYNTAX\n  imports INT\n  configuration <k> $PGM:K </k> " + "".join("<c%d> " % i for i in range(n)) + "0" + "".join(" </c%d>" % i for i in reversed(range(n))) + "\nendmodule\n")
elif shape == "token":
    out.append(base + main_head + '  rule g(0) => st("' + "a" * n + '")\nendmodule\n')
if shape == "cfgdeep":
    out.append(base.replace("endmodule\n", "") + "  syntax N ::= \"nz\" [symbol(nz)] | s(N) [symbol(s)]\n  syntax KItem ::= w(N) [symbol(w)]\nendmodule\n" + "module MAIN\n  imports MAIN-SYNTAX\n  imports INT\n  configuration <k> $PGM:K </k> <c> " + "s(" * n + "nz" + ")" * n + " </c>\nendmodule\n")
if shape == "unary":
    out.append(base.replace("endmodule\n", "") + "  syntax N ::= \"nz\" [symbol(nz)] | s(N) [symbol(s)]\n  syntax KItem ::= w(N) [symbol(w)]\nendmodule\n" + main_head + "  rule g(0) => w(" + "s(" * n + "nz" + ")" * n + ")\nendmodule\n")
if shape == "cfglist":
    out.append(base + "module MAIN\n  imports MAIN-SYNTAX\n  imports INT\n  imports LIST\n  configuration <k> $PGM:K </k> <c> " + " ".join("ListItem(%d)" % i for i in range(n)) + " </c>\nendmodule\n")
if shape == "rulelist":
    out.append(base.replace("imports STRING-SYNTAX\n", "imports STRING-SYNTAX\n  imports LIST\n").replace("endmodule\n", "") + "  syntax KItem ::= l(List) [symbol(l)]\nendmodule\nmodule MAIN\n  imports MAIN-SYNTAX\n  imports INT\n  imports LIST\n  configuration <k> $PGM:K </k>\n  rule g(0) => l(" + " ".join("ListItem(%d)" % i for i in range(n)) + ")\nendmodule\n")
print("".join(out))
