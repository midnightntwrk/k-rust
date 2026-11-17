module T126-RULE-LHS-NOT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(#Not(a())) => a() ... </k>
endmodule
