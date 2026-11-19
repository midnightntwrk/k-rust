module E3-ML-RULE-LHS-NOT-OTHER
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(#Not(a())) => b() ... </k>
endmodule
