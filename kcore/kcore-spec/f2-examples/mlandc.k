module E3-ML-RULE-RHS-AND-CTOR
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(X) => X #And a() ... </k>
endmodule
