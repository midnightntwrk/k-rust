module E3-ML-RULE-LHS-OR
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> d(X, a()) #Or d(a(), X) => X ... </k>
endmodule
