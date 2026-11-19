module E3-ML-RULE-LHS-AND-PATS
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(d(X, _) #And d(_, b())) => X ... </k>
endmodule
