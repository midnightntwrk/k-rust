module E3-ML-RULE-LHS-AND
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp, Exp) [symbol(d)]
  rule <k> c(X #And d(_, b())) => X ... </k>
endmodule
