module E3-ML-RULE-LHS-OR-RHS-AND
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d(Exp) [symbol(d)]
  rule <k> c(X) #Or d(X) => X #And a() ... </k>
endmodule
