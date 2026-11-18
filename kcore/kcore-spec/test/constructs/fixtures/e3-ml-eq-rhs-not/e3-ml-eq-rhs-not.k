module E3-ML-EQ-RHS-NOT
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)]
  rule g(X) => X
  rule f(X) => #Not(g(X))
endmodule
