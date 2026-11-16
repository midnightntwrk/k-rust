module E3-ML-AND-LHS
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)]
  rule f(X) => X
  rule g(X) => X
  rule f(X) #And g(X) => f(X) [simplification]
endmodule
