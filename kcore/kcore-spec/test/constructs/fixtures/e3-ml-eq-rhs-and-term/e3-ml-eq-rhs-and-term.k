module E3-ML-EQ-RHS-AND-TERM
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)]
  rule f(X) => X
  rule g(X) => 0 -Int X
  rule h(X) => f(X) #And g(X)
endmodule
