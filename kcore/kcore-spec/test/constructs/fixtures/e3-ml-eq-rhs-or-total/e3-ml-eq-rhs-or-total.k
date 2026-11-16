module E3-ML-EQ-RHS-OR-TOTAL
  imports INT
  syntax Int ::= f(Int) [function, total, symbol(f)] | g(Int) [function, total, symbol(g)] | h(Int) [function, total, symbol(h)]
  rule f(X) => X
  rule g(X) => 0 -Int X
  rule h(X) => f(X) #Or g(X)
endmodule
