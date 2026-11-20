module E3-ML-EQ-RHS-CEIL
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)] | k(Int) [function, symbol(k)]
  rule f(X) => X requires X >Int 0
  rule g(X) => 0 -Int X requires X <Int 5
  rule h(X) => X #And #Ceil(f(X))
  rule k(X) => X #And (#Ceil(f(X)) #And #Ceil(g(X)))
endmodule
