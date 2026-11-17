module E3-ML-EQ-RHS-NOT-CEIL-AND
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int) [function, symbol(g)] | h(Int) [function, symbol(h)]
  rule f(X) => X requires X >Int 0
  rule g(X) => 0 -Int X requires X <Int 5
  rule h(X) => X #And #Not(#Ceil(f(X) #And g(X)))
endmodule
