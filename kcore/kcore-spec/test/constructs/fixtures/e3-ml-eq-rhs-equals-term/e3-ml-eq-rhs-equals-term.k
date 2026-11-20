module E3-ML-EQ-RHS-EQUALS-TERM
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)] | h(Int) [function, symbol(h)]
  rule f(X) => X requires X >Int 0
  rule h(X) => X #And {f(X) #Equals X}
endmodule
