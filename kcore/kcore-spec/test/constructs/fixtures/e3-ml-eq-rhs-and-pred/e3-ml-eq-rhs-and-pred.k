module E3-ML-EQ-RHS-AND-PRED
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X #And {(X >Int 0) #Equals true}
endmodule
