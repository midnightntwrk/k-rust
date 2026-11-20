module E3-EQ-EXISTS-NESTED-ML
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(X) => #Exists B:Bool. notBool(#Exists C:Bool. (C #And {C #Equals B}))
endmodule
