module E3-EQ-EXISTS-PARTIAL-ML
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
