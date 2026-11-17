module E3-EQ-EXISTS-TWICE-ML
  imports BOOL
  syntax Bool ::= p(Bool) [function, symbol(p)]
  rule p(X) => #Exists B:Bool. #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
