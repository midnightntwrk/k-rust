module E3-EQ-EXISTS-ML-AND-RIGHT
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(X) => (notBool X) #And (#Exists B:Bool. (B #And {B #Equals X}))
endmodule
