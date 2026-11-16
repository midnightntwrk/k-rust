module E3-EQ-EXISTS-ML-IN-OR
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)] | fx(Bool) [function, symbol(fx)]
  rule f(X) => X #Or (#Exists B:Bool. (B #And {B #Equals notBool X}))
  rule fx(X) => X #Or (#Exists B:Bool. (B #And {B #Equals X}))
endmodule
