module E3-EQ-EXISTS-ML-UNDER-APP
  imports BOOL
  syntax Bool ::= f(Bool) [function, total, symbol(f)] | g(Bool) [function, total, symbol(g)]
  rule f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))
  rule g(B) => notBool B
endmodule
