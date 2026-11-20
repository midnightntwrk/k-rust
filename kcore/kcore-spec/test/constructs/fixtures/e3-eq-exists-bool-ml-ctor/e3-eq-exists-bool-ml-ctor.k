module E3-EQ-EXISTS-BOOL-ML-CTOR
  imports BOOL
  syntax Bool ::= foo() [symbol(foo)]
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
