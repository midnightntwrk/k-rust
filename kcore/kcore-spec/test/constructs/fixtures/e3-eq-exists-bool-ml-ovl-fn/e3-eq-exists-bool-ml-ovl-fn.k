module E3-EQ-EXISTS-BOOL-ML-OVL-FN
  imports BOOL
  syntax Exp ::= Bool | neg(Exp) [symbol(negExp), overload(neg)]
  syntax Bool ::= neg(Bool) [function, total, symbol(negBool), overload(neg)]
  rule neg(B:Bool) => notBool B
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
