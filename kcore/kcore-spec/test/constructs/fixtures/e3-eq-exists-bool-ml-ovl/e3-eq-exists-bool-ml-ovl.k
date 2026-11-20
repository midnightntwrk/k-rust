module E3-EQ-EXISTS-BOOL-ML-OVL
  imports BOOL
  syntax Exp ::= Bool | neg(Exp) [symbol(negExp), overload(neg)]
  syntax Bool ::= neg(Bool) [symbol(negBool), overload(neg)]
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
