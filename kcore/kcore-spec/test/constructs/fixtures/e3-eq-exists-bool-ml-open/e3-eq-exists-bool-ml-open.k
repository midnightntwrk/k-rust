module E3-EQ-EXISTS-BOOL-ML-OPEN
  imports BOOL
  syntax Bool ::= Bool "&&&" Bool [comm, symbol(band)]
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
