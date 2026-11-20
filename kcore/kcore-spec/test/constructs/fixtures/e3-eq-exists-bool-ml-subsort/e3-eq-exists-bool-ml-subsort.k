module E3-EQ-EXISTS-BOOL-ML-SUBSORT
  imports BOOL
  syntax Foo ::= "foo" [symbol(foo)]
  syntax Bool ::= Foo
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => #Exists B:Bool. (B #And {B #Equals notBool X})
endmodule
