module E3-EQ-EXISTS-BOOL-PARTIAL
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(X) => ?B ensures ?B ==Bool notBool X
endmodule
