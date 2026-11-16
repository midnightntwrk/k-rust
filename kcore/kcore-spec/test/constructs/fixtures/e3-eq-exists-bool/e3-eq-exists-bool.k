module E3-EQ-EXISTS-BOOL
  imports BOOL
  syntax Bool ::= f(Bool) [function, total, symbol(f)]
  rule f(X) => ?B ensures ?B ==Bool notBool X
endmodule
