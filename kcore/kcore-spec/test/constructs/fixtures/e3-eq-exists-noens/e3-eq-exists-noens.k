module E3-EQ-EXISTS-NOENS
  imports BOOL
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(_) => ?B
endmodule
