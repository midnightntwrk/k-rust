module E3-ML-FLOOR-LHS
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule #Floor(f(X)) => #Top [simplification]
endmodule
