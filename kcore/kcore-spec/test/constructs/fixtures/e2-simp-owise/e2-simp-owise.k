module E2-SIMP-OWISE
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(f(X)) => f(X) [simplification, owise]
endmodule
