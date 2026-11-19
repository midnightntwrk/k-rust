module E2-SIMP-LABEL
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule [s-label]: f(f(X)) => f(X) [simplification]
endmodule
