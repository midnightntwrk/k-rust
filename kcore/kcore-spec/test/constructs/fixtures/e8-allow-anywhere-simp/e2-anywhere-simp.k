module E2-ANYWHERE-SIMP
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(f(X)) => f(X) [simplification, anywhere]
endmodule
