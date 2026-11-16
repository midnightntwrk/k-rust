module E2-SIMP-PRIORITY
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(f(X)) => f(X) [simplification, priority(10)]
endmodule
