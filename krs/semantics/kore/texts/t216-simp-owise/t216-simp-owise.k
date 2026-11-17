// A simplification beside a function's equations, one of them [owise].
module T216-SIMP-OWISE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X requires X >Int 0
  rule f(_) => 0 [owise]
  rule f(f(X)) => f(X) [simplification]
endmodule
