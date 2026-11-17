module C3-SIMP-KRES-REQ
  imports INT
  imports BOOL
  syntax KResult ::= Int
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(f(X)) => f(X) requires X >Int 0 [simplification]
endmodule
