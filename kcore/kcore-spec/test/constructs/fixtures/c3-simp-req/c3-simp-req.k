module C3-SIMP-REQ
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) requires X >Int 0 [simplification]
endmodule
