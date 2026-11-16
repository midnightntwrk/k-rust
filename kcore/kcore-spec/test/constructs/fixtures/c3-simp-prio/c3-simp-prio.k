module C3-SIMP-PRIO
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) [simplification]
endmodule
