module C3-SIMP-ENS
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) ensures X >=Int 0 [simplification]
endmodule
