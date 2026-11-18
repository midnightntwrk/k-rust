module C3-SIMP-ENS-TRUE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) ensures f(X) ==Int X [simplification]
endmodule
