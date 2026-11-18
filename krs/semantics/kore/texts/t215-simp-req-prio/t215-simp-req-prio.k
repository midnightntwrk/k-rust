// A simplification with a requires beside an equation of priority 40.
module T215-SIMP-REQ-PRIO
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) requires X >Int 0 [simplification]
endmodule
