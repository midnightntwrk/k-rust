// A simplification with an ensures beside an equation of priority 40.
module T217-SIMP-ENS
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(f(X)) => f(X) ensures X >=Int 0 [simplification]
endmodule
