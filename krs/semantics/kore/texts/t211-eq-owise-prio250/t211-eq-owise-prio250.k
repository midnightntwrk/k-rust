// A function equation of priority 250 beside an [owise] equation.
module T211-EQ-OWISE-PRIO250
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(250)]
  rule f(_) => 0 [owise]
endmodule
