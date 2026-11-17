module C3-EQ-PRIO-TOTAL-COMP
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(_) => 0
endmodule
