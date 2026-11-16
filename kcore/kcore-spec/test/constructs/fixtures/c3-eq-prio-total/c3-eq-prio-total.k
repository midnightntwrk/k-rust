module C3-EQ-PRIO-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X [priority(40)]
endmodule
