module C3-EQ-ONLY-PRIO-PLAIN
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(40)]
  rule f(_) => 0
endmodule
