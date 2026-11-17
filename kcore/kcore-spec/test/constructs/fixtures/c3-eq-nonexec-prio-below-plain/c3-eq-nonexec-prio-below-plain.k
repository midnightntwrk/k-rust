module C3-EQ-NONEXEC-PRIO-BELOW-PLAIN
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0 [priority(40)]
  rule f(X) => X
endmodule
