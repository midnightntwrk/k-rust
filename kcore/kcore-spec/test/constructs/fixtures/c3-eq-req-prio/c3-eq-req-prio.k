module C3-EQ-REQ-PRIO
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X requires X >Int 0 [priority(40)]
endmodule
