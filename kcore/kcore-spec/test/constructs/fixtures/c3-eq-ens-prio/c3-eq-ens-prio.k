module C3-EQ-ENS-PRIO
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X ensures X >=Int 0 [priority(40)]
endmodule
