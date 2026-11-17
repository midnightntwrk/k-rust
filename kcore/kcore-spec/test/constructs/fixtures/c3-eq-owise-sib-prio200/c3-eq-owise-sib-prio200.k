module C3-EQ-OWISE-SIB-PRIO200
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [priority(200)]
  rule f(_) => 0 [owise]
endmodule
