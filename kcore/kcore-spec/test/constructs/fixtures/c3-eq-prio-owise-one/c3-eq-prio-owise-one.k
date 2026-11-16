module C3-EQ-PRIO-OWISE-ONE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [owise, priority(40)]
endmodule
