module C3-EQ-OWISE-PRIO40-SIB
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X requires X >Int 0
  rule f(_) => 0 [owise, priority(40)]
endmodule
