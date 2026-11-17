module C3-EQ-OWISE-SIB-NONEXEC-PRIO250
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [non-executable, priority(250)]
  rule f(_) => 0 [owise]
endmodule
