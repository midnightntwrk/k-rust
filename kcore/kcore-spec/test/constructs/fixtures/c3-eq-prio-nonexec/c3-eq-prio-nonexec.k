module C3-EQ-PRIO-NONEXEC
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0
  rule f(X) => X [non-executable, priority(60)]
endmodule
