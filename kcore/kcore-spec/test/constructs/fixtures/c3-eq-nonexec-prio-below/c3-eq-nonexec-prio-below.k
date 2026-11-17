module C3-EQ-NONEXEC-PRIO-BELOW
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0 [non-executable, priority(40)]
  rule f(X) => X
endmodule
