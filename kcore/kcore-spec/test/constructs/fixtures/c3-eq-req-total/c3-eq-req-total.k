module C3-EQ-REQ-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X requires X >Int 0
endmodule
