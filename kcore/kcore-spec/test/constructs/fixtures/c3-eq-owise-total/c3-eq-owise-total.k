module C3-EQ-OWISE-TOTAL
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X
  rule f(_) => 0 [owise]
endmodule
