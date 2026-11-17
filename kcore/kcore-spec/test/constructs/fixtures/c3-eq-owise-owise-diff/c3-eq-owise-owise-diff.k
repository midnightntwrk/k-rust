module C3-EQ-OWISE-OWISE-DIFF
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0
  rule f(1) => 2 [owise]
  rule f(_) => 1 [owise]
endmodule
