module C3-EQ-OWISE-OWISE-ONE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 0
  rule f(1) => 1
  rule f(_) => 1 [owise]
endmodule
