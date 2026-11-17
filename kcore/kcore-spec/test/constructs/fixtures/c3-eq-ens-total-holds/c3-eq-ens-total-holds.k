module C3-EQ-ENS-TOTAL-HOLDS
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, total, symbol(f)]
  rule f(X) => X ensures X ==Int X
endmodule
