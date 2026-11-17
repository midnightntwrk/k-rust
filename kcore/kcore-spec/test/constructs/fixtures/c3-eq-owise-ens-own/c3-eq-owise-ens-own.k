module C3-EQ-OWISE-ENS-OWN
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 1
  rule f(X) => X ensures X >=Int 0 [owise]
endmodule
