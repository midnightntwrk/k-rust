module C3-EQ-ONLY-ENS
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X ensures X >=Int 0
endmodule
