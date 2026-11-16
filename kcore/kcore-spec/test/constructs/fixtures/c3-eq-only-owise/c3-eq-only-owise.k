module C3-EQ-ONLY-OWISE
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
  rule f(_) => 0 [owise]
endmodule
