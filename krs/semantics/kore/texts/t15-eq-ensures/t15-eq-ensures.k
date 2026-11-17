module T15-EQ-ENSURES
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X ensures X >Int 0
  rule f(_) => 0 [owise]
endmodule
