module T128-EQ-RHS-BOTTOM
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => #Bottom requires X <Int 0
  rule f(X) => X [owise]
endmodule
