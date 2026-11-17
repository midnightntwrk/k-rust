module T11-EQ-APPLIES
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 10
  rule f(X) => 20 requires X >Int 5
endmodule
