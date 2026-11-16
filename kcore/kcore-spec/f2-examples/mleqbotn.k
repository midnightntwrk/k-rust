module E3-ML-EQ-RHS-BOTTOM-NOVAL
  imports INT
  imports STRING
  syntax Exp ::= f(Int) [function, symbol(f)] | c(String) [symbol(c)]
  rule f(X) => #Bottom requires X <Int 0
  rule f(X) => c("x") [owise]
endmodule
