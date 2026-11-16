module E3-ML-EQ-RHS-BOTTOM-CTOR
  imports INT
  syntax Exp ::= f(Int) [function, symbol(f)] | a() [symbol(a)] | c(Int) [symbol(c)]
  rule f(X) => #Bottom requires X <Int 0
  rule f(X) => a() [owise]
endmodule
