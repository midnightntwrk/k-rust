module E3-ML-EQ-ARG-NOT
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(#Not(0)) => 1
  rule f(0) => 0
endmodule
