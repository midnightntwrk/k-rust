module C3-EQ-PLAIN
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
endmodule
