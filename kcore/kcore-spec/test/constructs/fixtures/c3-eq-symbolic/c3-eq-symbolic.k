module C3-EQ-SYMBOLIC
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [symbolic]
endmodule
