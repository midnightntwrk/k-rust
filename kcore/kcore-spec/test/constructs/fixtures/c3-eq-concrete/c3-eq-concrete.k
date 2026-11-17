module C3-EQ-CONCRETE
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [concrete]
endmodule
