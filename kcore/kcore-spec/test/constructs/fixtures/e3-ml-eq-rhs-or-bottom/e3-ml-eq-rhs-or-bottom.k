module E3-ML-EQ-RHS-OR-BOTTOM
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X #Or #Bottom
endmodule
