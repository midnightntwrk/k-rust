module C3-EQ-PDEF
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [preserves-definedness]
endmodule
