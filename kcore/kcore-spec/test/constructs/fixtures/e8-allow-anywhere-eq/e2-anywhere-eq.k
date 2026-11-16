module E2-ANYWHERE-EQ
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [anywhere]
endmodule
