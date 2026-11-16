module E2-SYNTACTIC-EQ
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [syntactic(1)]
endmodule
