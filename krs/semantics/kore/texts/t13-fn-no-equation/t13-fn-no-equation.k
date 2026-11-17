module T13-FN-NO-EQUATION
  imports INT
  syntax Int ::= g(Int) [function, symbol(g)]
  rule g(0) => 1
endmodule
