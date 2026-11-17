module T17-NONLINEAR
  imports INT
  syntax Int ::= same(Int, Int) [function, symbol(same)]
  rule same(X, X) => 1
  rule same(_, _) => 0 [owise]
endmodule
