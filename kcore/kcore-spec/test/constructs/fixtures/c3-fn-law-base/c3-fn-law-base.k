module C3-FN-LAW-BASE
  imports INT
  syntax Int ::= pl(Int, Int) [function, total, symbol(pl)]
  rule pl(A, B) => A +Int B
endmodule
