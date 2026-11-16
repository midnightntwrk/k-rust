module E2-FN-ASSOC-BAD
  imports INT
  syntax Int ::= pl(Int, Int) [function, total, assoc, symbol(pl)]
  rule pl(A, B) => A -Int B
endmodule
