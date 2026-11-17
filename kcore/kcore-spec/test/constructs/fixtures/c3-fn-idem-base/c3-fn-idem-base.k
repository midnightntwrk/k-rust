module C3-FN-IDEM-BASE
  imports INT
  syntax Int ::= pm(Int, Int) [function, total, symbol(pm)]
  rule pm(A, B) => maxInt(A, B)
endmodule
