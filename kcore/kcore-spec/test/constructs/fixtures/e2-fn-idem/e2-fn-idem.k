module E2-FN-IDEM
  imports INT
  syntax Int ::= pm(Int, Int) [function, total, idem, symbol(pm)]
  rule pm(A, B) => maxInt(A, B)
endmodule
