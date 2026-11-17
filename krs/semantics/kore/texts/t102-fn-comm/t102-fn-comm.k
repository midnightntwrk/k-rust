module T102-FN-COMM
  imports INT
  syntax Int ::= pl(Int, Int) [function, total, comm, symbol(pl)]
  rule pl(A, B) => A +Int B
endmodule
