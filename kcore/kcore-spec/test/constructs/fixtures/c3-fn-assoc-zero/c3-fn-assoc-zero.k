module C3-FN-ASSOC-ZERO
  imports INT
  syntax Int ::= "zero" [function, total, symbol(zero)]
  syntax Int ::= pu(Int, Int) [function, total, assoc, symbol(pu)]
  rule zero => 0
  rule pu(A, B) => A +Int B
endmodule
