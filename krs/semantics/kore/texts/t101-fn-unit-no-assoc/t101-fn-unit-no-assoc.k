module T101-FN-UNIT-NO-ASSOC
  imports INT
  syntax Int ::= "zero" [function, total, symbol(zero)]
  syntax Int ::= pu(Int, Int) [function, total, unit(zero), symbol(pu)]
  rule zero => 0
  rule pu(A, B) => A +Int B
endmodule
