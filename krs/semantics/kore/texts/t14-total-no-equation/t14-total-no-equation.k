module T14-TOTAL-NO-EQUATION
  imports INT
  imports BOOL
  syntax Bool ::= even(Int) [function, total, symbol(even)]
  rule even(0) => true
endmodule
