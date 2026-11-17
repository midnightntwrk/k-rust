// Two overloaded function productions: neg at Exp and neg at Int, the second total.
module T196-OVERLOAD-FN
  imports INT
  syntax Exp ::= Int | "e" [symbol(e)]
  syntax Exp ::= neg(Exp) [function, symbol(negExp), overload(neg)]
  syntax Int ::= neg(Int) [function, total, symbol(negInt), overload(neg)]
  rule neg(I:Int) => 0 -Int I
  rule neg(e) => e
endmodule
