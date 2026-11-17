module E5-OVL-FN-FN-CTOR-INT
  imports INT
  syntax Exp ::= Int | "e" [symbol(e)]
  syntax Exp ::= neg(Exp) [function, symbol(negExp), overload(neg)]
  syntax Int ::= neg(Int) [symbol(negInt), overload(neg)]
  rule neg(e) => e
endmodule
