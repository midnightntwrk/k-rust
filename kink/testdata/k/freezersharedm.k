// The mutant of freezershared.k (PJ-35, U35b review): `+` made `strict`. Its first position's
// context and the written `context HOLE + _` share a freezer hint, so k-rust numbers them by
// content, and the freezer names of that hint denote other contexts than in freezershared.k.
module FREEZERSHAREDM-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp          [strict, symbol(plus)]
               | Exp "-" Exp          [strict, symbol(minus)]
endmodule

module FREEZERSHAREDM
  imports FREEZERSHAREDM-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  context HOLE + _
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
