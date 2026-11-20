// Freezer names (PJ-35, U35b review): the written `context HOLE + _` heats the first operand of
// `+`, the position `strict` would add to `strict(2)`, so the two contexts share a freezer hint
// and k-rust numbers them by content. A strictness edit of `+` is then not read as redefining
// nothing, and an end holding either freezer is not compared across the two definitions.
// freezersharedm.k is the mutant, `+` made `strict`.
module FREEZERSHARED-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp          [strict(2), symbol(plus)]
               | Exp "-" Exp          [strict, symbol(minus)]
endmodule

module FREEZERSHARED
  imports FREEZERSHARED-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  context HOLE + _
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
