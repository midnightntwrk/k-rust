// Strictness edits (PJ-35, U35b): claim removal reads a production edit that changes only its
// `strict` or `seqstrict` positions as redefining nothing, where both definitions keep a strict
// production with two or more nonterminals (its contexts' freezers have infinitely many values).
// `hybrid`, a production-level `result` and a context alias are not read so: an edit of one fails
// closed. The main module imports INT, whose hooked and `concrete` equations make an edit of
// unknown effect unsupported.
module STRICTNESS-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp          [strict, symbol(plus)]
               | Exp "-" Exp          [seqstrict, symbol(minus)]
               | Exp "&" Exp          [strict(1), symbol(and)]
               | "~" Exp              [strict, symbol(neg)]
               | pair(Exp, Exp)       [strict, hybrid, symbol(pair)]
               | Exp "*" Exp          [strict, result(Int), symbol(times)]
               | Exp "/" Exp          [strict(c), symbol(div)]
endmodule

module STRICTNESS
  imports STRICTNESS-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  context alias [c]: <k> HERE ... </k>
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int & E => E requires I1 =/=Int 0
  rule 0 & _ => 0
  rule ~ I:Int => 0 -Int I
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0
endmodule
