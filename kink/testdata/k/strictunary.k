// Strictness edits (PJ-35, U35b): every strict production has one nonterminal, so each context's
// freezer has no argument and the freezer values are finitely many. An edit of strictness then
// fails closed (every symbol counts as redefined), since a claim could state their number.
module STRICTUNARY-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "~" Exp              [strict, symbol(neg)]
               | "!" Exp              [symbol(not)]
endmodule

module STRICTUNARY
  imports STRICTUNARY-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  rule ~ I:Int => 0 -Int I
  rule ! I:Int => 1 -Int I
endmodule
