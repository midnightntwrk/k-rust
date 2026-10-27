// FZ-FRESH fix round (review B1) mutant: lit.k's rule with its cells <a> and <b> in the other
// order, the same K rule.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <c> 2 </c> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <c> 2 </c> <b> _ => !_B:Int </b> <a> _ => !_A:Int </a>
endmodule
