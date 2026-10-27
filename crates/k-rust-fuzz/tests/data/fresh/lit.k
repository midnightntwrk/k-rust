// FZ-FRESH fix round (review B1) baseline: base.k with a cell <c> the rule matches as the literal
// 2, the rule's counter advance, so compilation advances the counter by a variable bound to it.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <c> 2 </c> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <c> 2 </c> <a> _ => !_A:Int </a> <b> _ => !_B:Int </b>
endmodule
