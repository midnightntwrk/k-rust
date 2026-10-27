// FZ-FRESH fix round (review S1) baseline: the constants <a> 1 <b> 0, the end base.k's rule has
// under the numbering k-rust does not choose.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => 1 </a> <b> _ => 0 </b>
endmodule
