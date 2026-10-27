// FZ-FRESH fix round (review S1) baseline: rb1.k's configuration, one end <r> 8 <s> 7, no fresh
// value.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <r> 7 </r> <s> 7 </s> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <r> _ => 8 </r>
endmodule
