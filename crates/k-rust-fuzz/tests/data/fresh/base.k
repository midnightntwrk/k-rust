// F-REORDER baseline (FZ-FRESH): one rule with two fresh names.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => !_A:Int </a> <b> _ => !_B:Int </b>
endmodule
