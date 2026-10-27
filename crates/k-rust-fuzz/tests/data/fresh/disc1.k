// F-COUNTER mutant: mints one value and discards it.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= tmp(Int)
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> </T>
  rule [mk]: <k> mk(N) => tmp(!_X:Int) ... </k> <a> _ => N </a>
  rule [tmp]: <k> tmp(_) => .K ... </k>
endmodule
