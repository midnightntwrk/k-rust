// G-SHIFT mutant: mints a value and discards it, then mints the value <a> gets.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= tmp(Int) | "again"
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => tmp(!_X:Int) ... </k>
  rule [tmp]: <k> tmp(_) => again ... </k>
  rule [again]: <k> again => .K ... </k> <a> _ => !_A:Int </a>
endmodule
