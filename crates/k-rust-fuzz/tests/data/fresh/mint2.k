// G-MINT-VISIBLE mutant: a second one-name step mints another value into <b>.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= "again"
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> </T>
  rule [mk]: <k> mk(_) => again ... </k> <a> _ => !_A:Int </a>
  rule [again]: <k> again => .K ... </k> <b> _ => !_B:Int </b>
endmodule
