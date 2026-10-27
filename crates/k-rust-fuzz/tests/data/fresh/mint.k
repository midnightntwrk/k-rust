// G-MINT-VISIBLE, G-SHIFT and G-FRESH-FOR-CONSTANT: one value minted into <a>.
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
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => !_A:Int </a>
endmodule
