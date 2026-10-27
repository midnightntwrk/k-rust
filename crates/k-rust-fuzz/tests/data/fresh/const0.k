// G-FRESH-FOR-CONSTANT boundary baseline: <a> gets the constant 0, the value mint.k mints.
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
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => 0 </a>
endmodule
