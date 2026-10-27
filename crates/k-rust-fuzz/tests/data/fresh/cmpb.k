// F-CMP baseline: two fresh names, then a comparison of the two minted values.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= "cmp"
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> <r> false </r> </T>
  rule [mk]: <k> mk(_) => cmp ... </k> <a> _ => !_A:Int </a> <b> _ => !_B:Int </b>
  rule [cmp]: <k> cmp => .K ... </k> <a> X </a> <b> Y </b> <r> _ => X <Int Y </r>
endmodule
