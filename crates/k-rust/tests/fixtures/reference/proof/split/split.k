module SPLIT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= start(Int) | "good" | "bad" | "a" | "b" | "c" | "d" | "t1" | "t2" | "t3"
endmodule

module SPLIT
  imports SPLIT-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  rule <k> start(I) => good ... </k> requires I >Int 0
  rule <k> start(I) => bad ... </k> requires I <=Int 0
  rule <k> a => b ... </k>
  rule <k> b => c ... </k>
  rule <k> t1 => t2 ... </k> ensures false
endmodule
