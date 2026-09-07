module BR-SYNTAX
  syntax Pgm ::= "a" | "b" | "c" | "d" | "e"
endmodule
module BR
  imports BR-SYNTAX
  configuration <k> $PGM:Pgm </k>
  rule <k> a => b ... </k>
  rule <k> a => c ... </k>
  rule <k> b => d ... </k>
  rule <k> c => d ... </k>
  rule <k> d => e ... </k>
endmodule
