module TR-SYNTAX
  syntax Pgm ::= "a" | "b" | "c"
endmodule
module TR
  imports TR-SYNTAX
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  rule <k> a => b ... </k> ensures false
  rule <k> a => c ... </k> [owise]
endmodule
