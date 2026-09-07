module CO-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= f(Int) | g(Int) | h(Int)
endmodule
module CO
  imports CO-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> f(N) => g(N) ... </k> [concrete]
  rule <k> g(N) => h(N) ... </k> [symbolic]
endmodule
