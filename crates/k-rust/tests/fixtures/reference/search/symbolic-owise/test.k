module SY-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= f(Int) | g(Int) | h(Int) | k(Int)
endmodule
module SY
  imports SY-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> f(N) => g(N) ... </k> requires N >Int 0 [priority(40)]
  rule <k> f(N) => h(N) ... </k> requires N <Int 10 [priority(60)]
  rule <k> f(N) => k(N) ... </k> [owise]
endmodule
