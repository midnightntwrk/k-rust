module E2-INIT-PARTIAL-FN
  imports INT
  syntax Pgm ::= "p" [symbol(p)]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(1) => 1
  configuration <k> $PGM:Pgm </k> <x> f(0) </x>
endmodule
