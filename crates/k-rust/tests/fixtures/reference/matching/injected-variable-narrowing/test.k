module TEST3
  imports INT
  syntax Exp ::= Int | bar(Int) [symbol(bar)] | baz(Exp) [symbol(baz)]
  syntax Pgm ::= Exp
  configuration <k> $PGM:Pgm </k>
  rule <k> I:Int => bar(I) </k> [label(injvar)]
endmodule
