module NONEB
  syntax Bar ::= bar() [symbol(bar)]
  syntax Baz ::= baz(Bar) [symbol(baz)]
  configuration <top> <k> $PGM:Baz </k> <aux> .K </aux> </top>
  rule <k> baz(B) => .K </k> <aux> _ => baz(B) </aux>
endmodule
