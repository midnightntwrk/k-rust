module BOOLB
  imports BOOL
  syntax Bar ::= bar(Bool, Bar) [symbol(bar)] | baz() [symbol(baz)]
  configuration <top> <k> $PGM:Bar </k> <flag> true </flag> </top>
  rule <k> bar(B, X) => X </k> <flag> F => F andBool B </flag>
endmodule
