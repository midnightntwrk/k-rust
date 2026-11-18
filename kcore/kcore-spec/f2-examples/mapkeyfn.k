module E3-MAP-KEY-FN
  imports INT
  imports MAP
  syntax Int ::= key(Int) [function, total, symbol(key)]
  rule key(X) => X +Int 1
  syntax Exp ::= get(Int) [symbol(get)]
  configuration <k> $PGM:Exp </k> <m> .Map </m>
  rule <k> get(X) => V ... </k> <m> key(X) |-> V ... </m>
endmodule
