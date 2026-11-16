module E7-REMOVEUNIT
  imports INT
  imports MAP
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  configuration <k> $PGM:Exp </k> <m> .Map </m>
  rule <k> a() => b() ... </k> <m> M => (1 |-> 2) M .Map </m>
endmodule
