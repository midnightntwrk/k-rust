module E3-CELLS-DOTBAG
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  configuration <t> <k> $PGM:Exp </k> </t>
  rule <t> .::Bag <k> a() => b() </k> </t>
endmodule
