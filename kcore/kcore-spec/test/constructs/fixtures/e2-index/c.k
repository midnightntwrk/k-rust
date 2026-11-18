module C
  imports INT
  syntax Exp ::= a() [symbol(a), index(0)]
  configuration <t> <k> $PGM:Exp </k> <one> 0 </one> <ec> 0 </ec> </t>
endmodule
