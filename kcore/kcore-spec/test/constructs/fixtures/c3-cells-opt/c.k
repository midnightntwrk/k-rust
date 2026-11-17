module C
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <one multiplicity="?"> 0 </one> <ec> 0 </ec> </t>
endmodule
