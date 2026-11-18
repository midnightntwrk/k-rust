module C
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k parser="PGM, C"> $PGM:Exp </k> <one> 0 </one> <ec> 0 </ec> </t>
endmodule
