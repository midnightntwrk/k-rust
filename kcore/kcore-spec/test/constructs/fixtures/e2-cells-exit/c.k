module C
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <one> 0 </one> <ec exit=""> 0 </ec> </t>
endmodule
