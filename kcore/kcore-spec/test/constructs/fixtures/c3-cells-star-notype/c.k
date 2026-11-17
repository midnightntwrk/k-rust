module C
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <bs> <bt multiplicity="*"> 0 </bt> </bs> </t>
endmodule
