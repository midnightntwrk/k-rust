module E2-CELLS-BAG
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <bs> <bt multiplicity="*" type="Bag"> 0 </bt> </bs> </t>
endmodule
