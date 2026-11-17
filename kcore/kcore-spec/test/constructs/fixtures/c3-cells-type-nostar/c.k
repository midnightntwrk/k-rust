module C
  imports INT
  imports SET
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <bs> <bt type="Set"> 0 </bt> </bs> </t>
endmodule
