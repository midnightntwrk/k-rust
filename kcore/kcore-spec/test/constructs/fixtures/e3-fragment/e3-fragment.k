module E3-FRAGMENT
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <s> 0 </s> </t>
  syntax Int ::= cnt(TCellFragment) [function, symbol(cnt)]
  rule cnt(<t>-fragment _ <s> N </s> </t>-fragment) => N
endmodule
