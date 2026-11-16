module E3-CELLS
  imports INT
  imports MAP
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c() [symbol(c)] | e() [symbol(e)]
  configuration <t> <k> $PGM:Exp </k> <s> 0 </s> <m> .Map </m> </t>
  rule <k> a() => b() ... </k> <s> N => N +Int 1 </s>
  rule <t> <k> b() => c() </k> <s> _ </s> <m> _ </m> </t>
  rule <t> <k> c() => e() ... </k> (<s> _ </s> <m> _ </m>) </t>
  rule <t> <k> e() => a() ... </k> B:Bag </t>
  rule <t> .Bag <k> e() => a() ... </k> ... </t> [priority(60)]
endmodule
