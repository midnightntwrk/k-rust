module E3-KSEQ
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c() [symbol(c)] | d() [symbol(d)]
  rule <k> a() => b() ~> c() ... </k>
  rule <k> b() => .K ... </k>
  rule <k> c() => . ... </k>
  rule <k> d() ~> X:K => (X) </k>
endmodule
