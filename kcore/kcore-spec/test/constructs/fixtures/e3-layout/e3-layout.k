module E3-LAYOUT
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  rule <k> a() => b() ... </k>
endmodule
