module E3-ML-AG
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  rule <k> a() => #AG(b()) ... </k>
  rule <k> b() => #wEF(a()) ... </k>
  rule <k> a() => #wAF(b()) ... </k> [priority(60)]
endmodule
