module E2-ONE-PATH [one-path]
  imports INT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  rule <k> a() => b() ... </k>
endmodule
