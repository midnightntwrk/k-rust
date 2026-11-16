module E3-REQENS
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)] | c(Int) [symbol(c)] | d(Int) [symbol(d)]
  rule <k> a(X) => b(X) ... </k> requires X >Int 0
  rule <k> b(X) => c(X) ... </k> ensures X >Int 0
  rule <k> c(X) => d(X) ... </k> requires X >Int 0 ensures X >Int 1
endmodule
