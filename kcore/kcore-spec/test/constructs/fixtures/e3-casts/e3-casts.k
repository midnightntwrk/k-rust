module E3-CASTS
  imports INT
  syntax Exp ::= Int | a(K) [symbol(a)] | b(Exp) [symbol(b)] | c(KItem) [symbol(c)] | d(Exp) [symbol(d)]
  rule <k> a(X:Int) => b(X) ... </k>
  rule <k> b(X::Int) => c(X) ... </k>
  rule <k> c(X) => d({X}:>Exp) ... </k>
  rule <k> d({ X }::Exp) => a(X) ... </k>
endmodule
