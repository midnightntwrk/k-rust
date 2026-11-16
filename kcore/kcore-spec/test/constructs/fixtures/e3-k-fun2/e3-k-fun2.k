module E3-K-FUN2
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | c(Int) [symbol(c)] | b(Exp) [symbol(b)]
  rule <k> c(X) => #fun(a(Y) => Y)(a(X)) ... </k>
  rule <k> b(a(X)) => #fun(b(a(Y) => a(Y +Int 1)))(b(a(X))) ... </k>
endmodule
