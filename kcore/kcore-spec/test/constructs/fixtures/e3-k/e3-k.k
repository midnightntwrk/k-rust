module E3-K
  imports INT
  imports BOOL
  syntax Exp ::= a(Int) [symbol(a)] | b(Exp) [symbol(b)] | c(Int) [symbol(c)] | d(Int) [symbol(d)]
  rule <k> b(a(_) #as E) => E ... </k>
  rule <k> c(X) => #fun(Y => Y +Int 1)(X) ... </k>
  rule <k> d(X) => #let Y = X +Int 1 #in a(Y) ... </k>
endmodule
