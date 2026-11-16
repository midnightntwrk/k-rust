module E3-K-UNIFY
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a(X) => b(X) ... </k> requires a(X) :=K a(1)
  rule <k> b(X) => a(X) ... </k> requires a(X) :/=K a(1)
endmodule
