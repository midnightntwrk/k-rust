module E2-UNBOUND
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(X) ... </k> [unboundVariables(X)]
endmodule
