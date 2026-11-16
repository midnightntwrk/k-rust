module E2-COMM-RULE
  syntax Exp ::= a(Exp, Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X, _) => X ... </k> [comm]
endmodule
