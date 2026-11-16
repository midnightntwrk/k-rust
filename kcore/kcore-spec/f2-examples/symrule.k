module E2-SYMBOLIC-RULE
  syntax Exp ::= a(Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X) => X ... </k> [symbolic]
endmodule
