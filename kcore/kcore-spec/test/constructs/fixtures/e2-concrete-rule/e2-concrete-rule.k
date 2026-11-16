module E2-CONCRETE-RULE
  syntax Exp ::= a(Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X) => X ... </k> [concrete]
endmodule
