module E2-SYNTACTIC-RULE
  syntax Exp ::= a(Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X) => X ... </k> [syntactic(1)]
endmodule
