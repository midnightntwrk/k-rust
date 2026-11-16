module E2-SIMP-ON-RULE
  syntax Exp ::= a(Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X) => X ... </k> [simplification]
endmodule
