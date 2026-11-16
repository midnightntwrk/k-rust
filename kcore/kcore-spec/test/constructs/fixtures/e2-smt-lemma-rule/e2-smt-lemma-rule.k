module E2-SMT-LEMMA-RULE
  syntax Exp ::= a(Exp) [symbol(a)] | "b" [symbol(b)]
  rule <k> a(X) => X ... </k> [smt-lemma]
endmodule
