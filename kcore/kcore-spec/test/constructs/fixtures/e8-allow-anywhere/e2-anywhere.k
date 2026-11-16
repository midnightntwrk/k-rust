module E2-ANYWHERE
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  rule a(X) => b(X) [anywhere]
endmodule
