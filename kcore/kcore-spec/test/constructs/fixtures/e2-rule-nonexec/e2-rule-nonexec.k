module E2-RULE-NONEXEC
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | c(Int) [symbol(c)]
  rule <k> c(X) => a(X) ... </k> [non-executable]
endmodule
