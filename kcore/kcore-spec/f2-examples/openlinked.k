module E2-OPEN-LINKED
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(X) ... </k> requires X ==Int 2 *Int H [unboundVariables(X, H)]
endmodule
