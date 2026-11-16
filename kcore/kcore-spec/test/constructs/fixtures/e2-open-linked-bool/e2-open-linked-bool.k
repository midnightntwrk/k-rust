module E2-OPEN-LINKED-BOOL
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(#if B #then 1 #else 0 #fi) ... </k>
    requires B ==Bool (2 *Int H ==Int 1) [unboundVariables(B, H)]
endmodule
