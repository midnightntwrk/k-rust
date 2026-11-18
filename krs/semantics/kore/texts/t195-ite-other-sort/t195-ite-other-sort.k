// The sort-parametric #if at the sort Int, where the K-EQUAL module states its equations at K only.
module T195-ITE-OTHER-SORT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a(Bool) | r(Int)
  rule <k> a(B) => r(#if B #then 1 #else 2 #fi) ... </k>
endmodule
