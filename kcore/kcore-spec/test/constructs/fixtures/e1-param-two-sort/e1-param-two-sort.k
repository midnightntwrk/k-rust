// A symbol with two sort parameters, `syntax {S, T} Bool ::= same(S, T)`, whose rule becomes an
// equation of the one instance Lblsame{SortK{}, SortK{}}, and a rule applying another instance,
// Lblsame{SortInt{}, SortExp{}}, of which the text states no equation.
// fixture.toml params records `kcore sem-fields`'s parameter lines.
module E1-PARAM-TWO-SORT
  imports INT
  imports BOOL
  syntax {S, T} Bool ::= same(S, T) [function, symbol(same)]
  syntax Exp ::= a(Int) [symbol(a)] | b(Bool) [symbol(b)]
  rule same(_, _) => true
  rule <k> a(X) => b(same(X, a(X))) ... </k>
endmodule
