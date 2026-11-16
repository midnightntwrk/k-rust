module E3-PARAM-CASES
  imports INT
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(pick)]
  syntax {P} Bool ::= isZeroOf(P, Int) [function, symbol(isZeroOf)]
  syntax Exp ::= a(Int) [symbol(a)] | b(Bool) [symbol(b)]
  rule pick(true, A, _) => A
  rule pick(false, _, B) => B
  rule isZeroOf(_, I) => I ==Int 0
  rule <k> a(X) => b(isZeroOf(a(X), pick(true, X, 0))) ... </k>
endmodule
