// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, in a
// definition that imports K-EQUAL, which declares K's ite.
module RDR-ITE-OWN-KEQ
  imports BOOL
  imports K-EQUAL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule f(X) => pick(false, X, b)
endmodule
