// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, in a
// definition that does not import K-EQUAL: the text states no equation of it.
module RDR-ITE-OWN
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule f(X) => pick(false, X, b)
endmodule
