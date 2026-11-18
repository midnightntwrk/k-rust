// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, in a
// definition that does not import K-EQUAL: the text states an equation of its instance at Foo.
module RDR-ITE-OWN-EQ
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule pick(true, X:Foo, _:Foo) => X
  rule f(X) => pick(false, X, b)
endmodule
