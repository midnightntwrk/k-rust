// A sort-parametric function of the text whose symbol is named ite, at two sort parameters, with
// an equation of its instance at Foo, Foo.
module RDR-ITE-TWO-EQ
  imports BOOL
  syntax {S1, S2} S2 ::= cast(S1) [function, symbol(ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule cast(a) => b
  rule f(X) => cast(X)
endmodule
