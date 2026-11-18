// A sort-parametric function of the text whose symbol is named ite, at two sort parameters.
module RDR-ITE-TWO
  imports BOOL
  syntax {S1, S2} S2 ::= cast(S1) [function, symbol(ite)]
  syntax Foo ::= "a" [symbol(a)] | f(Foo) [function, symbol(f)]
  rule f(X) => cast(X)
endmodule
