// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, hooked
// to BOOL.and, in a definition that does not import K-EQUAL.
module RDR-ITE-OWN-HOOKAND
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite), hook(BOOL.and)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule f(X) => pick(false, X, b)
endmodule
