// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, hooked
// to KEQUAL.ite, in a definition that does not import K-EQUAL.
module RDR-ITE-OWN-HOOK
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite), hook(KEQUAL.ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule f(X) => pick(false, X, b)
endmodule
