// A sort-parametric function of the text whose symbol is named pick, at one sort parameter, hooked
// to KEQUAL.ite, in a definition that does not import K-EQUAL, applied at Foo.
module RDR-ITE-PICK-HOOK
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(pick), hook(KEQUAL.ite)]
  syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | f(Foo) [function, symbol(f)]
  rule f(X) => pick(false, X, b)
endmodule
