// A sort-parametric function of the text whose symbol is named ite, at one sort parameter, in a
// definition that does not import K-EQUAL, applied at a sort of the user's file hooked as
// KVAR-SYNTAX hooks KVar (`[token, hook(KVAR.KVar)]`): a sort the reading does not have.
module RDR-ITE-OWN-HOOKED-SORT
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite)]
  syntax Name [token, hook(KVAR.KVar)]
  syntax Foo ::= "a" [symbol(a)] | f(Name) [function, symbol(f)] | g(Name) [symbol(g)]
  rule f(X) => g(pick(false, X, X))
endmodule
