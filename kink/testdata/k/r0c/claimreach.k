// Re-pin R0c-fix-2 (a mutant drops the claims its edit leaves unbacked): the reach of an edit.
// g's equation applies f and h's condition applies g, so an edit of f's equation leaves the claims
// of f, g and h unbacked, the lemma about f, and the preserves-definedness of `use`, whose
// condition applies g. k, its lemma and `other` rest on nothing f's edit touches. `use`'s and
// `other`'s own edits (rewrite rules) remove only their own claim.
module CLAIMREACH-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "halt" [symbol(halt)] | use(Int) [symbol(use)] | other(Int) [symbol(other)]
  syntax Int ::= f(Int) [function, total, smtlib(crf), symbol(f)]
               | g(Int) [function, total, symbol(g)]
               | h(Int) [function, total, symbol(h)]
               | k(Int) [function, total, symbol(k)]
endmodule
module CLAIMREACH
  imports CLAIMREACH-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [f]: f(I) => 10 /Int (I +Int 1)
  rule [g]: g(I) => f(I) +Int 1
  rule [h]: h(I) => 0 requires g(I) >Int 100
  rule [howise]: h(_) => 1 [owise]
  rule [k]: k(I) => I *Int 2
  rule [flemma]: f(I) +Int 0 => f(I) [simplification]
  rule [klemma]: k(I) +Int 0 => k(I) [simplification]
  rule [use]: <k> use(I) => halt </k> requires g(I) >Int 0 [preserves-definedness]
  rule [other]: <k> other(I) => halt </k> requires k(I) >Int 0 [preserves-definedness]
endmodule
