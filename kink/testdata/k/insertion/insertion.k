// Claim removal of an inserted constructor over a definition that imports the prelude (kink-patch
// tests/claims.rs `an_inserted_constructor_withdraws_what_takes_its_sort`, PJ-34 U34f). Kept out
// of testdata/k/ itself, whose files other tests walk.
//
// A constructor inserted at Val grows Val, Top above it, Wrap and Prog (constructors holding a
// Val), KItem and K, and List, Set and Map (which hold K items). Of the functions below, depth
// (over Val), topSize (over Top), unwrap (over Wrap) and count (over List) take a grown sort,
// and viaDepth reaches depth: their claims go. nat (result sort Val) and twice (over Int) keep
// theirs. depth-lemma mentions depth and goes, twice-lemma stays. note-lemma names only the
// prelude's #Equals, but quantifies over Note: it goes only when Note grows. A constructor
// inserted at Flag, which the definition puts below the prelude's IOError, is refused.
module INSERTION-SYNTAX
  imports INT-SYNTAX
  syntax Val ::= "z" [symbol(z)] | s(Val) [symbol(s)]
  syntax Top ::= Val
  syntax Wrap ::= wrap(Val) [symbol(wrap)]
  syntax Prog ::= "halt" [symbol(halt)]
                | run(Val, Prog) [symbol(run)]
                | go(Int, Prog) [symbol(go)]
  syntax Note
  syntax Flag ::= "on" [symbol(on)]
endmodule

module INSERTION
  imports INSERTION-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports LIST
  imports ML-SYNTAX
  syntax IOError ::= Flag
  configuration <k> .K </k>

  syntax Int ::= depth(Val) [function, total, symbol(depth)]
  rule depth(z) => 0
  rule depth(s(V)) => 1 +Int depth(V)
  syntax Int ::= topSize(Top) [function, total, symbol(topSize)]
  rule topSize(V:Val) => depth(V)
  syntax Int ::= unwrap(Wrap) [function, total, symbol(unwrap)]
  rule unwrap(wrap(V)) => depth(V)
  syntax Int ::= count(List) [function, total, symbol(count)]
  rule count(.List) => 0
  rule count(ListItem(_) L) => 1 +Int count(L)
  syntax Val ::= nat(Int) [function, total, symbol(nat)]
  rule nat(N) => z requires N <=Int 0
  rule nat(N) => s(nat(N -Int 1)) requires N >Int 0
  syntax Int ::= twice(Int) [function, total, symbol(twice)]
  rule twice(N) => N +Int N
  syntax Int ::= viaDepth(Int) [function, total, symbol(viaDepth)]
  rule viaDepth(N) => depth(nat(N))

  rule [depth-lemma]: depth(V) +Int 0 => depth(V) [simplification]
  rule [twice-lemma]: twice(N) +Int 0 => twice(N) [simplification]
  rule [note-lemma]: {_X:Note #Equals _Y:Note} => #Top [simplification]

  rule [run]: run(V, P) => P requires depth(V) >=Int 0 [preserves-definedness]
  rule [go]: go(I, P) => P requires twice(I) >Int 0 [preserves-definedness]
endmodule
