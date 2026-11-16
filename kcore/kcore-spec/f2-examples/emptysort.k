// Sorts without a value: `Empty` has no production, `Loop` only a production over itself, so no
// finite term has either sort. `f` takes an Empty and has no equation; `g`'s first equation matches
// an Empty, so only its `owise` equation applies to a value.
module EMPTYSORT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Empty
  syntax Loop ::= loop(Loop) [symbol(loop)]
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule

module EMPTYSORT
  imports EMPTYSORT-SYNTAX
  imports INT
  imports BOOL
  syntax Bool ::= f(Empty) [function, symbol(f)]
  syntax Int ::= g(KItem) [function, symbol(g)]
  rule g(_:Empty) => 1
  rule g(_) => 0 [owise]
  configuration <k> $PGM:Pgm </k>
  rule <k> go(I) => done(g(I)) </k>
endmodule
