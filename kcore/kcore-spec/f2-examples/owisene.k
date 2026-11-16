// An `[owise]` equation beside a `non-executable` one, as the corpus fixture
// owise-ignored-competitors: kompile's `[owise]` premise negates `choose(a, Y)` and not
// `choose(b, Y)` [non-executable]. The `non-executable` equation is an axiom of the text, read as
// an `aside` clause: one that no clause's priority premise negates. At (b, a) the text states both
// `= a` and `= b` (test/AsideClauses.lean).
module OWISENE-SYNTAX
  syntax Exp ::= "a" [symbol(a)] | "b" [symbol(b)]
               | choose(Exp, Exp) [function, symbol(choose)]
  syntax Cmd ::= go(Exp, Exp) [symbol(go)] | done(Exp) [symbol(done)]
endmodule

module OWISENE
  imports OWISENE-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [choose-a]: choose(a, Y) => Y
  rule [choose-b]: choose(b, Y) => Y [non-executable]
  rule [otherwise]: choose(X, _) => X [owise]
  rule [go]: <k> go(X, Y) => done(choose(X, Y)) </k>
endmodule
