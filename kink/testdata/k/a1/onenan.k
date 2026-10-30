// kink27 R3-CENSUS-RUNLEVEL fix round 1 (review should-fix 1): a kill through two NaNs a run
// computes by different operations on symbolic operands. From `go(0)`, `0.0 /Float 0.0` and
// `(1.0 /Float 0.0) -Float (2.0 /Float 0.0)` are both NaN; `alike` gives 7 when its arguments are
// one term (`==K`), else 0. k-rust reads one NaN per format (kink README, premise P-F3), so the
// baseline ends in `done(7)`; a mutant that respells `2.0` to `-2.0` makes the second argument an
// infinity and ends in `done(0)`. In a model where the two NaNs differ both sides end in
// `done(0)`. No run reads a k-rust class value (one format, no sign, min or max), so the census
// and the run lists admit the comparison.
module ONENAN-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule
module ONENAN
  imports ONENAN-SYNTAX
  imports INT
  imports FLOAT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>
  syntax Int ::= alike(Float, Float) [function, total, symbol(alike)]
  rule [alike]: alike(A, B) => 7 requires A ==K B
  rule [alikeow]: alike(_, _) => 0 [owise]
  rule [go]: <k> go(I) => done(alike(0.0 /Float Int2Float(I, 53, 11), (1.0 /Float Int2Float(I, 53, 11)) -Float (2.0 /Float Int2Float(I, 53, 11)))) </k>
endmodule
