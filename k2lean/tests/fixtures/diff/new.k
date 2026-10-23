// k2lean diff fixture, new generation (tests/fixtures/regen.sh compiles it into new/).
// Against old.k: every line moved; `start` relabelled `begin`; `done(s(z))` has a new
// right-hand side; `back(s(N))` uses `M` (a focus edit, same rule); `back(z)` removed;
// a second `halt(N)` rule (a collision: both get a digest); `stop(s(s(N)))` became
// `stop(s(N))` (a focus edit that changes the rule); `run(z)` added.


module DIFF-SYNTAX
  syntax Nat ::= "z" | s(Nat)
  syntax Pgm ::= run(Nat) | done(Nat) | back(Nat) | halt(Nat) | stop(Nat)
endmodule

module DIFF
  imports DIFF-SYNTAX
  configuration <k> $PGM:Pgm </k>

  rule <k> run(N) => done(N) </k> [label(begin)]
  rule <k> done(s(s(N))) => done(N) </k>
  rule <k> done(s(z)) => stop(s(z)) </k>
  rule <k> back(s(M)) => back(M) </k>
  rule <k> halt(N) => done(N) </k>
  rule <k> halt(N) => run(N) </k>
  rule <k> stop(s(N)) => stop(N) </k>
  rule <k> run(z) => stop(z) </k>
endmodule
