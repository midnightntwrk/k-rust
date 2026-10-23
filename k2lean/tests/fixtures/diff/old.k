// k2lean diff fixture, old generation (tests/fixtures/regen.sh compiles it into old/).
module DIFF-SYNTAX
  syntax Nat ::= "z" | s(Nat)
  syntax Pgm ::= run(Nat) | done(Nat) | back(Nat) | halt(Nat) | stop(Nat)
endmodule

module DIFF
  imports DIFF-SYNTAX
  configuration <k> $PGM:Pgm </k>

  rule <k> run(N) => done(N) </k> [label(start)]
  rule <k> done(s(s(N))) => done(N) </k>
  rule <k> done(s(z)) => stop(z) </k>
  rule <k> back(s(N)) => back(N) </k>
  rule <k> back(z) => stop(z) </k>
  rule <k> halt(N) => done(N) </k>
  rule <k> stop(s(s(N))) => stop(N) </k>
endmodule
