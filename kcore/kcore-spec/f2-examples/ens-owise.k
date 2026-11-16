// An equation with an `ensures` beside an `[owise]` equation: the text gives `half` no value where
// N >=Int 0 fails, while reading the `ensures` as a `requires` would let the `[owise]` clause give
// it 0 there; the reader refuses it (`ensuresPriority`).
module ENS-OWISE-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= half(Int) [function, symbol(half)]
  syntax Cmd ::= run(Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module ENS-OWISE
  imports ENS-OWISE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule half(N) => N /Int 2 ensures N >=Int 0
  rule half(_) => 0 [owise]
  rule [go]: <k> run(N) => done(half(N)) </k>
endmodule
