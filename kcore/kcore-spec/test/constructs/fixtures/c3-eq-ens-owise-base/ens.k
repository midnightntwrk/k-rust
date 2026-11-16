// A function equation with an `ensures`: `half(N) => N /Int 2 ensures N >=Int 0`. The text's
// equation is `half(N) = N /Int 2 ∧ (N >=Int 0 = true)`: `half` has the value N /Int 2 where
// N >=Int 0 and no value where it does not. It is `half`'s only equation, so the reader reads it as
// the clause with `N >=Int 0` as its `requires` (`ensuresAsRequires`).
module ENS-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= half(Int) [function, symbol(half)]
  syntax Cmd ::= run(Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module ENS
  imports ENS-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule half(N) => N /Int 2 ensures N >=Int 0
  rule [go]: <k> run(N) => done(half(N)) </k>
endmodule
