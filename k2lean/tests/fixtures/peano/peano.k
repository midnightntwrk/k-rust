module PEANO-SYNTAX
  syntax Nat ::= "z" | s(Nat)
  syntax Pgm ::= run(Nat) | done(Nat)
endmodule

module PEANO
  imports PEANO-SYNTAX
  configuration <k> $PGM:Pgm </k>

  syntax Nat ::= plus(Nat, Nat) [function, total]
  rule plus(z, M) => M
  rule plus(s(N), M) => s(plus(N, M))

  syntax Nat ::= double(Nat) [function, total]
  rule double(N) => plus(N, N)

  syntax B ::= "tt" | "ff"
  syntax B ::= even(Nat) [function, total]
             | odd(Nat)  [function, total]
  rule even(z) => tt
  rule even(s(N)) => odd(N)
  rule odd(z) => ff
  rule odd(s(N)) => even(N)

  syntax Nat ::= pick(B, Nat) [function, total]
  rule pick(tt, N) => double(N)
  rule pick(_, N) => N [owise]

  rule <k> run(N) => done(pick(even(N), N)) </k> [label(start)]
  rule <k> done(s(s(N))) => done(N) </k>
endmodule
