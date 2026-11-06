// f's andThenBool skips N /Int D, a partial application that owes D =/=Int 0, so the
// witness at f originates. g applies f under its own andThenBool: with f declared total, g's
// witness is inherited from f (removing f's origin removes it); with f partial, g's originates
// too, since f(N, D) may be undefined on every reading.
module SCORIGP-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Bool, Int, Int) [symbol(go)] | res(Bool) [symbol(res)]
endmodule
module SCORIGP
  imports SCORIGP-SYNTAX
  imports INT
  imports BOOL
  syntax Bool ::= f(Int, Int) [function, symbol(f)] | g(Bool, Int, Int) [function, total, symbol(g)]
  configuration <k> $PGM:Prog </k>
  rule f(N, D) => D =/=Int 0 andThenBool N /Int D >Int 1
  rule g(B, N, D) => B andThenBool f(N, D)
  rule [go]: <k> go(B, N, D) => res(g(B, N, D)) </k>
endmodule
