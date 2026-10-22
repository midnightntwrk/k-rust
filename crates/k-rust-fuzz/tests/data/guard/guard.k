// The climb's score fixture (FZ-12, ARCHITECTURE.md 6.2): a guard that is undefined for some
// inputs. `go(X)` becomes `at(X)`; `goal` fires when `notBool pb(X)`, where the partial
// function `pb(X) = 10 /Int X >Int 3` is undefined at `X = 0`, true at `X = 1` and `X = 2`, and
// false elsewhere; the `owise` rule `goal-else` ends every other walk. Every walk ends with an
// empty `<k>`: a natural end.

module GUARD-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module GUARD
  imports GUARD-SYNTAX
  imports INT
  imports BOOL

  syntax Bool  ::= pb(Int)  [function, symbol(pb)]
  syntax KItem ::= at(Int)  [symbol(at)]

  rule [pb-def]: pb(X) => 10 /Int X >Int 3

  configuration <k> $PGM:Pgm </k>

  rule [enter]:     <k> go(X) => at(X) </k>
  rule [goal]:      <k> at(X) => .K </k> requires notBool pb(X)
  rule [goal-else]: <k> at(_) => .K </k> [owise]
endmodule
