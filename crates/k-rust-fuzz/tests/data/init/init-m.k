// Mutant of the initializer pair (FZ-ENGINE-R4, final review S1): `f(go(N))` is
// `N *Int (N /Int N)`, which is `N` for every `N =/= 0` and undefined for `N = 0`. So the initial
// configuration of `go(0)` has no instance in the mutant, and the mutant has no run and no end on
// it, while the baseline ends with `0` in <x>: a removed end one step before any rule applies.

module INIT-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module INIT
  imports INIT-SYNTAX
  imports INT

  syntax Int ::= f(Pgm)  [function, symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <x> f($PGM) </x>

  rule f(go(N)) => N *Int (N /Int N)
endmodule
