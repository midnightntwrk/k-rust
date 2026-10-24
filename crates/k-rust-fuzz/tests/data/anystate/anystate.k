// Any-state pattern targets (ARCHITECTURE.md 4.1, FZ-ANYSTATE).
//
// `hold(N)` writes `keep(f(N))` on <k> before `drop`, and rule `drop` then erases it. `f` is a
// partial function whose only equation is `f(0) => 1`. So `hold(0)` passes through the
// configuration `keep(1) ~> drop`, and every other `hold(N)` through one that holds the
// unevaluated `f(N)`, which may denote nothing: a pattern that matches it does not reach there.
// k-rust keeps that step's definedness obligation `#Ceil(f(N))` as the path's constraint (on
// both later configurations), beside the undefined step under `#Not(#Ceil(f(N)))`.

module ANYSTATE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= hold(Int)  [symbol(hold)]
endmodule

module ANYSTATE
  imports ANYSTATE-SYNTAX
  imports INT

  syntax Int   ::= f(Int)    [function, symbol(f)]
  syntax KItem ::= keep(Int) [symbol(keep)]
                 | "drop"    [symbol(drop)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [f-zero]: f(0) => 1

  rule [hold]: <k> hold(N) => keep(f(N)) ~> drop ... </k>
  rule [drop]: <k> keep(_) ~> drop => .K ... </k> <out> _ => 1 </out>
endmodule
