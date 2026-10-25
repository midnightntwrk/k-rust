// State matches and committed transitions (docs/compatibility.md, "State matches", "Committed
// transitions"): programs whose paths meet, so that a `state-set` run absorbs an arrival.
//
// - `go(N)`: `ab` then `bd`, or `ac` then `cd`; both reach `<k> .K </k> <out> N </out>` at depth
//   2, where the `cd` arrival is merged into the `bd` one.
// - `mark(N)`: the same diamond, where the branch met first (`me`, `ed`) reads an
//   implementation-chosen value (`size(keys_list(...))` of a two-key map, 2 in every listing
//   order) and the other (`mf`, `fd`) reads nothing; both reach `<out> N </out>` at depth 2.
// - `pick(N)`: `bad` divides 10 by N and `good` writes 0; on `pick(0)` `bad`'s successor is
//   undefined beside `good`'s and is rolled back.
// - `undef(N)`: one step whose only rule divides 10 by N: an undefined step on `undef(0)`.
// - `loop(N)`: counts N down to 0, one state per value.

module MATCH-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)    [symbol(go)]
               | mark(Int)  [symbol(mark)]
               | pick(Int)  [symbol(pick)]
               | undef(Int) [symbol(undef)]
               | loop(Int)  [symbol(loop)]
endmodule

module MATCH
  imports MATCH-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) [symbol(b)] | c(Int) [symbol(c)]
                 | e(Int) [symbol(e)] | f(Int) [symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [ab]: <k> go(N) => b(N) ... </k>
  rule [ac]: <k> go(N) => c(N) ... </k>
  rule [bd]: <k> b(N) => .K ... </k> <out> _ => N </out>
  rule [cd]: <k> c(N) => .K ... </k> <out> _ => N </out>

  rule [me]: <k> mark(N) => e(N) ... </k>
  rule [mf]: <k> mark(N) => f(N) ... </k>
  rule [ed]: <k> e(N) => .K ... </k>
             <out> _ => N +Int size(keys_list((1 |-> 0) (2 |-> 0))) -Int 2 </out>
  rule [fd]: <k> f(N) => .K ... </k> <out> _ => N </out>

  rule [bad]:  <k> pick(N) => .K ... </k> <out> _ => 10 /Int N </out>
  rule [good]: <k> pick(_) => .K ... </k> <out> _ => 0 </out>

  rule [undef]: <k> undef(N) => .K ... </k> <out> _ => 10 /Int N </out>

  rule [down]: <k> loop(N) => loop(N -Int 1) ... </k> requires N >Int 0
  rule [stop]: <k> loop(0) => .K ... </k>
endmodule
