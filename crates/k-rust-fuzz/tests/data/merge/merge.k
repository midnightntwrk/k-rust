// Branches that meet (FZ-STATESET): each program's two first steps lead to one configuration at
// depth 2, so a `state-set` run keeps the arrival it meets first and absorbs the other, whose
// trace no leaf keeps; a `path-set` run keeps both leaves.
//
// - `go(N)`: `ab` then `bd`, or `ac` then `cd`, both ending with N in <out>. Neither reads
//   anything. Under `state-set` the `ab` arrival is met first, so `ac` fires on a path the
//   result shows on no leaf (B1, `fired-off-trace`).
// - `mark(N)`: the same diamond, where the branch met first (`me`, `ed`) reads an
//   implementation-chosen value (`size(keys_list(...))` of a two-key map, `MAP.keys_list`, class
//   `order`; 2 in every listing order) and the other (`mf`, `fd`) reads nothing. Under
//   `state-set` without `max_work` the one leaf carries the first arrival's mark (V1); under
//   `path-set` the `fd` leaf is clean.
// - `pick(N)`: two candidates of one priority; `bad` divides 10 by N, `good` writes 0. On
//   `pick(0)` `bad`'s successor is undefined beside `good`'s, so it is rolled back: `bad` is in
//   coverage `applied` and on no path.

module MERGE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)    [symbol(go)]
               | mark(Int)  [symbol(mark)]
               | pick(Int)  [symbol(pick)]
endmodule

module MERGE
  imports MERGE-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) | c(Int) | e(Int) | f(Int)

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
endmodule
