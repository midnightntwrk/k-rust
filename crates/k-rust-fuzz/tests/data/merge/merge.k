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
// - `tri(N)`: three first steps. `u` then `ue` ends at `<out> N`; `t` then `te` ends there at the
//   same depth, so under `state-set` its arrival is absorbed into `u`'s; `s` sets `<out>` to 7,
//   after which `t` fires again and `te`, which needs `<out> 0`, cannot: an abnormal stop at
//   `h(N)` with `t` on its trace (and `u` then `ue` reach `<out> N` a step later).
// - `chain(N)`: N diamonds in a row, each `cl` or `cr` then back to `chain(N - 1)`, ending at
//   `chain(0)` with `<out> 1`: 2^N paths and 3N + 1 distinct states.
// - `both(N)`: `mark(5)`, then `chain(N)` (FZ-STATESET-MATCH): `<k> chain(N) </k> <out> 5 </out>`
//   at depth 3 is reached first on `mark`'s branch that reads a chosen value, and a path set
//   then explores that branch's 2^N paths before the clean branch, so a modest work bound cuts it
//   there; a state set expands `chain(N)` once and absorbs the clean branch's arrival.
// - `stall(N)`: `sa` then `sz`, or `sb` then `tz`, both reaching `<k> z(N) </k>` at depth 2, to
//   which no rule applies: an abnormal stop on every path. Under `state-set` the `sb` arrival
//   is absorbed, so `sb` fires on no retained trace (FZ-STATESET-MATCH).

module MERGE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Pgm ::= go(Int)    [symbol(go)]
               | mark(Int)  [symbol(mark)]
               | pick(Int)  [symbol(pick)]
               | tri(Int)   [symbol(tri)]
               | chain(Int) [symbol(chain)]
               | both(Int)  [symbol(both)]
               | stall(Int) [symbol(stall)]

  // Whether `X` is the first key `keys_list` lists of a two-key map, which the definition
  // leaves open: k-rust lists the keys in execution mode and leaves the listing unevaluated in
  // proof mode (FZ-STATESET-MATCH).
  syntax Bool ::= isFirst(Int) [function, symbol(isFirst)]
endmodule

module MERGE
  imports MERGE-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) | c(Int) | e(Int) | f(Int) | g(Int) | h(Int) | l(Int) | r(Int)
                 | y(Int) | w(Int) | z(Int)

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

  rule [u]:  <k> tri(N) => g(N) ... </k>
  rule [t]:  <k> tri(N) => h(N) ... </k>
  rule [s]:  <k> tri(_) ... </k> <out> 0 => 7 </out>
  rule [ue]: <k> g(N) => .K ... </k> <out> _ => N </out>
  rule [te]: <k> h(N) => .K ... </k> <out> 0 => N </out>

  rule [cl]: <k> chain(N) => l(N) ... </k> requires N >Int 0
  rule [cr]: <k> chain(N) => r(N) ... </k> requires N >Int 0
  rule [ld]: <k> l(N) => chain(N -Int 1) ... </k>
  rule [rd]: <k> r(N) => chain(N -Int 1) ... </k>
  rule [c0]: <k> chain(0) => .K ... </k> <out> _ => 1 </out>

  rule [bm]: <k> both(N) => mark(5) ~> chain(N) ... </k>

  rule isFirst(X) => X ==Int {keys_list((1 |-> 0) (2 |-> 0)) [ 0 ]}:>Int

  rule [sa]: <k> stall(N) => y(N) ... </k>
  rule [sb]: <k> stall(N) => w(N) ... </k>
  rule [sz]: <k> y(N) => z(N) ... </k>
  rule [tz]: <k> w(N) => z(N) ... </k>
endmodule
