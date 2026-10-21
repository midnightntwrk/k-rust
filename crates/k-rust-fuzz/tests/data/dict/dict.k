// The dictionary proposer's fixture (FZ-11, ARCHITECTURE.md 8.3): guards whose constants a
// blind draw does not find, reached through the rule graph and through function calls.
//
// `run(N, S, M)` becomes `step1(N, S, M)` (rule `start`). `gate` moves on to `step2` only when
// `S` is the string "open"; its `owise` rule `gate-else` ends the walk. `goal` fires on
// `step2(N, _, fast)` when `limit(N) ==Int 1`: `limit`'s equation `limit-big` (N > 500) calls
// `cap`, whose equation `cap-eq` gives 1 only for N == 777, so `goal` fires exactly for
// `S = "open"`, `M = fast` and `N = 777`. Its `owise` rule `goal-else` ends every other walk.
//
// On `step2(N, _, slow)`, `slow` moves on to `probe(N)`. There `pgoal` fires when `good(N)`, a
// Boolean helper whose condition is its right-hand side (`N ==Int 4711`), and `igoal` when
// `pick(N) ==Int 1`, where `pick`'s right-hand side is `#if N ==Int 31337 #then 1 #else 0 #fi`;
// the `owise` rule `probe-else` writes `N` to `<out>`. These conditions are written in
// equation right-hand sides, not in `requires`.
//
// Every rule rewrites the whole `<k>` cell (no `...`), so the rule graph is the chain
// `pre` -> `start` -> `gate` -> `goal`, with `gate-else` beside `gate` and `goal-else` beside
// `goal`, and `gate` -> `slow` -> `pgoal`, `igoal`, `probe-else`: `pre` is 3 edges from `goal`,
// outside a radius of 2. No rule produces `far(N)`, so `far` does not reach `goal` at all.
// Every walk ends with an empty `<k>`: a natural end.

module DICT-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX

  syntax Mode ::= "fast" [symbol(fast)] | "slow" [symbol(slow)] | "idle" [symbol(idle)]
  syntax Pgm  ::= run(Int, String, Mode)  [symbol(run)]
endmodule

module DICT
  imports DICT-SYNTAX
  imports INT
  imports STRING
  imports BOOL
  imports K-EQUAL

  syntax Int ::= limit(Int)  [function, total, symbol(limit)]
               | cap(Int)    [function, total, symbol(cap)]

  rule [limit-big]:   limit(N) => cap(N) requires N >Int 500
  rule [limit-small]: limit(_) => 0 [owise]
  rule [cap-eq]:      cap(N) => 1 requires N ==Int 777
  rule [cap-other]:   cap(_) => 2 [owise]

  syntax Bool ::= good(Int)  [function, total, symbol(good)]
  syntax Int  ::= pick(Int)  [function, total, symbol(pick)]

  rule [good-def]: good(N) => N ==Int 4711
  rule [pick-def]: pick(N) => #if N ==Int 31337 #then 1 #else 0 #fi

  syntax KItem ::= step1(Int, String, Mode)  [symbol(step1)]
                 | step2(Int, String, Mode)  [symbol(step2)]
                 | pre(Int)                  [symbol(pre)]
                 | far(Int)                  [symbol(far)]
                 | probe(Int)                [symbol(probe)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [pre]:       <k> pre(N) => run(N, "early", idle) </k> requires N ==Int 4242
  rule [start]:     <k> run(N, S, M) => step1(N, S, M) </k>
  rule [gate]:      <k> step1(N, S, M) => step2(N, S, M) </k> requires S ==String "open"
  rule [gate-else]: <k> step1(_, _, _) => .K </k> [owise]
  rule [goal]:      <k> step2(N, _, fast) => .K </k> <out> _ => 1 </out>
                    requires limit(N) ==Int 1
  rule [goal-else]: <k> step2(_, _, _) => .K </k> [owise]
  rule [far]:       <k> far(N) => .K </k> requires N ==Int 123456
  rule [slow]:      <k> step2(N, _, slow) => probe(N) </k>
  rule [pgoal]:     <k> probe(N) => .K </k> <out> _ => 2 </out> requires good(N)
  rule [igoal]:     <k> probe(N) => .K </k> <out> _ => 3 </out> requires pick(N) ==Int 1
  rule [probe-else]: <k> probe(N) => .K </k> <out> _ => N </out> [owise]
endmodule
