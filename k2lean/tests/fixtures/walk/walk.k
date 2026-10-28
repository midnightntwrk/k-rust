// A kind 1 invariant written as walks over maps by free-key patterns (k2lean/docs/invariants.md;
// the gate's library `walk`): every value of every worker's `<env>` is a key of `<store>`. The
// workers form a cell map, walked by `workersIn` with the pattern `<worker> … </worker> Ws` (the
// cell map's key is the worker's `<wid>`, read twice), and each environment is walked by `allIn`
// with `(_ |-> V) E`. `k2lean gen --invariant envsOk` turns both walks into element-wise forms
// (`Invariant.workersIn_walk`, `Invariant.allIn_walk`), which the collection lemmas read. The
// store is updated (`set`), grows by a fresh key (`grow`) and has a binding rebound (`bump`): the
// environments do not change there, and the invariant holds because every key of the store stays a
// key, which the collections closer derives from the store's terms (`MapHook.KeysIncl`).
// `idsOk` walks the workers with no test of its own: its pattern reads the key and `<wid>` with one
// variable, so a binding passes exactly when it is stored under its own `<wid>`
// (`Invariant.idsOk_test`); `fork` adds the new worker under its `<wid>`.
requires "domains.md"

module WALK-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= bind(Int, Int, Int)  // worker W binds X to location L, a key of the store
               | fork(Int, Int)       // worker W forks a worker V with a copy of its environment
               | drop(Int)            // worker W ends
               | forget(Int, Int)     // worker W unbinds X
               | set(Int, Int)        // store V at location L
               | grow(Int)            // add the fresh location L, bound to 0
               | bump(Int)            // increment the value at location L
               | seq(Cmd, Cmd)
endmodule

module WALK
  imports WALK-SYNTAX
  imports INT
  imports MAP
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <workers>
      <worker multiplicity="*" type="Map">
        <wid> 0 </wid>
        <env> .Map </env>
      </worker>
    </workers>
    <store> .Map </store>

  syntax Bool ::= envsOk(GeneratedTopCell) [function, total]
                | workersIn(WorkersCell, Map) [function, total]
                | allIn(Map, Map) [function, total]
                | idsOk(WorkersCell) [function]
  rule envsOk(<generatedTop> <k> _ </k> WS:WorkersCell <store> S </store> _ </generatedTop>)
    => workersIn(WS, S) andBool idsOk(WS)
  rule workersIn(<workers> .Bag </workers>, _) => true
  rule workersIn(<workers> <worker> <wid> _ </wid> <env> E </env> </worker> Ws </workers>, S)
    => allIn(E, S) andBool workersIn(<workers> Ws </workers>, S)
  rule idsOk(<workers> .Bag </workers>) => true
  rule idsOk(<workers> <worker> <wid> _ </wid> <env> _ </env> </worker> Ws </workers>)
    => idsOk(<workers> Ws </workers>)
  rule allIn(.Map, _) => true
  rule allIn((_ |-> V) E, S) => V in_keys(S) andBool allIn(E, S)

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k>
  rule <k> bind(W, X, L) => .K ... </k>
       <worker> <wid> W </wid> <env> E => E[X <- L] </env> </worker>
       <store> S </store>
    requires L in_keys(S) [label(bind)]
  rule <k> fork(W, V) => .K ... </k>
       <worker> <wid> W </wid> <env> E </env> </worker>
       (.Bag => <worker> <wid> V </wid> <env> E </env> </worker>) [label(fork)]
  rule <k> drop(W) => .K ... </k>
       (<worker> <wid> W </wid> <env> _ </env> </worker> => .Bag) [label(drop)]
  rule <k> forget(W, X) => .K ... </k>
       <worker> <wid> W </wid> <env> E => E[X <- undef] </env> </worker> [label(forget)]
  rule <k> set(L, V) => .K ... </k>
       <store> S => S[L <- V] </store> [label(set)]
  rule <k> grow(L) => .K ... </k>
       <store> S => S (L |-> 0) </store>
    requires notBool (L in_keys(S)) [label(grow)]
  rule <k> bump(L) => .K ... </k>
       <store> ... L |-> (I => I +Int 1) ... </store> [label(bump)]
endmodule
