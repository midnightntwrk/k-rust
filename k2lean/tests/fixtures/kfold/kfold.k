// A kind 1 invariant written as a fold over `<k>` (k2lean/docs/invariants.md; the gate's library
// `kfold`): every pending `use(L)` names a key of `<store>`. `kOk` folds the `K` sequence with the
// test of one item `itemOk`, which calls `kOk` back on the continuation that an item `later(K)`
// holds (as SIMPLE's stack frames do), so the two are mutually recursive, well-founded and
// `Option`-valued. `k2lean gen --invariant ok` turns the fold into its element-wise form
// `Invariant.kOk_iff`, which reads a rule's `<k>` item by item, and unfolds `itemOk` by its
// equations. `itemOk` tests `use(L)` and `later(K)`, `KItem`s of their own, and is `true` at every
// other item by its `owise` equation, which applies to a command (a `Cmd` injected into `KItem`)
// through `Invariant.itemOk_owise_Cmd`: `seq` pushes two commands, `call` a `use`, `wrap` a `later`
// holding a command, and `nop`, `use`, `later` pop one. The `<stack>` list is folded by `stackOk`
// with the same partial test (`Invariant.stackOk_iff`, from its two equations): `push` pushes a
// `later`, `pop` drops one. An item `scope(E)` holds a map whose every value is a key of the store
// (`allIn`, a map walk). The store grows (`grow`) and is updated (`set`): every pending item stays
// valid because the group `kOk`, `itemOk`, `stackOk` reads the store through its keys only, which
// `Invariant.itemOk_mono` and the others prove from the equations (`invariants.md` §3.1).
requires "domains.md"

module KFOLD-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= call(Int)          // use location L, a key of the store
               | nop()
               | wrap(Cmd)          // defer C in a `later` item
               | push(Cmd)          // defer C on the stack
               | pop()
               | seq(Cmd, Cmd)
               | grow(Int)          // add the fresh location L, bound to 0
               | set(Int, Int)      // store V at location L
               | save(Int)          // remember location L, a key of the store, in a scope
endmodule

module KFOLD
  imports KFOLD-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <store> .Map </store>
    <stack> .List </stack>

  syntax KItem ::= use(Int)
                 | later(K)
                 | scope(Map)

  syntax Bool ::= ok(GeneratedTopCell) [function, total]
                | kOk(K, Map) [function, total]
                | itemOk(KItem, Map) [function, total]
                | stackOk(List, Map) [function, total]
                | allIn(Map, Map) [function, total]
  rule ok(<generatedTop> <k> K </k> <store> S </store> <stack> St </stack> _ </generatedTop>)
    => kOk(K, S) andBool stackOk(St, S)
  rule kOk(.K, _) => true
  rule kOk(I:KItem ~> K, S) => itemOk(I, S) andBool kOk(K, S)
  rule itemOk(use(L), S) => L in_keys(S)
  rule itemOk(later(K), S) => kOk(K, S)
  rule itemOk(scope(E), S) => allIn(E, S)
  rule itemOk(_, _) => true [owise]
  rule stackOk(.List, _) => true
  rule stackOk(ListItem(I) L, S) => itemOk(I, S) andBool stackOk(L, S)
  rule allIn(.Map, _) => true
  rule allIn((_ |-> V) E, S) => V in_keys(S) andBool allIn(E, S)

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k> [label(seq)]
  rule <k> call(L) => use(L) ... </k> <store> S </store> requires L in_keys(S) [label(call)]
  rule <k> use(_) => .K ... </k> [label(use)]
  rule <k> nop() => .K ... </k> [label(nop)]
  rule <k> wrap(C) => later(C ~> .K) ... </k> [label(wrap)]
  rule <k> later(_) => .K ... </k> [label(later)]
  rule <k> push(C) => .K ... </k> <stack> St => ListItem(later(C ~> .K)) St </stack> [label(push)]
  rule <k> pop() => .K ... </k> <stack> ListItem(_) St => St </stack> [label(pop)]
  rule <k> grow(L) => .K ... </k> <store> S => S (L |-> 0) </store>
    requires notBool (L in_keys(S)) [label(grow)]
  rule <k> set(L, V) => .K ... </k> <store> S => S[L <- V] </store> [label(set)]
  rule <k> save(L) => scope(0 |-> L) ... </k> <store> S </store> requires L in_keys(S) [label(save)]
  rule <k> scope(_) => .K ... </k> [label(scope)]
endmodule
