// A kind 1 invariant written as a fold over `<k>` (k2lean/docs/invariants.md; the gate's library
// `kfold`): every pending `use(L)` names a key of `<store>`. `kOk` folds the `K` sequence with the
// test of one item `itemOk`, which calls `kOk` back on the continuation that an item `later(K)`
// holds (as SIMPLE's stack frames do), so the two are mutually recursive, well-founded and
// `Option`-valued. `k2lean gen --invariant ok` turns the fold into its element-wise form
// `Invariant.kOk_iff`, which reads a rule's `<k>` item by item, and unfolds `itemOk` by its
// equations. `itemOk` tests `use(L)` and `later(K)`, `KItem`s of their own, and is `true` at every
// other item by its `owise` equation, which applies to a command (a `Cmd` injected into `KItem`)
// through `Invariant.itemOk_owise_Cmd`: `seq` pushes two commands, `call` a `use`, `wrap` a `later`
// holding a command, and `nop`, `use`, `later` pop one.
requires "domains.md"

module KFOLD-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= call(Int)          // use location L, a key of the store
               | nop()
               | wrap(Cmd)          // defer C in a `later` item
               | seq(Cmd, Cmd)
endmodule

module KFOLD
  imports KFOLD-SYNTAX
  imports INT
  imports MAP
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <store> .Map </store>

  syntax KItem ::= use(Int)
                 | later(K)

  syntax Bool ::= ok(GeneratedTopCell) [function, total]
                | kOk(K, Map) [function, total]
                | itemOk(KItem, Map) [function, total]
  rule ok(<generatedTop> <k> K </k> <store> S </store> _ </generatedTop>) => kOk(K, S)
  rule kOk(.K, _) => true
  rule kOk(I:KItem ~> K, S) => itemOk(I, S) andBool kOk(K, S)
  rule itemOk(use(L), S) => L in_keys(S)
  rule itemOk(later(K), S) => kOk(K, S)
  rule itemOk(_, _) => true [owise]

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k> [label(seq)]
  rule <k> call(L) => use(L) ... </k> <store> S </store> requires L in_keys(S) [label(call)]
  rule <k> use(_) => .K ... </k> [label(use)]
  rule <k> nop() => .K ... </k> [label(nop)]
  rule <k> wrap(C) => later(C ~> .K) ... </k> [label(wrap)]
  rule <k> later(_) => .K ... </k> [label(later)]
endmodule
