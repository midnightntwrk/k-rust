// A kind 1 invariant over a map that rules extend by a map built by recursion on an `Int` range
// (k2lean/docs/invariants.md; the gate's library `range`): `alloc N` binds `N` fresh locations to
// `0`, `set L V` stores a non-negative value at a location, and every value of `<store>` stays a
// non-negative integer. `fill` is the shape of SIMPLE's `N ... M |-> K` with its value a plain
// variable; `k2lean gen --invariant storeNat@store` gets the lemma that `fill`'s result binds its
// value at each of its keys (`Invariant.range_*`, from `fill`'s two equations).
requires "domains.md"

module RANGE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= alloc(Int)     // N fresh locations bound to 0
               | set(Int, Int)  // store V at location L
               | seq(Cmd, Cmd)
endmodule

module RANGE
  imports RANGE-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  configuration
    <k> $PGM:Cmd </k>
    <next> 0 </next>
    <store> .Map </store>

  // the map binding V at every key from A to B
  syntax Map ::= fill(Int, Int, Int) [function]
  rule fill(A, B, _) => .Map requires A >Int B
  rule fill(A, B, V) => A |-> V fill(A +Int 1, B, V) requires A <=Int B

  // every value of the store is a non-negative integer
  syntax Bool ::= storeNat(Map) [function, total]
                | natVals(List) [function, total]
                | isNat(KItem) [function, total]
  rule storeNat(S) => natVals(values(S))
  rule natVals(.List) => true
  rule natVals(ListItem(X) L) => isNat(X) andBool natVals(L)
  rule isNat(I:Int) => I >=Int 0
  rule isNat(_) => false [owise]

  rule <k> seq(C1, C2) => C1 ~> C2 ... </k>
  rule <k> alloc(N) => .K ... </k>
       <next> L => L +Int N </next>
       <store> S => S fill(L, L +Int N -Int 1, 0) </store>
    requires N >=Int 0 [label(alloc)]
  rule <k> set(L, V) => .K ... </k>
       <store> S => S[L <- V] </store>
    requires V >=Int 0 [label(set)]
endmodule
