// A fixture of `k2lean confluence` with a false slot (k2lean/docs/design.md, section 3.6): the
// fixture race with each worker writing its count to the shared accumulator once, instead of
// adding to it. Two workers with different counts race on `<acc>`: the last write wins, so two
// schedules end with different `<acc>`, and the slot of two `put` steps is refuted.
requires "domains.md"

module DRF-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "spawn" "(" Int ")" ";" Pgm | "done"
endmodule

module DRF
  imports DRF-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  imports LIST
  imports K-EQUAL
  configuration <T>
      <k> $PGM:Pgm </k>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <todo> 0 </todo> </worker> </workers>
      <acc> 0 </acc>
      <next> 0 </next>
    </T>

  rule <worker> <wid> _ </wid> <todo> C => 0 </todo> </worker>
       <acc> _ => C </acc>
    requires C >Int 0 [label(put)]
  rule <k> spawn ( N ) ; P => P ... </k>
       <workers> (.Bag => <worker> <wid> I </wid> <todo> N </todo> </worker>) ... </workers>
       <next> I => I +Int 1 </next> [label(spawn)]
  rule <k> done => .K ... </k> [label(stop)]

  // Data-race freedom, `drfOk` (`gen --invariant drfOk@T`, k2lean/docs/invariants.md): at most one
  // write to `<acc>` is pending. A worker whose `todo` is positive claims the accumulator (the
  // claim `0`), and so does each `spawn(N)` with a positive `N` left in the program; no claim is
  // made twice. `wclaims` lists the workers' claims; the order K's map pattern takes the workers in
  // is not fixed, and `noDup` does not depend on it.
  syntax List ::= todoClaims(Int) [function, total]
                | pclaims(Pgm) [function, total]
                | kclaims(K) [function, total]
                | wclaims(WorkersCell) [function, total]
  syntax Bool ::= drfOk(TCell) [function, total]
                | noDup(List) [function, total]
  rule todoClaims(0) => .List
  rule todoClaims(_) => ListItem(0) [owise]
  rule pclaims(spawn(N); P) => todoClaims(N) pclaims(P)
  rule pclaims(done) => .List
  rule kclaims(.K) => .List
  rule kclaims(P:Pgm ~> K) => pclaims(P) kclaims(K)
  rule wclaims(<workers> .Bag </workers>) => .List
  rule wclaims(<workers> <worker> <wid> _ </wid> <todo> C </todo> </worker> Ws </workers>)
    => todoClaims(C) wclaims(<workers> Ws </workers>)
  rule noDup(.List) => true
  rule noDup(ListItem(X) L) => notBool (X in L) andBool noDup(L)
  rule drfOk(<T> <k> K </k> WS:WorkersCell <acc> _ </acc> <next> _ </next> </T>)
    => noDup(wclaims(WS) kclaims(K))
  // Not an invariant of the fixture: `k2lean/crates/k2lean/tests/cli.rs` checks that a fold of claims
  // read outside `noDup` (here by `==K` in a side condition, which depends on the order K's map
  // pattern takes the workers in) is not taken as a fold of claims.
  syntax Bool ::= drfOrdered(TCell) [function, total]
  rule drfOrdered(<T> <k> _ </k> WS:WorkersCell <acc> _ </acc> <next> _ </next> </T>) => noDup(wclaims(WS))
    requires wclaims(WS) ==K ListItem(0) ListItem(1)
  rule drfOrdered(_) => false [owise]
endmodule
