// K claims over the decoder of tests/fixtures/prio/prio.k against its independently written table
// `expected` (the operands' fields as `/Int` and `%Int`, the decoder's as bit ranges).
requires "prio.k"

module PRIO-SPEC
  imports PRIO

  // one opcode: the target's operands are values of partial functions at literals
  // (`22 /Int 4`), found before the configuration is unified (`solveWitness`)
  claim [one]: <k> dec(22) => mv(expected((22 /Int 4) %Int 4), expected(22 %Int 4)) </k>

  // the family: `dec(X)` by its equation whose `requires` the claim's implies (`byEquation`), then
  // the two tables at the symbolic fields, by cases on each field's values (`kc_index_split`)
  claim [family]: <k> dec(X:Int) => mv(expected((X /Int 4) %Int 4), expected(X %Int 4)) </k>
    requires X >=Int 0 andBool X <Int 64 andBool bitRangeInt(X, 4, 2) ==Int 1 andBool X =/=Int 21

  // the family with source and destination swapped: false (at 22, `mv(rb, rc)` is no `mv(rc, rb)`
  // and has no successor), refuted by hand (demos/claims/hand/PrioHand.lean)
  claim [swapped]: <k> dec(X:Int) => mv(expected(X %Int 4), expected((X /Int 4) %Int 4)) </k>
    requires X >=Int 0 andBool X <Int 64 andBool bitRangeInt(X, 4, 2) ==Int 1 andBool X =/=Int 21
endmodule
