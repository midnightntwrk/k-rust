// The fixture of kink-native's `invariant` tests: a memory whose keys an invariant keeps
// outside a ROM region, read by a pair of rules split on the region, and two scalar cells an
// invariant orders.
module INVMEM-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= read(Int) [symbol(read)]
              | "bump" [symbol(bump)]
              | "tie" [symbol(tie)]
              | "aliased" [symbol(aliased)]
              | "either" [symbol(either)]
              | "disjoint" [symbol(disjoint)]
              | "implied" [symbol(implied)]
endmodule

module INVMEM
  imports INVMEM-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports MAP
  imports LIST

  configuration
    <t>
      <k> $PGM:K </k>
      <memory> .Map </memory>
      <romEnd> 0 </romEnd>
      <a> 0 </a>
      <b> 0 </b>
    </t>

  // Whether an address lies in the ROM region, which ends at `E`.
  syntax Bool ::= inRom(Int, Int) [function, total, symbol(inRom)]
  rule inRom(E, A) => A <Int E

  // No key of the map lies in the ROM region: a walk over the map's bindings.
  syntax Bool ::= outsideRom(Map, Int) [function, total, symbol(outsideRom)]
  rule outsideRom(.Map, _) => true
  rule outsideRom((K:Int |-> _) M, E) => notBool inRom(E, K) andBool outsideRom(M, E)
  rule outsideRom((_ |-> _) M, E) => outsideRom(M, E) [owise]

  // The same invariant, as a fold over the list of the map's keys.
  syntax Bool ::= outsideRomKeys(Map, Int) [function, total, symbol(outsideRomKeys)]
                | keysOutside(List, Int) [function, total, symbol(keysOutside)]
  rule outsideRomKeys(M, E) => keysOutside(keys_list(M), E)
  rule keysOutside(.List, _) => true
  rule keysOutside(ListItem(K:Int) L, E) => notBool inRom(E, K) andBool keysOutside(L, E)
  rule keysOutside(ListItem(_) L, E) => keysOutside(L, E) [owise]

  // The scalar invariant: `a` is at most `b`.
  syntax Bool ::= ordered(Int, Int) [function, total, symbol(ordered)]
  rule ordered(A, B) => A <=Int B

  rule [readz]:    <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires notBool inRom(E, A)
  rule [readzRom]: <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires inRom(E, A)

  rule [bump]: <k> bump => .K ... </k> <a> A </a> <b> B </b> requires A >Int B
  rule [tie]:  <k> tie => .K ... </k> <a> A </a> <b> B </b> requires A >Int B andBool B >Int A

  // `small` and `big` read one cell, for the alternatives of `either`.
  syntax Bool ::= small(Int) [function, total, symbol(small)]
                | big(Int) [function, total, symbol(big)]
  rule small(A) => A <=Int 0
  rule big(A) => A >Int 1

  // A cell bound by an alias that the right-hand side reads.
  syntax Int ::= aOf(ACell) [function, total, symbol(aOf)]
  rule aOf(<a> X </a>) => X
  rule [aliased]: <k> aliased => .K ... </k> (<a> A </a> #as C) <b> B => aOf(C) </b>
    requires A >Int B
  // An axiom whose left-hand side has two alternatives.
  rule [either]: <k> either => .K ... </k> <a> (0 #Or 1) </a>
  // Guards whose second atom is reached through a disjunction and an implication.
  rule [disjoint]: <k> disjoint => .K ... </k> <a> A </a> <b> B </b>
    requires A >Int B orBool B >Int A
  rule [implied]: <k> implied => .K ... </k> <a> A </a> <b> B </b>
    requires A >Int B impliesBool B >Int A
endmodule
