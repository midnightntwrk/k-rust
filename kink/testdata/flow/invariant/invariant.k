// Flow fixture (FB-39): argued obligations whose arguments rest on invariants. A memory whose keys
// an invariant keeps outside a ROM region, read by a pair of rules split on the region, and two
// scalar cells an invariant orders; the corpus only idles, so no read and no bump is matched.
module INVARIANT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= read(Int) [symbol(read)]
               | "bump"    [symbol(bump)]
               | "idle"    [symbol(idle)]
endmodule

module INVARIANT
  imports INVARIANT-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports LIST

  configuration
    <t>
      <k> $PGM:Pgm </k>
      <memory> 8 |-> 0 </memory>
      <romEnd> 4 </romEnd>
      <a> 0 </a>
      <b> 1 </b>
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

  // The scalar invariant: `a` is at most `b`; and a function of the same cells that is no
  // invariant, since it is not Bool.
  syntax Bool ::= ordered(Int, Int) [function, total, symbol(ordered)]
  rule ordered(A, B) => A <=Int B
  syntax Int ::= gap(Int, Int) [function, total, symbol(gap)]
  rule gap(A, B) => B -Int A
  // The same order under another function, and a claim false of every state, which therefore
  // excludes everything.
  syntax Bool ::= orderedToo(Int, Int) [function, total, symbol(orderedToo)]
  rule orderedToo(A, B) => A <=Int B
  syntax Bool ::= never(Int) [function, total, symbol(never)]
  rule never(A) => A <Int A

  rule [readz]:    <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires notBool inRom(E, A)
  rule [readzRom]: <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires inRom(E, A)
  rule [bump]: <k> bump => .K ... </k> <a> A </a> <b> B => A </b> requires A >Int B
  rule [idle]: <k> idle => .K ... </k>
endmodule
