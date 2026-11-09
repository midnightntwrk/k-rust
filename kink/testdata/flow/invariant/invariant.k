// Flow fixture (FB-39): argued obligations whose arguments rest on invariants. A memory whose keys
// an invariant keeps outside a ROM region, read by a pair of rules split on the region and written
// by a rule that may store anywhere, and two scalar cells an invariant orders; the corpus only
// idles, so no read, write and bump is matched, and a test adds the programs it needs. `inRom` is
// applied by the read rules too, so it stays an obligation under any invariant; the invariants'
// own functions are applied by no rule.
module INVARIANT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= read(Int)       [symbol(read)]
               | write(Int, Int) [symbol(write)]
               | "bump"          [symbol(bump)]
               | "idle"          [symbol(idle)]
               > Pgm ";" Pgm     [symbol(seq), right]
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

  // No key of the map lies in the ROM region, written as its violation: `false` where some
  // binding breaks it, `true` otherwise. Whichever binding the map pattern takes, the first
  // equation gives `false`, so its self-pair joins, and the `owise` equation is a priority group
  // of its own.
  syntax Bool ::= outsideRom(Map, Int) [function, total, symbol(outsideRom)]
  rule outsideRom((K:Int |-> _) _, E) => false requires inRom(E, K)
  rule outsideRom(_, _) => true [owise]

  // The same invariant as a recursive walk over the map's bindings: its right-hand side reads the
  // binding the map pattern took, so the critical-pair check does not show its self-pair to join,
  // and it is not shown to be a function.
  syntax Bool ::= outsideRomWalk(Map, Int) [function, total, symbol(outsideRomWalk)]
  rule outsideRomWalk(.Map, _) => true
  rule outsideRomWalk((K:Int |-> _) M, E) => notBool inRom(E, K) andBool outsideRomWalk(M, E)
  rule outsideRomWalk((_ |-> _) M, E) => outsideRomWalk(M, E) [owise]

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
  // The same invariant under another function, and a claim false of every state, which
  // therefore excludes everything.
  syntax Bool ::= outsideRomToo(Map, Int) [function, total, symbol(outsideRomToo)]
  rule outsideRomToo(M, E) => outsideRom(M, E)
  syntax Bool ::= never(Int) [function, total, symbol(never)]
  rule never(A) => A <Int A

  rule [readz]:    <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires notBool inRom(E, A)
  rule [readzRom]: <k> read(A) => .K ... </k> <memory> (A |-> _) _ </memory> <romEnd> E </romEnd>
    requires inRom(E, A)
  rule [bump]: <k> bump => .K ... </k> <a> A </a> <b> B => A </b> requires A >Int B
  rule [idle]: <k> idle => .K ... </k>
  rule [write]: <k> write(A, V) => .K ... </k> <memory> M => M [ A <- V ] </memory>
  rule [seq]: <k> P:Pgm ; Q:Pgm => P ~> Q ... </k>
endmodule
