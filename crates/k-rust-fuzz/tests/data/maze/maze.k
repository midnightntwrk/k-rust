// The stall benchmark (FZ-13): a maze of nested guarded rules over nine integer holes, after
// daedaluzz. `walk(A, B, C, D, E, F, G, H, I)` stores the holes in cells and starts at room
// `r0`. Every rule labelled `c*`, `s*` or `u*` is a cell, and every cell is a rule target.
//
// - The corridor `c1` .. `c7` leads from room `r0` to room `r6` and out: cell k fires only on a
//   path that fired cells 1 .. k-1, since only cell k-1 produces the room cell k leaves from.
// - The side cells `s1` .. `s5` branch off the corridor and end the walk.
// - The cells `u1` .. `u4` are unreachable (negative controls): `u1`'s guard is unsatisfiable,
//   `u2`'s contradicts the guard of `c4` on the path to its room, no rule produces `u3`'s room
//   `rz`, and `u4`'s nonlinear guard has no integer solution.
//
// The guards of one room are pairwise disjoint, so every input has exactly one path whatever
// the rule order, and each room's `owise` rule ends the walk when no cell's guard holds. Every
// walk ends with an empty `<k>`: a natural end. The holes never change after `enter`, so a
// guard on a hole states a fact about the input. `research/stall-benchmark.md` in the fz26
// notes gives each guard's kind and the proposer meant to crack it.

module MAZE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= walk(Int, Int, Int, Int, Int, Int, Int, Int, Int)  [symbol(walk)]
endmodule

module MAZE
  imports MAZE-SYNTAX
  imports INT
  imports BOOL

  syntax KItem ::= "r0" [symbol(r0)] | "r1" [symbol(r1)] | "r2" [symbol(r2)]
                 | "r3" [symbol(r3)] | "r4" [symbol(r4)] | "r5" [symbol(r5)]
                 | "r6" [symbol(r6)] | "rz" [symbol(rz)]

  configuration <k> $PGM:Pgm </k>
                <a> 0 </a> <b> 0 </b> <c> 0 </c> <d> 0 </d> <e> 0 </e>
                <f> 0 </f> <g> 0 </g> <h> 0 </h> <i> 0 </i>

  rule [enter]:
    <k> walk(A, B, C, D, E, F, G, H, I) => r0 ... </k>
    <a> _ => A </a> <b> _ => B </b> <c> _ => C </c> <d> _ => D </d> <e> _ => E </e>
    <f> _ => F </f> <g> _ => G </g> <h> _ => H </h> <i> _ => I </i>

  // Room r0.
  rule [c1]: <k> r0 => r1 ... </k> <a> A </a> requires A >Int 0
  rule [r0-out]: <k> r0 => .K ... </k> [owise]

  // Room r1 (A > 0).
  rule [c2]: <k> r1 => r2 ... </k> <a> A </a> <b> B </b> requires B >Int A
  rule [s1]: <k> r1 => .K ... </k> <b> B </b> requires B <Int 0 andBool B >Int -64
  rule [u1]: <k> r1 => .K ... </k> <a> A </a> requires A >Int 10 andBool A <Int 5
  rule [r1-out]: <k> r1 => .K ... </k> [owise]

  // Room r2 (A > 0, B > A).
  rule [c3]: <k> r2 => r3 ... </k> <c> C </c> requires C ==Int 7
  rule [s2]: <k> r2 => .K ... </k> <c> C </c> requires C >Int 4096 andBool C <Int 8192
  rule [s3]: <k> r2 => .K ... </k> <c> C </c> <d> D </d> requires C <Int -1 andBool D ==Int C
  rule [u4]: <k> r2 => .K ... </k> <c> C </c> requires C *Int C ==Int 2
  rule [r2-out]: <k> r2 => .K ... </k> [owise]

  // Room r3 (C = 7).
  rule [c4]: <k> r3 => r4 ... </k> <d> D </d> requires D >Int 1000 andBool D <Int 1100
  rule [s4]: <k> r3 => .K ... </k> <d> D </d> requires D <Int -1000000
  rule [r3-out]: <k> r3 => .K ... </k> [owise]

  // Room r4 (1000 < D < 1100).
  rule [c5]: <k> r4 => r5 ... </k> <e> E </e> requires E ==Int 31337
  rule [u2]: <k> r4 => .K ... </k> <d> D </d> requires D <Int 50
  rule [r4-out]: <k> r4 => .K ... </k> [owise]

  // Room r5 (E = 31337).
  rule [c6]: <k> r5 => r6 ... </k> <f> F </f> <g> G </g>
    requires F *Int 3 ==Int G +Int 1000001 andBool G >Int 5000
  rule [s5]: <k> r5 => .K ... </k> <f> F </f> <g> G </g>
    requires G <=Int 5000 andBool F ==Int G +Int 12345
  rule [r5-out]: <k> r5 => .K ... </k> [owise]

  // Room r6 (3F = G + 1000001, G > 5000).
  rule [c7]: <k> r6 => .K ... </k> <h> H </h> <i> I </i>
    requires H *Int I ==Int 2021027 andBool 1 <Int H andBool H <Int I
  rule [r6-out]: <k> r6 => .K ... </k> [owise]

  // Room rz, which no rule produces.
  rule [u3]: <k> rz => .K ... </k>
endmodule
