// Function equations with a free-key map pattern `K |-> V REST` (crates/k2lean/tests/snapshots.rs):
// such an equation applies at the first binding, in the map's order, at which the rest of its
// left-hand side and its requires hold (k2lean/docs/design.md, section 2, "Functions").
requires "domains.md"

module FREEKEY-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go"
endmodule

module FREEKEY
  imports FREEKEY-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <m> .Map </m>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <cnt> 0 </cnt> </worker> </workers>
    </T>

  // not recursive: some value is a negative integer (the value does not depend on the binding)
  syntax Bool ::= hasNeg(Map) [function, total]
  rule hasNeg((_ |-> V:Int) _) => true requires V <Int 0
  rule hasNeg(_) => false [owise]

  // recursive over a map: every value is a non-negative integer
  syntax Bool ::= allNat(Map) [function, total]
                | isNat(KItem) [function, total]
  rule allNat(.Map) => true
  rule allNat((_ |-> V) M) => isNat(V) andBool allNat(M)
  rule isNat(I:Int) => I >=Int 0
  rule isNat(_) => false [owise]

  // recursive over a cell map: the sum of the workers' counts
  syntax WorkerCellMap
  syntax Int ::= total(WorkerCellMap) [function, total]
  rule total(.WorkerCellMap) => 0
  rule total(<worker> <wid> _ </wid> <cnt> C </cnt> </worker> W) => C +Int total(W)

  rule <k> go => .K ... </k> <m> M => M[0 <- total(W)] </m> <workers> W </workers>
    requires allNat(M) andBool notBool hasNeg(M) [label(sum)]
  rule <worker> <wid> _ </wid> <cnt> C => C +Int 1 </cnt> </worker> [label(tick)]
endmodule
