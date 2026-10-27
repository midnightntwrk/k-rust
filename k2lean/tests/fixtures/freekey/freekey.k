// Function equations with a free-key map pattern `K |-> V REST` (crates/k2lean/tests/snapshots.rs):
// such an equation applies at the first binding, in the map's order, at which the rest of its
// left-hand side and its requires hold (k2lean/docs/design.md, section 2, "Functions").
requires "domains.md"

module FREEKEY-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go" | "check" | "go2" | "go3"
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
      <jobs>
        <job multiplicity="*" type="Map">
          <jid> 0 </jid> <owner> 0 </owner> <prio> 0 </prio> <ctl> <lo> 0 </lo> <hi> 0 </hi> </ctl> <done> false </done>
        </job>
      </jobs>
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

  // two free keys (lexicographic choice): two positive values; the instances agree (`true`)
  syntax Bool ::= twoPos(Map) [function, total]
  rule twoPos((_ |-> V1:Int) (_ |-> V2:Int) _) => true requires V1 >Int 0 andBool V2 >Int 0
  rule twoPos(_) => false [owise]

  // partial, with instances that disagree on a map with two positive values: K's axioms determine
  // no value there (`anyPos.Agrees` is false), and the definition takes the least key's
  syntax Int ::= anyPos(Map) [function]
  rule anyPos((_ |-> V:Int) _) => V requires V >Int 0

  // recursive, after a guard-only equation whose negation the termination proof reads (the
  // cascade names it): the sum of at most N values
  syntax Int ::= takeSum(Int, Map) [function]
  rule takeSum(N, _) => 0 requires N <=Int 0
  rule takeSum(N, (_ |-> V:Int) R) => V +Int takeSum(N -Int 1, R)

  // recursive over a cell map: the sum of the workers' counts
  syntax WorkerCellMap
  syntax Int ::= total(WorkerCellMap) [function, total]
  rule total(.WorkerCellMap) => 0
  rule total(<worker> <wid> _ </wid> <cnt> C </cnt> </worker> W) => C +Int total(W)

  // recursive over a cell map whose element has five cells, one of them nested, each bound by its
  // own variable or `_` (the shape of SIMPLE's `<thread>`): every job's bounds are ordered
  syntax Bool ::= jobsOk(JobsCell) [function, total]
  rule jobsOk(<jobs> .Bag </jobs>) => true
  rule jobsOk(<jobs> <job> <jid> _ </jid> <owner> _ </owner> <prio> _ </prio> <ctl> <lo> L </lo> <hi> H </hi> </ctl>
                           <done> _ </done> </job> Js </jobs>)
    => L <=Int H andBool jobsOk(<jobs> Js </jobs>)

  rule <k> go => .K ... </k> <m> M => M[0 <- total(W)] </m> <workers> W </workers>
    requires allNat(M) andBool notBool hasNeg(M) [label(sum)]
  rule <worker> <wid> _ </wid> <cnt> C => C +Int 1 </cnt> </worker> [label(tick)]
  rule <k> go2 => .K ... </k> <m> M => M[2 <- takeSum(3, M)] </m> [label(take)]
  rule <k> go3 => .K ... </k> <m> M => M[3 <- 1] </m> JS:JobsCell requires jobsOk(JS) [label(jobs)]
  rule <k> check => .K ... </k> <m> M => M[1 <- anyPos(M)] </m> requires twoPos(M) [label(check)]
endmodule
