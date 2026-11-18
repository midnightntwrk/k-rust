/-
  The executable step evaluates a rule's `pre` and `post` when they are conjunctions of `\in` and
  `\equals` atoms. Run from the package root: `lake env lean test/ExecPreAtoms.lean`.
  Kernel-checked.

  The rule `<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest </k>
  <generatedCounter> N </generatedCounter>`, X the key of `N +Int 1`, beside a rule of priority 200
  on every configuration (counter := 7); the key by `pre := X ∈ N +Int 1` (`cM`), by
  `pre := (0 <=Int N) = true ∧ X ∈ N +Int 1` (`cC`), or by `post := X ∈ N +Int 1` (`cP`).
  Each core is `execReady`. At `<k> 1 ~> . </k> 0` (1 is the value of `0 +Int 1`) the rule with the
  key steps; at `<k> 5 ~> . </k> 0` its `pre` is false, so it does not block the rule of priority
  200, which steps (`cM`, `cC`); with the key in `post`, the rule blocks it there and has no
  successor. Nothing runs out of fuel, so these lists are exactly the `Step` successors
  (`CExec.step_iff_at`, `FnDet` of a core without user functions), and `CExec.run_exact` applies.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ExecPreAtomsTest

open GroundTerm Faithful
open Faithful.UndefRhsWitness (kIds cellSorts cellCtors cellSubsorts)

def lhsK : Term :=
  .app topLabel [.app kIds.label [.app kseq [.inj Srt.int Srt.kitem (.var 2), .var 0]], .app counterLabel [.var 1]]
def rhsK : Term := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]]
/-- `N +Int 1` -/
def fN : Term := .app intAdd [.var 1, .dv Srt.int (.int 1)]

/-- `pre := X ∈ N +Int 1` -/
def kcMem : Rule :=
  { vars := [Srt.k, Srt.int, Srt.int], lhs := lhsK, req := none, rhs := rhsK, ens := none, prio := 50,
    pre := .mem Srt.int (.var 2) fN }

/-- `pre := (0 <=Int N) = true ∧ X ∈ N +Int 1` -/
def kcConj : Rule :=
  { kcMem with
    pre := .and (.equals Srt.bool (.app intLe [.dv Srt.int (.int 0), .var 1]) (.dv Srt.bool (.bool true)))
      (.mem Srt.int (.var 2) fN) }

/-- `<k> K </k> <generatedCounter> N </generatedCounter> => <k> K </k> <generatedCounter> 7 </generatedCounter>` -/
def r200 : Rule :=
  { vars := [Srt.k, Srt.int], lhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.var 1]],
    req := none, rhs := .app topLabel [.app kIds.label [.var 0], .app counterLabel [.dv Srt.int (.int 7)]],
    ens := none, prio := 200 }

def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def cM : Semantics := { base with rules := [kcMem, r200] }
def cC : Semantics := { base with rules := [kcConj, r200] }
/-- `post := X ∈ N +Int 1` (the right side's predicate) in place of `pre`. -/
def kcPost : Rule := { kcMem with pre := .top, post := .mem Srt.int (.var 2) fN }
def cP : Semantics := { base with rules := [kcPost, r200] }

/-- `<k> x ~> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfgK (x n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kIds.label [.ctor kseq [.inj Srt.int Srt.kitem (int x), .ctor dotk []]], .ctor counterLabel [int n]]
/-- `<k> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfg0 (n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kIds.label [.ctor dotk []], .ctor counterLabel [int n]]

theorem ready : CExec.execReady cM = true ∧ CExec.execReady cC = true ∧ CExec.execReady cP = true := by
  decide +kernel

theorem coreM : cM.coreOK = true := by decide_cheap

theorem coreC : cC.coreOK = true := by decide_cheap

theorem coreP : cP.coreOK = true := by decide_cheap

theorem core : cM.coreOK = true ∧ cC.coreOK = true ∧ cP.coreOK = true := ⟨coreM, coreC, coreP⟩

/-- What the executable step lists, at fuel 20, nothing out of fuel. -/
theorem listed :
    CExec.successorsN cM 20 (cfgK 1 0) = [cfg0 0] ∧ CExec.outOfFuel cM 20 (cfgK 1 0) = false ∧
    CExec.successorsN cM 20 (cfgK 5 0) = [cfgK 5 7] ∧ CExec.outOfFuel cM 20 (cfgK 5 0) = false ∧
    CExec.successorsN cC 20 (cfgK 1 0) = [cfg0 0] ∧ CExec.outOfFuel cC 20 (cfgK 1 0) = false ∧
    CExec.successorsN cC 20 (cfgK 5 0) = [cfgK 5 7] ∧ CExec.outOfFuel cC 20 (cfgK 5 0) = false ∧
    CExec.successorsN cP 20 (cfgK 1 0) = [cfg0 0] ∧ CExec.outOfFuel cP 20 (cfgK 1 0) = false ∧
    CExec.successorsN cP 20 (cfgK 5 0) = [] ∧ CExec.outOfFuel cP 20 (cfgK 5 0) = false := by
  decide +kernel

theorem sorts (d : Semantics) (hd : d = cM ∨ d = cC ∨ d = cP) :
    d.sortOf (cfgK 1 0) = some topCellSort ∧ d.sortOf (cfg0 0) = some topCellSort ∧
    d.sortOf (cfgK 5 0) = some topCellSort ∧ d.sortOf (cfgK 5 7) = some topCellSort := by
  rcases hd with rfl | rfl | rfl <;> decide +kernel

/-- No user function, and the sort predicates' clauses agree: one result at most. -/
theorem fnDet (d : Semantics) (hd : d.fns = []) : FnDet d :=
  fnDet_of_agree (fun _ h => by rw [hd] at h; cases h) (fun _ h => by rw [hd] at h; cases h)

theorem noFns : cM.fns = [] ∧ cC.fns = [] ∧ cP.fns = [] := ⟨rfl, rfl, rfl⟩

/-- **The rule with the key in `pre` steps at `<k> 1 ~> . </k> 0`**, read off the step. -/
theorem stepM_A : Step cM ⟨cfgK 1 0, (sorts cM (.inl rfl)).1⟩ ⟨cfg0 0, (sorts cM (.inl rfl)).2.1⟩ :=
  (CExec.successorsN_step_ready ready.1 (n := 20) (by rw [listed.1]; exact List.mem_singleton_self _)).2

/-- **At `<k> 5 ~> . </k> 0` the step lists exactly the `Step` successors**: the rule of priority
200's, which the rule with the key does not block. -/
theorem exactM_B (y : Config cM) :
    Step cM ⟨cfgK 5 0, (sorts cM (.inl rfl)).2.2.1⟩ y ↔ y.val = cfgK 5 7 := by
  refine (CExec.step_iff_at (x := ⟨cfgK 5 0, (sorts cM (.inl rfl)).2.2.1⟩) ready.1 (fnDet cM noFns.1)
    listed.2.2.2.1).trans ?_
  rw [listed.2.2.1]
  simp

theorem exactC_B (y : Config cC) :
    Step cC ⟨cfgK 5 0, (sorts cC (.inr (.inl rfl))).2.2.1⟩ y ↔ y.val = cfgK 5 7 := by
  refine (CExec.step_iff_at (x := ⟨cfgK 5 0, (sorts cC (.inr (.inl rfl))).2.2.1⟩) ready.2.1
    (fnDet cC noFns.2.1) listed.2.2.2.2.2.2.2.1).trans ?_
  rw [listed.2.2.2.2.2.2.1]
  simp

/-- **With the key in `post`, the rule applies at `<k> 5 ~> . </k> 0` and blocks the rule of
priority 200, but its `post` is false there: no successor.** -/
theorem exactP_B (y : Config cP) :
    ¬ Step cP ⟨cfgK 5 0, (sorts cP (.inr (.inr rfl))).2.2.1⟩ y :=
  CExec.noStep_at ready.2.2 (fnDet cP noFns.2.2) listed.2.2.2.2.2.2.2.2.2.2.2 listed.2.2.2.2.2.2.2.2.2.2.1 y

/-- **`run_exact` at a core whose rule has a `pre`.** -/
example : ((Γ cM ∪ Γstep cM) ⊧ (den cM (cfgK 5 0) ⇒
      KoreAML.allNext (KoreAML.disjList ((CExec.successorsN cM 20 (cfgK 5 0)).map (den cM))))) ∧
    ∀ y ∈ CExec.successorsN cM 20 (cfgK 5 0), Γ cM ⊧ (den cM (cfgK 5 0) ⇒ KoreAML.sNext (den cM y)) :=
  CExec.run_exact (x := ⟨cfgK 5 0, (sorts cM (.inl rfl)).2.2.1⟩) core.1 ready.1 (fnDet cM noFns.1)
    listed.2.2.2.1

end ExecPreAtomsTest

end KCore

#print axioms KCore.ExecPreAtomsTest.ready
#print axioms KCore.ExecPreAtomsTest.core
#print axioms KCore.ExecPreAtomsTest.fnDet
#print axioms KCore.ExecPreAtomsTest.listed
#print axioms KCore.ExecPreAtomsTest.stepM_A
#print axioms KCore.ExecPreAtomsTest.exactM_B
#print axioms KCore.ExecPreAtomsTest.exactC_B
#print axioms KCore.ExecPreAtomsTest.exactP_B
