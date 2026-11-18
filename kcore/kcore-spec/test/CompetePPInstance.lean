/-
  A kernel instance of `Faithful.not_applies_of_notApplies_heldCEx` and
  `Faithful.notApplies_of_not_applies_ppCEx`: a rule with a `pre` that has a rule of a larger
  priority beside it, in a core `coreOK` accepts. Run from the package root:
  `lake env lean test/CompetePPInstance.lean`. Kernel-checked.

  The rule `kcMem`: `<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest
  </k> <generatedCounter> N </generatedCounter>` with `pre := X ∈ N +Int 1` (X the key of
  `N +Int 1`), priority 50, beside `r200`, a rule of priority 200 on every configuration. Every
  hypothesis of the two lemmas is a decided fact of the core (`facts`) or read off the executable
  step (`CExec.notApplies_of_ruleMatches`, `CExec.stepDecided_of_fuel`, `CExec.applies_of_ruleMatches`),
  and the variable table is the left side's keys and `pre`'s variables. In every model of `Γc cM`:
  at `<k> 5 ~> . </k> 0`, where `pre` is false (`0 +Int 1` is 1), the configuration's element is
  outside the rule's `applies` pattern (`not_applies_B`); at `<k> 1 ~> . </k> 0`, where `pre` holds,
  it is inside it (`applies_A`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace CompetePPInstanceTest

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
/-- `<k> x ~> . </k> <generatedCounter> n </generatedCounter>`. -/
def cfgK (x n : Int) : GroundTerm :=
  .ctor topLabel [.ctor kIds.label [.ctor kseq [.inj Srt.int Srt.kitem (int x), .ctor dotk []]], .ctor counterLabel [int n]]

theorem coreM : cM.coreOK = true := by decide_cheap

/-- What the two lemmas ask of the core and of the rule, decided (`coreOK` by `coreM`). -/
theorem facts : cM.coreOK = true ∧ cM.ruleSorted kcMem = true ∧ cM.rulePlainPP kcMem = true ∧
    cM.rules.any (fun r'' => kcMem.prio < r''.prio) = true ∧
    (kcMem.opens.any fun i => (kcMem.vars[i]?.map cM.confined).getD false) = false ∧
    kcMem.pre.hasBinder = false ∧ kcMem.needsWitness cM = false ∧ cM.fns = [] ∧
    CExec.execReady cM = true ∧ kcMem.pre.isTop = false :=
  ⟨coreM, by decide +kernel⟩

theorem mem : kcMem ∈ cM.rules := List.mem_cons_self ..

theorem sortA : cM.sortOf (cfgK 1 0) = some topCellSort := by decide +kernel
theorem sortB : cM.sortOf (cfgK 5 0) = some topCellSort := by decide +kernel

/-- The executable step at fuel 20: at `<k> 5 ~> . </k> 0` every match of the rule has `pre`
false; at `<k> 1 ~> . </k> 0` its match applies; nothing ran out of fuel at either. -/
theorem listed : (∀ σb ∈ CExec.ruleMatches cM 20 kcMem (cfgK 5 0), σb.2 = some false) ∧
    CExec.outOfFuel cM 20 (cfgK 5 0) = false ∧
    (∃ σb ∈ CExec.ruleMatches cM 20 kcMem (cfgK 1 0), σb.2 = some true) ∧
    CExec.outOfFuel cM 20 (cfgK 1 0) = false := by
  decide +kernel

/-- No user function, and the sort predicates' clauses agree: one result at most. -/
theorem fnDet : FnDet cM :=
  fnDet_of_agree (fun _ h => by rw [facts.2.2.2.2.2.2.2.1] at h; cases h)
    (fun _ h => by rw [facts.2.2.2.2.2.2.2.1] at h; cases h)

/-- **The rule does not apply at `<k> 5 ~> . </k> 0`**: its `pre` is false under every match. -/
theorem notApplies_B : NotApplies cM kcMem (cfgK 5 0) :=
  CExec.notApplies_of_ruleMatches (x := ⟨cfgK 5 0, sortB⟩) facts.2.2.2.2.2.2.2.2.1 mem listed.1

/-- **It applies at `<k> 1 ~> . </k> 0`.** -/
theorem applies_A : ¬ NotApplies cM kcMem (cfgK 1 0) := by
  obtain ⟨⟨σ, b⟩, hm, hb⟩ := listed.2.2.1
  simp only at hb
  subst hb
  exact CExec.not_notApplies_of_ruleMatches (x := ⟨cfgK 1 0, sortA⟩) facts.2.2.2.2.2.2.2.2.1 fnDet mem hm

/-- The variable table: the keys of the rule's variables and the variables of `pre`'s pattern. -/
def tbl : KoreAML.VarTable :=
  (List.range kcMem.vars.length).map (canonKey cM kcMem.vars) ++
    KoreAML.varsOf (Cond.kore cM (canonVars cM kcMem.vars) (srtOf cM topCellSort) kcMem.pre)

theorem hkeys : ∀ i < kcMem.vars.length, i ∈ kcMem.leftVars → canonKey cM kcMem.vars i ∈ tbl :=
  fun i hi _ => List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore cM (canonVars cM kcMem.vars) (srtOf cM topCellSort) kcMem.pre),
    k ∈ tbl :=
  fun _ hk => List.mem_append_right _ hk

theorem hcw : ∀ fn ∈ cM.fns, ∀ cl ∈ fn.clauses, cl.needsWitness cM = true → cl.CondDecided cM :=
  fun fn hfn => by rw [facts.2.2.2.2.2.2.2.1] at hfn; cases hfn

/-- The first conjunct of `StepDecided` at the rule, at both configurations. -/
theorem decided (x : Config cM) (hf : CExec.outOfFuel cM 20 x.val = false) :
    ∀ σ, cM.WellSortedAt kcMem.vars kcMem.leftVars σ → PatVal cM σ kcMem.lhs x.val →
      (∀ t, kcMem.req = some t → ∃ v, EvalTerm cM σ t v) ∧ ∃ b, Holds cM kcMem.vars.length σ kcMem.pre b :=
  (CExec.stepDecided_of_fuel facts.2.2.2.2.2.2.2.2.1 fnDet hf kcMem mem
    (fun r' hr' hlt => by
      simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact absurd hlt (by decide))).1

section
variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- The left side of `kcMem` binds each of its variables, so the rule has `rulePlainHeldH` at the
empty set of symbols. -/
theorem heldM : cM.rulePlainHeldH (fun _ => false) kcMem = true :=
  Semantics.rulePlainHeldH_of_opens_nil _ (by decide +kernel)

/-- **`not_applies_of_notApplies_heldCEx` at `kcMem`, every hypothesis discharged**: in a model of
`Γc cM`, `<k> 5 ~> . </k> 0`'s element is outside the rule's `applies` pattern. -/
theorem not_applies_B (hI : I ⊧ᴵP Γc cM) (e : ML.Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies cM kcMem (canonRulePres kcMem))).interpret I e (elemOf cM I (cfgK 5 0)) :=
  not_applies_of_notApplies_heldCEx (x := ⟨cfgK 5 0, sortB⟩) (Semantics.coreOKEx_of_coreOK facts.1) hI hcw
    (fun _ _ _ hH => absurd hH (by decide)) facts.2.1 heldM facts.2.2.2.1
    (fun h => absurd h (by rw [facts.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [facts.2.2.2.2.2.1]; decide))
    (fun h => absurd h (by rw [facts.2.2.2.2.2.2.1]; decide))
    notApplies_B hkeys hkP e

/-- **The two directions at `kcMem`, every hypothesis discharged**, at both configurations: outside
the `applies` pattern at `<k> 5 ~> . </k> 0`, inside it at `<k> 1 ~> . </k> 0`
(`notApplies_of_not_applies_ppCEx`). -/
theorem applies_iff_AB (hI : I ⊧ᴵP Γc cM) (e : ML.Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies cM kcMem (canonRulePres kcMem))).interpret I e (elemOf cM I (cfgK 5 0)) ∧
    (KoreAML.tr ⟨tbl, []⟩ (applies cM kcMem (canonRulePres kcMem))).interpret I e (elemOf cM I (cfgK 1 0)) :=
  ⟨not_applies_B hI e, Classical.byContradiction fun h => applies_A
    (notApplies_of_not_applies_ppCEx (x := ⟨cfgK 1 0, sortA⟩) (Semantics.coreOKEx_of_coreOK facts.1) hI hcw facts.2.1
      (fun h => absurd h (by rw [facts.2.2.2.2.2.1]; decide)) (decided ⟨cfgK 1 0, sortA⟩ listed.2.2.2) hkeys hkP e h)⟩

end

end CompetePPInstanceTest

end KCore

#print axioms KCore.CompetePPInstanceTest.coreM
#print axioms KCore.CompetePPInstanceTest.facts
#print axioms KCore.CompetePPInstanceTest.fnDet
#print axioms KCore.CompetePPInstanceTest.notApplies_B
#print axioms KCore.CompetePPInstanceTest.applies_A
#print axioms KCore.CompetePPInstanceTest.not_applies_B
#print axioms KCore.CompetePPInstanceTest.applies_iff_AB
