/-
  The ok track's readiness condition without the `\top` shape (`Semantics.okM`). Run from the
  package root: `lake env lean test/OkM.lean`. Kernel-checked.

  The rule `<k> X:Int ~> Rest </k> <generatedCounter> N </generatedCounter> => <k> Rest </k>
  <generatedCounter> N </generatedCounter>` with `pre := X ∈ N +Int 1`, beside a rule of priority
  200 on every configuration (`cM`): `okM` accepts it and `ok` does not, its `pre` not being `\top`
  (`okM_not_ok`); the same rule with no `pre` (`cT`) is accepted by both (`ok_top`). The accessors
  over `okM` and the general progress lemma read at `cM` (`sortCtxM`, `progressM`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace OkMTest

open GroundTerm
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
def cT : Semantics := { base with rules := [{ kcMem with pre := .top }, r200] }

/-- **`okM` true and `ok` false at a core whose rule has a predicate.** -/
theorem okM_not_ok : cM.okM = true ∧ cM.ok = false ∧ cM.okAll = true ∧ kcMem.pre.isTop = false := by
  decide +kernel

theorem ok_top : cT.ok = true ∧ cT.okM = true := by decide +kernel

theorem srReady : cM.srReady = true := by decide +kernel

/-- The accessors over `okM` at `cM`. -/
theorem sortCtxM : SortCtx cM := sortCtx_of_okM okM_not_ok.1 srReady (Semantics.ovlCase_of (by decide +kernel))

example : ∀ r ∈ cM.rules, ∃ s, sortOfTerm cM.patCtx r.vars r.lhs = some s := lhs_sorted_of_okM okM_not_ok.1
example : Exec.ClauseCtx cM := Exec.clauseCtx_of_okM okM_not_ok.1
example : cM.subsortsOK = true := NamesApart.okM_subsortsOK okM_not_ok.1
example : kcMem.exs = [] ∧ binds kcMem.vars.length (varOccs kcMem.lhs) = true :=
  Semantics.okM_rule okM_not_ok.1 (List.mem_cons_self ..)
example : (cM.withHooks HookParams.none).okM = true := (Semantics.okM_withHooks cM _).trans okM_not_ok.1

/-- **Progress by the rule with a `pre`**, from the general form over `okAll`. -/
theorem progressM {x : Config cM} {σ : Subst} (hσ : cM.WellSorted kcMem.vars σ) (hm : PatVal cM σ kcMem.lhs x.val)
    (hpre : Holds cM kcMem.vars.length σ kcMem.pre true) {v : GroundTerm} (he : EvalTerm cM σ kcMem.rhs (some v)) :
    Reachability.Progress (Step cM) x :=
  Step.progress_of_rule_all (i := 0) (Semantics.okAll_of_okM okM_not_ok.1) srReady rfl hσ hm
    (fun t h => by cases h) hpre (fun r' hr' hlt => by
      simp only [cM, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact absurd hlt (by decide))
    he (fun t h => by cases h) .top

end OkMTest

end KCore

#print axioms KCore.OkMTest.okM_not_ok
#print axioms KCore.OkMTest.ok_top
#print axioms KCore.OkMTest.sortCtxM
#print axioms KCore.OkMTest.progressM
