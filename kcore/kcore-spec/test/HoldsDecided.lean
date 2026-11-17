/-
  A well-sorted condition has a truth value (`Faithful.holds_decided`), and a step by a well-sorted
  rule with any predicates reads evaluations with results (`Faithful.Rule.decided_pp`,
  `Faithful.stepDecided_pp`). Run from the package root: `lake env lean -j1 test/HoldsDecided.lean`.

  - The landed `Rule.decided_of_total` and `stepDecided_of_rules` are `Rule.decided_pp` and
    `stepDecided_pp` under `rulePlainOpen`, by terms.
  - At the reader's semantics for `f2-examples/symrule.kompile.kore` (`coreOK` by `decide +kernel`),
    under `FnTerminates`: a closed `∀B:Bool. B ==Bool B` and a closed `∃Z:Int. Z = 0` have truth
    values (the second over the unconfined sort Int: no list of its values is read), and a rule
    `a() => a()` with the premise `∃B:Bool. B = true` (`ruleSorted` by `decide +kernel`) has the
    results `StepDecided` asks at every configuration.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore Faithful

namespace HoldsDecided

/-- The landed lemmas are the instances under `rulePlainOpen`. -/
example : type_of% @Faithful.Rule.decided_of_total := fun h hft _ hs _ x => Rule.decided_pp h hft hs x
example : type_of% @Faithful.stepDecided_of_rules :=
  fun h hft hr x => stepDecided_pp h hft (fun r m => (hr r m).1) x

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide +kernel

/-- `∀B:Bool. B ==Bool B`, closed. -/
def pAll : Cond := .all Srt.bool (.equals Srt.bool (.var 0) (.var 0))
/-- `∃Z:Int. Z = 0`, closed. -/
def pEx : Cond := .ex Srt.int (.equals Srt.int (.var 0) (.dv Srt.int (.int 0)))

example (hft : FnTerminates c) :
    (∃ b, Holds c 0 [] pAll b) ∧ (∃ b, Holds c 0 [] pEx b) := by
  have hv : varOccsCond 0 pAll = [] ∧ varOccsCond 0 pEx = [] := by decide +kernel
  have hok : c.condOK [] pAll = true ∧ c.condOK [] pEx = true := by decide +kernel
  refine ⟨holds_decided (hypSound_of_core coreOK) hft pAll hok.1 ?_,
    holds_decided (hypSound_of_core coreOK) hft pEx hok.2 ?_⟩
  · rw [List.length_nil, hv.1]; intro i hi; cases hi
  · rw [List.length_nil, hv.2]; intro i hi; cases hi

/-- The sorts of the first two variables of the text's rule: K and the counter cell's. -/
noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

/-- `a() => a()` with the premise `∃B:Bool. B = true`. -/
noncomputable def rPre : Rule :=
  { vars := [sK, sC], lhs := cfg (.var 1), req := none, rhs := cfg (.var 1), ens := none, prio := 50, exs := [],
    pre := .ex Srt.bool (.equals Srt.bool (.var 2) (.dv Srt.bool (.bool true))) }

theorem rPre_sorted : c.ruleSorted rPre = true ∧ rPre.pre.isTop = false := by decide +kernel

example (hft : FnTerminates c) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt rPre.vars rPre.leftVars σ → PatVal c σ rPre.lhs x →
      (∀ t, rPre.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c rPre.vars.length σ rPre.pre b) ∧
    (∀ σ, c.WellSorted rPre.vars σ → PatVal c σ rPre.lhs x →
      (∀ t, rPre.req = some t → EvalTerm c σ t (some (bool true))) → Holds c rPre.vars.length σ rPre.pre true →
        (∃ v, EvalTerm c σ rPre.rhs v) ∧ (∀ e, rPre.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c rPre.vars.length σ rPre.post b) :=
  Rule.decided_pp (hypSound_of_core coreOK) hft rPre_sorted.1 x

end HoldsDecided
