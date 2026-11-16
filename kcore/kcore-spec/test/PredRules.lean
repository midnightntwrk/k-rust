/-
  Rules with predicates, each well sorted, at the conjunct `Semantics.rulePlainPP`.
  Run from the package root: `lake env lean -j1 test/PredRules.lean`. Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/symrule.kompile.kore` (as `test/ExRules.lean`):
  `a(Exp)` and `b()` of sort Exp, over the configuration `cfgE x`
  (`<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), V0)), C)`), V0 of sort K and C of the counter cell's
  sort. The rules:
  - `rNot`: `Z => G` with pre `not (and (mem Z b) (mem Z G))`, Z and G of Exp, G open: the shape of a
    complement on the left side; G is held by the right side under constructors;
  - `rOr`: `b => ?Z` with post `or (mem Z b) (mem Z a(b))`, Z existential: the shape of a connective
    on the right side; Z is held by the right side under constructors;
  - `rBad`: `b => b ensures ?Z ==Int 0`: Z of the unconfined sort Int under the hooked function
    `_==Int_` only, and in no condition: the conjunct is false.
  Each is well sorted (`ruleSorted`); `rNot` and `rOr` have the conjunct, neither has `rulePlainEx`
  (its predicates are not `\top`). `rulePlainPP_of_ex` at the definition's rules, and
  `rulePlainEx_iff_pp` at `rNot`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace PredRules

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def tA (t : Term) : Term := .app 381 [t]
def tB : Term := .app 382 []
def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(x), V0)), C)`. -/
def cfgE (x : Term) : Term := .app 71 [.app 379 [.app 0 [.inj 32 1 x, .var 0]], .var 1]

/-- The sorts of the first two variables of the text's rule: K and the counter cell's. -/
noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

example : c.symName 381 = "Lbla" ∧ c.symName 382 = "Lblb" ∧ c.sortName 32 = "Exp" := by decide +kernel

/-- `Z => G` with pre `not (and (mem Z b) (mem Z G))`. -/
noncomputable def rNot : Rule :=
  { vars := [sK, sC, 32, 32], lhs := cfgE (.var 2), req := none, rhs := cfgE (.var 3), ens := none, prio := 50,
    pre := .not (.and (.mem 32 (.var 2) tB) (.mem 32 (.var 2) (.var 3))) }

/-- `b => ?Z` with post `or (mem Z b) (mem Z a(b))`. -/
noncomputable def rOr : Rule :=
  { vars := [sK, sC, 32], lhs := cfgE tB, req := none, rhs := cfgE (.var 2), ens := none, prio := 50, exs := [2],
    post := .or (.mem 32 (.var 2) tB) (.mem 32 (.var 2) (tA tB)) }

/-- `b => b ensures ?Z ==Int 0`. -/
noncomputable def rBad : Rule :=
  { vars := [sK, sC, Srt.int], lhs := cfgE tB, req := none, rhs := cfgE tB, ens := some (.app intEq [.var 2, i 0]),
    prio := 50, exs := [2] }

/-- `rNot` is well sorted with the conjunct; G (index 3) is its only open variable, held by the
right side under constructors; its pre is not `\top`, so it has no `rulePlainEx`. -/
theorem rNot_pp : c.ruleSorted rNot = true ∧ c.rulePlainPP rNot = true ∧ rNot.opens = [3] ∧
    (ctorOccs c rNot.rhs).contains 3 = true ∧ c.rulePlainEx rNot = false := by
  decide +kernel

/-- `rOr` is well sorted with the conjunct; Z (index 2) is existential and held by the right side
under constructors; its post is not `\top`. -/
theorem rOr_pp : c.ruleSorted rOr = true ∧ c.rulePlainPP rOr = true ∧ rOr.opens = [2] ∧ rOr.exs = [2] ∧
    (ctorOccs c rOr.rhs).contains 2 = true ∧ c.rulePlainEx rOr = false := by
  decide +kernel

/-- `rBad` is well sorted, and the conjunct is false. -/
theorem rBad_pp : c.ruleSorted rBad = true ∧ c.rulePlainPP rBad = false := by
  decide +kernel

/-- `rulePlainEx_iff_pp` at `rNot`: its conjunct holds and its pre is not `\top`. -/
example : ¬ c.rulePlainEx rNot = true := fun h =>
  absurd (Semantics.rulePlainEx_iff_pp.mp h).1 (by decide +kernel)

theorem coreOK : c.coreOK = true := by decide +kernel

/-- `rulePlainPP_of_ex` at the definition's rules. -/
example : ∀ r ∈ c.rules, c.rulePlainPP r = true := fun r hr =>
  Semantics.rulePlainPP_of_ex (Semantics.rulePlainOpen_iff_ex.mp (Semantics.ruleFactsOpen_of_core coreOK r hr).2).1

end PredRules
