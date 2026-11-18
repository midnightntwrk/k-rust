/-
  KCore. The instances of a step by a rule without existential variables, for a rule whose `post`
  need not be `\top`: the pattern.

  `famEx c r σ` with `r.exs = []` is `∃v̄. (v̄ = ⟦σ⟧ ∧ rhs ∧ ⌈ens = true⌉ ∧ post)`, every variable
  fixed (`famEx_eqPP`). A condition with a binder is not `\top` (`not_isTop_of_hasBinder`), so a
  rule of `c` whose `post` has one makes `c.readsConfined` true (`readsConfined_of_post`), which
  the binder cases of the Holds lemma ask. That the instances are the successor
  (`famEx_denPPCEx`) is FamExCEx.lean's.
-/
import KcoreSpec.OpenSound
import KcoreSpec.SatRulePP
import KcoreSpec.ClausePreCore
import KcoreSpec.CondTwoTables

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder reads_of_agrees)

section
variable {c : Semantics}

/-- The pattern `famEx` reads, for a rule without existential variables, whatever its `post`:
every variable is fixed to its value under σ. -/
theorem famEx_eqPP {r : Rule} (hex : r.exs = []) (σ : Subst) :
    famEx c r σ = KoreAML.denB (KoreAML.existsAll (srtOf c topCellSort)
      ((canonVars c r.vars).map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) (fixK c r σ (List.range r.vars.length) ++
        [.and (srtOf c topCellSort) ([Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))] ++
          Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.post)]))) := by
  have hv := filterMap_range_getElem? (canonVars c r.vars)
  rw [canonVars_length] at hv
  have hf : (List.range r.vars.length).filter (fun _ => true) = List.range r.vars.length :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [famEx, ruleRight, hex, List.contains_nil, Bool.not_false, List.filterMap_nil, List.foldr_nil]
  rw [hf, hv]

/-- A condition with a binder is not `\top`. -/
theorem not_isTop_of_hasBinder {p : Cond} (h : hasBinder p = true) : p.isTop = false := by
  cases p with
  | top => exact absurd h (by simp [hasBinder])
  | _ => rfl

/-- A rule of `c` whose `post` has a binder makes `c.readsConfined` true. -/
theorem readsConfined_of_post {r : Rule} (hr : r ∈ c.rules) (hb : hasBinder r.post = true) :
    c.readsConfined = true := by
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inl ⟨r, hr, by simp [hb]⟩

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

end

end Faithful

open Faithful

end KCore
