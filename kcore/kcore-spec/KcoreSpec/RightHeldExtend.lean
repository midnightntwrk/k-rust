/-
  KCore. A substitution well sorted on the variables of a clause's patterns and conditions extends
  to every variable of the clause, where each other variable is of a sort with a value.

  `Fails` and `Clause.DecidesAt` range over substitutions well sorted on `leftVars`, `Eval.clause`
  and `Clause.AppliesAt` over substitutions well sorted on every variable. Under `HeldAt` (each
  variable in `leftVars` or of a sort with a value; `Semantics.RightHeld` gives it of every clause
  of the definition's functions) the first give the second (`Semantics.extendHeld`), agreeing on
  `leftVars`. Matching and evaluation read a substitution at the term's variables only
  (`PatVal.congr_varsRH`, `PatVals.congr_varsRH`; for `EvalTerm`, `Exec.EvalTerm.congr`), and the
  patterns and the `requires` have their variables in `leftVars`, so a match with a `requires`
  true under the first is one under the extension (`Clause.appliesAt_extendRH`, HoldsCongr.lean,
  which reads the clause's predicate at `leftVars` too).
-/
import KcoreSpec.RightHeld
import KcoreSpec.EvalFunctionalDefs

set_option autoImplicit false

namespace KCore

/-! ## Matching reads a substitution at the pattern's variables only -/

mutual
  /-- Matching reads σ at the pattern's variables only. -/
  theorem PatVal.congr_varsRH {c : Semantics} {σ σ' : Subst} : ∀ {p : Term} {v : GroundTerm}, PatVal c σ p v →
      (∀ j ∈ varOccs p, σ'.lookup j = σ.lookup j) → PatVal c σ' p v
    | .var j, v, h, ha => by
      cases h with
      | var h => exact .var (by rw [ha j (by simp [varOccs]), h])
    | .dv s l, v, h, _ => by cases h; exact .dv
    | .app f ps, v, h, ha => by
      have ha' : ∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j := fun j hj => ha j (by simpa [varOccs] using hj)
      cases h with
      | ctor hc hs => exact .ctor hc (PatVals.congr_varsRH hs ha')
      | hook hp hs hv => exact .hook hp (PatVals.congr_varsRH hs ha') hv
      | coll hc hp hs hv => exact .coll hc hp (PatVals.congr_varsRH hs ha') hv
      | ovl hc ho hs hv => exact .ovl hc ho (PatVals.congr_varsRH hs ha') hv
    | .inj a b p, v, h, ha => by
      cases h with
      | inj h => exact .inj (PatVal.congr_varsRH h fun j hj => ha j (by simpa [varOccs] using hj))
    | .as p i, v, h, ha => by
      cases h with
      | as h hi =>
        exact .as (PatVal.congr_varsRH h fun j hj => ha j (by simp [varOccs, hj]))
          (by rw [ha i (by simp [varOccs]), hi])
    termination_by structural p => p
  /-- Matching a list of patterns reads σ at their variables only. -/
  theorem PatVals.congr_varsRH {c : Semantics} {σ σ' : Subst} : ∀ {ps : List Term} {vs : List GroundTerm},
      PatVals c σ ps vs → (∀ j ∈ varOccsList ps, σ'.lookup j = σ.lookup j) → PatVals c σ' ps vs
    | [], vs, h, _ => by cases h; exact .nil
    | p :: ps, vs, h, ha => by
      cases h with
      | cons h hs =>
        exact .cons (PatVal.congr_varsRH h fun j hj => ha j (by simp [varOccsList, hj]))
          (PatVals.congr_varsRH hs fun j hj => ha j (by simp [varOccsList, hj]))
    termination_by structural ps => ps
end

/-! ## The extension step -/

/-- Each variable of `vars` outside `L` is of a sort with a value. -/
def Semantics.HeldAt (c : Semantics) (vars : List Srt) (L : List Nat) : Prop :=
  ∀ i s, vars[i]? = some s → i ∈ L ∨ ∃ v, c.sortOf v = some s

/-- `RightHeld` gives `HeldAt` of each clause of the definition's functions, on its `leftVars`. -/
theorem Semantics.RightHeld.heldAt {c : Semantics} (h : c.RightHeld) {f : Fn} (hf : f ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ f.clauses) : c.HeldAt cl.vars cl.leftVars :=
  h f hf cl hcl

theorem Semantics.extendHeld_aux {c : Semantics} {vars : List Srt} {L : List Nat} (hh : c.HeldAt vars L)
    (σ : Subst) :
    ∀ js : List Nat, ∃ σ' : Subst, (∀ i ∈ L, σ'.lookup i = σ.lookup i) ∧
      ∀ i ∈ js, i ∉ L → ∀ s, vars[i]? = some s → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some s
  | [] => ⟨σ, fun _ _ => rfl, fun _ h => nomatch h⟩
  | j :: js => by
    obtain ⟨σ', h1, h2⟩ := Semantics.extendHeld_aux hh σ js
    by_cases hj : j ∈ L
    · exact ⟨σ', h1, fun i hi hiL s hs => by
        rcases List.mem_cons.mp hi with rfl | hi
        · exact absurd hj hiL
        · exact h2 i hi hiL s hs⟩
    · cases hv : vars[j]? with
      | none => exact ⟨σ', h1, fun i hi hiL s hs => by
          rcases List.mem_cons.mp hi with rfl | hi
          · rw [hv] at hs; cases hs
          · exact h2 i hi hiL s hs⟩
      | some t =>
        rcases hh j t hv with hjL | ⟨v, hsv⟩
        · exact absurd hjL hj
        · refine ⟨(j, v) :: σ', fun i hi => ?_, fun i hi hiL s hs => ?_⟩
          · have hne : (i == j) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; rintro rfl; exact hj hi
            simp only [List.lookup, hne]; exact h1 i hi
          · by_cases hij : i = j
            · subst hij
              rw [hv] at hs; cases hs
              exact ⟨v, by simp [List.lookup], hsv⟩
            · have hne : (i == j) = false := by simpa using hij
              rcases List.mem_cons.mp hi with rfl | hi
              · exact absurd rfl hij
              · simp only [List.lookup, hne]; exact h2 i hi hiL s hs

/-- **A substitution well sorted on `L` extends to every variable** where each other variable is of
a sort with a value, agreeing on `L`. -/
theorem Semantics.extendHeld {c : Semantics} {vars : List Srt} {L : List Nat} (hh : c.HeldAt vars L) {σ : Subst}
    (hσ : c.WellSortedAt vars L σ) :
    ∃ σ', c.WellSorted vars σ' ∧ ∀ i ∈ L, σ'.lookup i = σ.lookup i := by
  obtain ⟨σ', h1, h2⟩ := Semantics.extendHeld_aux hh σ (List.range vars.length)
  refine ⟨σ', fun i s hs => ?_, h1⟩
  by_cases hi : i ∈ L
  · obtain ⟨v, hv, hsv⟩ := hσ i hi s hs
    exact ⟨v, (h1 i hi).trans hv, hsv⟩
  · have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hs).1
    exact h2 i (List.mem_range.mpr hlt) hi s hs

/-- The variables of a clause's `requires` are among those of its patterns and conditions. -/
theorem Clause.req_leftVarsRH {cl : Clause} {t : Term} (ht : cl.req = some t) : ∀ i ∈ varOccs t, i ∈ cl.leftVars :=
  fun i hi => List.mem_append_right _ (List.mem_append_left _ (by rw [ht]; exact hi))

/-- Where a clause's patterns bind every variable, each variable is in `leftVars`. -/
theorem Semantics.heldAt_of_bindsRH {c : Semantics} {cl : Clause}
    (hb : binds cl.vars.length (varOccsList cl.pats) = true) : c.HeldAt cl.vars cl.leftVars := by
  intro i s hs
  have hi : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  exact Or.inl (List.mem_append_left _ (List.contains_iff_mem.mp (List.all_eq_true.mp hb i (List.mem_range.mpr hi))))

/-! ## The held variables of one function -/

/-- Each variable of each clause of `fn` is in the clause's `leftVars` or of a sort with a value
(`HeldAt` of each clause: what `RightHeld` states of every function, of the one). -/
def Semantics.HeldFn (c : Semantics) (fn : Fn) : Prop :=
  ∀ cl ∈ fn.clauses, c.HeldAt cl.vars cl.leftVars

/-- `RightHeld` gives `HeldFn` of each of the definition's functions. -/
theorem Semantics.RightHeld.heldFn {c : Semantics} (h : c.RightHeld) {f : Fn} (hf : f ∈ c.fns) : c.HeldFn f :=
  fun _ hcl => h.heldAt hf hcl

/-- A clause `clauseValued` accepts has `HeldAt`: a variable outside `leftVars` is of a sort
`valued` accepts, which has a value (`valued_value`). -/
theorem Semantics.heldAt_of_clauseValued {c : Semantics} {cl : Clause} (h : c.clauseValued cl = true) :
    c.HeldAt cl.vars cl.leftVars := by
  intro i s hs
  have hi : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hs, Bool.or_eq_true, List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Semantics.valued_value h1)

/-- **A function that is not held-named has `HeldFn`**, decided on the data. -/
theorem Semantics.heldFn_of_not_named {c : Semantics} {fn : Fn} (hfn : fn ∈ c.fns)
    (hn : fn.label ∉ c.heldObligations) : c.HeldFn fn := by
  cases h : fn.clauses.all c.clauseValued
  · exact absurd (List.mem_map.mpr ⟨fn, List.mem_filter.mpr ⟨hfn, by simp [h]⟩, rfl⟩) hn
  · exact fun cl hcl => Semantics.heldAt_of_clauseValued (List.all_eq_true.mp h cl hcl)

end KCore
