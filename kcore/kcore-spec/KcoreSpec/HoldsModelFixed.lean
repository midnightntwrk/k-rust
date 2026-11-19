/-
  KCore. A condition in the value model at a transition T, with a binder of a sort that is not
  confined.

  `Cond.boundV c val` (BoundConf.lean) is `Cond.boundConf c` with one more case at an `ex` binder: a
  sort that `val` admits, whose variable the body fixes (`Cond.fixes`) by a term over the other
  variables; `Cond.bound c` is it at `Semantics.valued` (`Cond.bound_eq_boundV`).

  In the value model every element of a numbered sort is a value's, so the Holds lemma's recursion
  (`HoldsShape.holds_denB`) reads `Cond.boundV c val` there for every `val` that admits numbered
  sorts only (`boundReads_boundV_stdI`, HoldsModel.lean): the binder over the elements of the sort
  is the binder over its values, and nothing is read of the body fixing the variable.
  - `holds_atT_fixed`: `Model.holds_atT` with `Cond.boundV c val` for `Cond.bound c`;
  - `holds_stdI_fixed`: `holds_stdI` likewise: where the condition has a truth value, it holds at an
    element of a numbered predicate sort exactly where that value is `true`.
-/
import KcoreSpec.HoldsModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-- **A condition in the value model at T, over `Cond.boundV`**: `holds_atT` with `Cond.boundV c val`
for `Cond.bound c`, `val` admitting numbered sorts only. -/
theorem holds_atT_fixed (h : HypModelCore c) {val : Srt → Bool}
    (hval : ∀ s, val s = true → s < nRegSorts + c.sortNames.length) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.boundV c val vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hh : Holds c vars.length σ p b)
    (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔ b = true :=
  HoldsShape.holds_denB (atomFacts_stdI h) (binderFacts_stdI h) (boundReads_boundV_stdI h hval) p
    hok hbd hP (reads_of_readsT h hr) hk hS hh a ((inhOf_srtOf_stdI h hS _ a).mpr ha)

end Model

open ML Model

/-- **A rule's condition in the value model at any transition T, over `Cond.boundV`**: `holds_stdI`
for a condition whose `ex` binders are of a confined sort or of a sort `val` admits with the body
fixing the variable, `val` admitting numbered sorts only. Where the condition has a truth value at
σ, an element of a numbered predicate sort is in `Cond.kore p` exactly where `Holds … p true`. -/
theorem holds_stdI_fixed {c : Semantics} (h : HypModelCore c) (T : GroundTerm → GroundTerm → Prop)
    {val : Srt → Bool} (hval : ∀ s, val s = true → s < nRegSorts + c.sortNames.length) (p : Cond)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation Elem} {S : Srt}
    (hok : c.condOK vars p = true) (hbd : Cond.boundV c val vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : ReadsT c vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) (srtOf c S) p), k ∈ tbl)
    (hS : S < nRegSorts + c.sortNames.length) (hd : ∃ b, Holds c vars.length σ p b)
    (a : Elem) (ha : InSort c S a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)).interpret (stdI_T c T) e a ↔
      Holds c vars.length σ p true := by
  obtain ⟨b, hb⟩ := hd
  rw [holds_atT_fixed (T := T) h hval p hok hbd hP hr hk hS hb a ha]
  constructor
  · rintro rfl; exact hb
  · intro ht
    exact (holds_atT_fixed (T := T) h hval p hok hbd hP hr hk hS hb a ha).mp
      ((holds_atT_fixed (T := T) h hval p hok hbd hP hr hk hS ht a ha).mpr rfl)

end Faithful

end KCore
