/-
  KCore. What the clause lemmas read of a clause's predicate in a model.

  A clause's premise carries its predicate at the sort variable `R` (`withPre`), and its conditions
  `∃ō. (⌈req = true⌉ ∧ pre)` carry it at Bool (`Clause.condK`). `PreRead c I cl` is what the lemmas
  on a clause's sentences read of the predicate in I: a truth value `Holds` gives it, with the
  readings of the terms it evaluates (`HoldsRead`), read at `R` (`atR`), and the predicate at `R`
  moved to Bool through another table (`toBool`). It is asked of the clauses whose predicate is not
  `\top` only.
-/
import KcoreSpec.HoldsNode
import KcoreSpec.HoldsRead
import KcoreSpec.HoldsCongr
import KcoreSpec.CondKoreVars
import KcoreSpec.CondVarsCongr

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace HoldsShape

/-- **What the clause lemmas read of a clause's predicate in I.** -/
structure PreRead (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (cl : Clause) : Prop where
  /-- The truth value b that `Holds` gives the predicate under σ, with the readings in I of the
  terms it evaluates (`HoldsRead`), is read at the sort variable `R`: σ well sorted over sorts that
  agree with the clause's at the variables of its patterns and conditions, at a valuation that
  gives each variable of the predicate the element of its value under σ and `R` a sort, an element
  of that sort is in the predicate's pattern exactly where b is `true`. -/
  atR : ∀ {vars : List Srt} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M} {σr : M},
    HoldsRead c I cl.vars.length σ cl.pre b → vars.length = cl.vars.length →
    (∀ i ∈ cl.leftVars, vars[i]? = cl.vars[i]?) → c.WellSorted vars σ →
    (∀ i ∈ varOccsCond cl.vars.length cl.pre, ∀ v, σ.lookup i = some v →
      ∀ m, m = e.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ (den c v).interpret I e m) →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
    KoreAML.VarKey.sortVar "R" ∈ tbl →
    (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → KoreAML.IsSort I σr →
    ∀ a, KoreAML.Inh I σr a →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e a ↔ b = true)
  /-- The predicate at `R`, where it holds at an element of the sort `R` is given, holds at Bool at
  every element of Bool, through another table and at another valuation that gives each variable
  of the predicate the same element, an element of the variable's sort. -/
  toBool : ∀ {tbl tbl' : KoreAML.VarTable} {e e' : Valuation M} {σr : M} {m mB : M},
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
    KoreAML.VarKey.sortVar "R" ∈ tbl →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) (srtOf c Srt.bool) cl.pre), k ∈ tbl') →
    (∀ i ∈ varOccsCond cl.vars.length cl.pre,
      InS I (c.sortName (cl.vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c cl.vars i))) ∧
      e.evalEvar (tbl.ev (canonKey c cl.vars i)) = e'.evalEvar (tbl'.ev (canonKey c cl.vars i))) →
    (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → KoreAML.IsSort I σr → KoreAML.Inh I σr m →
    (KoreAML.inhOf (KoreAML.trSort tbl' (srtOf c Srt.bool))).interpret I e' mB →
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m →
    (KoreAML.tr ⟨tbl', []⟩ (Cond.kore c (canonVars c cl.vars) (srtOf c Srt.bool) cl.pre)).interpret I e' mB

/-- The premise of a clause whose predicate is not `\top`, read: the premise without the predicate
and the predicate at `R`. -/
theorem withPre_interp {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M} {vs : List KoreAML.Var}
    {cl : Clause} {prem : Kore.Pattern} (hne : cl.pre.isTop = false)
    {tbl : KoreAML.VarTable} {e : Valuation M} {m : M} :
    (KoreAML.tr ⟨tbl, []⟩ (withPre c vs cl prem)).interpret I e m ↔
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret I e m ∧
        (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs KoreAML.R cl.pre)).interpret I e m := by
  unfold withPre
  rw [hne, if_neg (by simp), tr_and2, KoreAML.interp_sAnd]

/-- A predicate that is not `\top` is not `isTop`. -/
theorem isTop_false_of_ne {p : Cond} (h : p ≠ .top) : p.isTop = false := by
  cases hp : p.isTop with
  | false => rfl
  | true => exact absurd (Cond.eq_top_of_isTop hp) h

/-- A predicate that is not `isTop` is not `\top`. -/
theorem ne_top_of_isTop_false {p : Cond} (h : p.isTop = false) : p ≠ .top := fun hp => by
  rw [hp] at h; simp [Cond.isTop] at h

/-- The variables of a clause's premise are variables of its premise with its predicate. -/
theorem varsOf_withPre_prem {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    {k : KoreAML.VarKey} (hk : k ∈ KoreAML.varsOf prem) : k ∈ KoreAML.varsOf (withPre c vs cl prem) := by
  unfold withPre
  split
  · exact hk
  · exact Model.varsOf_and_mem (List.mem_cons_self ..) hk

/-- The variables of a clause's predicate at `R` are variables of its premise with its predicate,
where the predicate is not `\top`. -/
theorem varsOf_withPre_pre {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    (hne : cl.pre.isTop = false) {k : KoreAML.VarKey} (hk : k ∈ KoreAML.varsOf (Cond.kore c vs KoreAML.R cl.pre)) :
    k ∈ KoreAML.varsOf (withPre c vs cl prem) := by
  unfold withPre
  rw [hne, if_neg (by simp)]
  exact Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk

/-- A free variable of a clause's premise with its predicate is one of the premise or of the
predicate at `R`. -/
theorem freeOf_withPre {c : Semantics} {vs : List KoreAML.Var} {cl : Clause} {prem : Kore.Pattern}
    {bound : List KoreAML.VarKey} {k : KoreAML.VarKey} (hk : k ∈ KoreAML.freeOf bound (withPre c vs cl prem)) :
    k ∈ KoreAML.freeOf bound prem ∨
      (cl.pre.isTop = false ∧ k ∈ KoreAML.freeOf bound (Cond.kore c vs KoreAML.R cl.pre)) := by
  unfold withPre at hk
  split at hk
  · exact Or.inl hk
  · rename_i hne
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
    simp only [List.append_nil, List.mem_append] at hk
    rcases hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨by simpa using hne, hk⟩

end HoldsShape

end KCore
