/-
  KCore. `Semantics.coreOKEx`, the well-sortedness that admits clauses with existential variables,
  stated apart from `coreOK`.

  `clausesPlainEx` asks what a clause's existential variables and its right-side predicate need
  for the function's values to be the values its instances give (`clausePlainEx`: an existential
  variable is of a confined sort or fixed by the predicate, and a clause without one has the
  predicate `\top`), that they are in scope, apart, outside the left side and that the predicate
  is sorted (`clauseExOK`), with the conjunct on a clause's open condition variables. `sortedOKEx` is `sortedOK` with `clausesPlainEx` in place of `clausesPlain`, and
  `coreOKEx` is `coreOK` with `sortedOKEx` in place of `sortedOK`. `clausesPlain` has the body of
  `clausesPlainEx`, so each is the other (`Semantics.clausesPlain_iff_ex`, `sortedOK_iff_ex`,
  `coreOK_iff_ex`).
-/
import KcoreSpec.Statements
import KcoreSpec.Obligations
import KcoreSpec.ClausePlainEx

set_option autoImplicit false

namespace KCore

/-- **Clauses that may bind variables by `\exists`**: each existential variable is of a confined
sort or fixed by the right-side predicate, which is `\top` where there is none
(`clausePlainEx`); the existential variables are in scope, apart and outside the left side, and the
right-side predicate is sorted (`clauseExOK`); and a clause's open condition variables are of
confined sorts or held by a cut of its premise predicate (`memHeld`), or its conditions are closed. -/
def Semantics.clausesPlainEx (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  c.clausePlainEx cl && c.clauseExOK cl &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false ||
      memHeld c (varOccsList cl.pats) cl.pre i)

/-- `sortedOK` with `clausesPlainEx` in place of `clausesPlain`. -/
def Semantics.sortedOKEx (c : Semantics) : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.clausesPlainEx && c.paramsPlain

/-- `coreOK` with `sortedOKEx` in place of `sortedOK`. -/
def Semantics.coreOKEx (c : Semantics) : Bool :=
  c.sortedOKEx && c.faithCoreOK && c.hooksApart && c.predsApart && c.idsOK && c.overloadsOK

/-- What `clausesPlainEx` asks of one clause of a function of the semantics. -/
theorem Semantics.clausesPlainEx_spec {c : Semantics} (h : c.clausesPlainEx = true) {fn : Fn}
    (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    c.clausePlainEx cl = true ∧ c.clauseExOK cl = true ∧
      (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false ||
      memHeld c (varOccsList cl.pats) cl.pre i) = true := by
  have := List.all_eq_true.mp (List.all_eq_true.mp h fn hfn) cl hcl
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A clause without existential variables whose right-side predicate is `\top` meets
`clauseExOK`. -/
theorem Semantics.clauseExOK_of_nil {c : Semantics} {cl : Clause} (hex : cl.exs = [])
    (hpost : cl.post.isTop = true) : c.clauseExOK cl = true := by
  unfold Semantics.clauseExOK
  rw [Cond.eq_top_of_isTop hpost, hex]
  simp [nodup, Semantics.condOK]

/-- `clausesPlain` is `clausesPlainEx`. -/
theorem Semantics.clausesPlain_iff_ex {c : Semantics} : c.clausesPlain = true ↔ c.clausesPlainEx = true := Iff.rfl

/-- `sortedOK` is `sortedOKEx`. -/
theorem Semantics.sortedOK_iff_ex {c : Semantics} : c.sortedOK = true ↔ c.sortedOKEx = true := Iff.rfl

/-- **`coreOK` is `coreOKEx`.** -/
theorem Semantics.coreOK_iff_ex {c : Semantics} : c.coreOK = true ↔ c.coreOKEx = true := Iff.rfl

/-- What `sortedOKEx` says of the sorts, the clauses and the rules: what `sortedOK` says
(`Semantics.sortedOK_sorted`). -/
theorem Semantics.sortedOKEx_sorted {c : Semantics} (h : c.sortedOKEx = true) :
    (c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
      c.rules.all c.ruleSorted) = true := by
  simp only [Semantics.sortedOKEx, Bool.and_eq_true] at h ⊢; exact h.1.1.1

theorem Semantics.sortedOKEx_parts {c : Semantics} (h : c.sortedOKEx = true) :
    c.subsortsOK = true ∧
      (∀ f ∈ c.fns, ∀ cl ∈ f.clauses, c.clauseSorted f (c.fns.map Fn.sig) cl = true) ∧
      c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.clausesPlainEx = true ∧
      c.paramsPlain = true := by
  simp only [Semantics.sortedOKEx, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, fun f hf cl hcl => List.all_eq_true.mp (List.all_eq_true.mp h2 f hf) cl hcl, h3, h4, h5, h6⟩

/-- What `sortedOKEx` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_sortedOKEx {c : Semantics} (h : c.sortedOKEx = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ instDecode? (c.symName k.sig.name) = none ∧
    c.shapesOK = true :=
  Semantics.raw_of_paramsPlain (Semantics.sortedOKEx_parts h).2.2.2.2.2 hk hr

/-- Each clause's predicate, in a semantics `sortedOKEx` accepts, is well sorted over the clause's
variables (`condOK`), with binders that range where values and elements agree (`Cond.bound`). -/
theorem Semantics.sortedOKEx_clausePre {c : Semantics} (h : c.sortedOKEx = true) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) :
    c.condOK cl.vars cl.pre = true ∧ Cond.bound c cl.vars.length cl.pre = true := by
  have := (Semantics.sortedOKEx_parts h).2.1 fn hfn cl hcl
  simp only [Semantics.clauseSorted, Bool.and_eq_true] at this
  exact ⟨this.2, this.1.2.1⟩

/-- A clause without existential variables, in a semantics `sortedOKEx` accepts, has the right-side
predicate `\top`. -/
theorem Semantics.sortedOKEx_post_of_nil {c : Semantics} (h : c.sortedOKEx = true) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) (hex : cl.exs = []) : cl.post = .top :=
  Cond.eq_top_of_isTop ((Semantics.clausePlainEx_nil_iff hex).mp
    (Semantics.clausesPlainEx_spec (Semantics.sortedOKEx_parts h).2.2.2.2.1 hfn hcl).1)

theorem Semantics.coreOKEx_parts {c : Semantics} (h : c.coreOKEx = true) :
    c.sortedOKEx = true ∧ c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true := by
  simp only [Semantics.coreOKEx, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- `coreOKEx`'s condition on the overloading symbols. -/
theorem Semantics.coreOKEx_ovls {c : Semantics} (h : c.coreOKEx = true) : c.overloadsOK = true := by
  simp only [Semantics.coreOKEx, Bool.and_eq_true] at h
  exact h.2

end KCore
