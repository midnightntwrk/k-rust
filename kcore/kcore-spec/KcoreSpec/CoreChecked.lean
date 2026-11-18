/-
  KCore, checked layer: `coreOK` decided conjunct by conjunct, its sort checks read from the
  tables, for a definition that meets `coreOK` whether or not it meets `wf` (`kcore gen --core`).

  `Semantics.sortedOK` reads the subsort closure in every clause's and rule's sort check, and a
  kernel decision recomputes it there. `fnRowsSortedT` and `ruleRowsSortedT` read it from the tables
  `T` (Tables.lean), a block of functions or of rules at a time; with `T = tables c` they are the
  checks of `sortedOK` (`sortedOK_of_T`). `coreOK_of_T` joins them with the other conjuncts, each a
  decision of its own (`faithCoreOK_of_parts`).
-/
import KcoreSpec.TablesChecked
import KcoreSpec.Statements

set_option autoImplicit false

namespace KCore

/-- Rows lo, …, lo + len - 1 of `l` pass `p`. -/
def rowsAll {α : Type} (l : List α) (p : α → Bool) (lo len : Nat) : Bool :=
  (List.range' lo len).all fun i => match l[i]? with
    | some x => p x
    | none => false

theorem rowsAll_add {α : Type} {l : List α} {p : α → Bool} {lo a b : Nat}
    (h1 : rowsAll l p lo a = true) (h2 : rowsAll l p (lo + a) b = true) : rowsAll l p lo (a + b) = true := by
  simp only [rowsAll, List.all_eq_true, List.mem_range'_1] at *
  intro m hm
  by_cases hma : m < lo + a
  · exact h1 m ⟨hm.1, hma⟩
  · exact h2 m ⟨by omega, by omega⟩

theorem all_of_rowsAll {α : Type} {l : List α} {p : α → Bool} (h : rowsAll l p 0 l.length = true) :
    l.all p = true := by
  simp only [rowsAll, List.all_eq_true, List.mem_range'_1] at h ⊢
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i ⟨Nat.zero_le _, by omega⟩
  simpa [List.getElem?_eq_getElem hi] using this

namespace Semantics
variable (T : Tables) (c : Semantics)

/-- `patCtxAll`, read from the tables. -/
def patCtxAllT : TermCtx := { c.patCtxT T with heads := (c.patCtxT T).heads ++ (c.collPatSigs ++ c.ovlSigs) }

/-- `clauseSorted`, read from the tables. -/
def clauseSortedT (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms (c.patCtxAllT T) cl.vars cl.pats == some f.args &&
  binds cl.vars.length (varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) &&
  reqOK (c.rhsCtxT T rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtxT T rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtxT T rhsHeads) cl.vars cl.ens &&
  (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) &&
  c.condOK cl.vars cl.pre

/-- `ruleSorted`, read from the tables. -/
def ruleSortedT (r : Rule) : Bool :=
  sortOfTerm (c.patCtxAllT T) r.vars r.lhs == some topCellSort &&
  binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
    varOccsCond r.vars.length r.post) &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !r.condVars.contains i) &&
  reqOK (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.req && c.condOK r.vars r.pre &&
  reqOK (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.ens && c.condOK r.vars r.post &&
  Cond.bound c r.vars.length r.pre && Cond.bound c r.vars.length r.post &&
  sortOfTerm (c.rhsCtxT T (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort

/-- The clauses of functions lo, …, lo + len - 1 are well sorted, read from the tables. -/
def fnRowsSortedT (lo len : Nat) : Bool :=
  rowsAll c.fns (fun f => f.clauses.all (c.clauseSortedT T f (c.fns.map Fn.sig))) lo len

/-- Rules lo, …, lo + len - 1 are well sorted, read from the tables. -/
def ruleRowsSortedT (lo len : Nat) : Bool := rowsAll c.rules (c.ruleSortedT T) lo len

end Semantics

section
variable {c : Semantics} {T : Tables}

theorem Semantics.fnRowsSortedT_join {a m b n : Nat} (h1 : c.fnRowsSortedT T 0 a = true)
    (h2 : c.fnRowsSortedT T m b = true) (hm : a = m) (hn : a + b = n) : c.fnRowsSortedT T 0 n = true := by
  subst hm hn
  unfold Semantics.fnRowsSortedT at h1 h2 ⊢
  exact rowsAll_add (lo := 0) h1 (by simpa using h2)

theorem Semantics.ruleRowsSortedT_join {a m b n : Nat} (h1 : c.ruleRowsSortedT T 0 a = true)
    (h2 : c.ruleRowsSortedT T m b = true) (hm : a = m) (hn : a + b = n) : c.ruleRowsSortedT T 0 n = true := by
  subst hm hn
  unfold Semantics.ruleRowsSortedT at h1 h2 ⊢
  exact rowsAll_add (lo := 0) h1 (by simpa using h2)

theorem Semantics.fnRowsSortedT_all {n : Nat} (hn : c.fns.length = n) (h : c.fnRowsSortedT T 0 n = true) :
    c.fnRowsSortedT T 0 c.fns.length = true := hn ▸ h

theorem Semantics.ruleRowsSortedT_all {n : Nat} (hn : c.rules.length = n) (h : c.ruleRowsSortedT T 0 n = true) :
    c.ruleRowsSortedT T 0 c.rules.length = true := hn ▸ h

/-- `sortedOK` from the tables: the declared subsorts, every function's clauses and every rule; and
the rules, clauses and parameters plain, and no pattern applying a function-overloaded symbol
(`ovlPatsOK`: the rows sort a rule's left side over `patCtxAll`), by the kernel unless given. -/
theorem Semantics.sortedOK_of_T (hT : T = tables c) (hs : c.subsortsOKT T = true)
    (hf : c.fnRowsSortedT T 0 c.fns.length = true) (hr : c.ruleRowsSortedT T 0 c.rules.length = true)
    (hpl : (c.rulesPlain && c.clausesPlain && c.paramsPlain) = true := by decide +kernel)
    (hov : c.ovlPatsOK = true := by decide +kernel) :
    c.sortedOK = true := by
  subst hT
  unfold Semantics.fnRowsSortedT at hf
  unfold Semantics.ruleRowsSortedT at hr
  have hf' := all_of_rowsAll hf
  have hr' := all_of_rowsAll hr
  simp only [Bool.and_eq_true] at hpl
  have hr'' : c.rules.all c.ruleSorted = true := List.all_eq_true.mpr fun r hr0 => by
    have h0 := List.all_eq_true.mp hr' r hr0
    simp only [Semantics.ruleSortedT, Bool.and_eq_true] at h0
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h0
    have h1' : sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort := beq_iff_eq.mp h1
    simp only [Semantics.ruleSorted, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨beq_iff_eq.mpr (sortOfTerm_to_nf r.lhs h1' (Semantics.ovlPats_lhs hov hr0)), h2⟩, h3⟩, h4⟩,
      h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  simp only [Semantics.sortedOK, subsortsOK_of_T hs, Bool.true_and, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hf', hr''⟩, hpl.1.1⟩, hpl.1.2⟩, hpl.2⟩

open Faithful Faithful.Model in
/-- `faithCoreOK` from its conjuncts, the names' apartness by sorted codes (`namesApartFast`): each
a decision of its own. -/
theorem Semantics.faithCoreOK_of_parts (h1 : namesNumbered c = true) (h2 : genWf c = true)
    (h3 : collSortsOK c = true) (h4 : collsOK c = true) (h5 : patHeadsOK c = true)
    (h6 : namesApartFast c = true) (h7 : LitsApart c = true) (h8 : sortsNumbered c = true)
    (h10 : itesApart c = true) (h11 : kindsApart c = true) (h12 : ctorsOnce c = true)
    (h13 : fnsApart c = true) : c.faithCoreOK = true := by
  simp only [Semantics.faithCoreOK, h1, h2, h3, h4, h5, namesApartK_of_fast h6, h7, h8, h10, h11, h12,
    h13, Bool.and_self]

/-- **`coreOK` from its conjuncts**, the sort checks read from the tables. -/
theorem Semantics.coreOK_of_T (hT : T = tables c) (hs : c.subsortsOKT T = true)
    (hf : c.fnRowsSortedT T 0 c.fns.length = true) (hr : c.ruleRowsSortedT T 0 c.rules.length = true)
    (hfa : c.faithCoreOK = true) (hha : c.hooksApart = true) (hpa : c.predsApart = true)
    (hids : c.idsOK = true) (hov : c.overloadsOK = true)
    (hpl : (c.rulesPlain && c.clausesPlain && c.paramsPlain) = true := by decide +kernel) : c.coreOK = true := by
  simp only [Semantics.coreOK, Semantics.sortedOK_of_T hT hs hf hr hpl (Semantics.overloadsOK_pats hov), hfa, hha, hpa, hids, hov, Bool.and_self]

end

end KCore
