/-
  KCore. A variable held by a cut of a clause, at a value.

  A clause's predicate `pre` is read at a sort given as a pattern (a clause's exclusion reads it at
  the sort variable `R`), so the facts of MemHeldValues.lean are restated at any sort that denotes
  one sort element:

  - `memHeldCl_mem_elem`: where `V ∈ t` holds at some element, inside a sort that denotes one sort
    element, the valuation's element at V is in t's translation.
  - `memHeldCl_witnessedAt`: in a model of `Γ`, at a valuation of the variables in their sorts that
    gives each variable of `bound` the element of a value, where `pre` holds at some element inside
    such a sort and each cut of `pre` is well sorted, the valuation gives each `memHeldH` variable the
    element of a value of its sort, for every H whose symbols have `HeldBack`.
  - `memHeld_clause_valuesF`: the same with `bound` a clause's patterns' variables, the patterns at
    the elements of values of their sorts (`patVals_backC` makes their variables values' elements),
    from the facts of a semantics the proofs of the exclusion read.
  - `memHeld_clause_valuesB`: the same in a model of `Γc` of a semantics `coreOK` accepts.
  - `memHeld_clause_values`: it at the landed `memHeld` (H = `Semantics.holds`).
-/
import KcoreSpec.MemHeldValues

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section MemElemS
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`\in` at a variable, inside a sort given as a pattern**: where `V ∈ t` holds at some element
inside a sort that denotes one sort element, the valuation's element at V is in t's translation. -/
theorem memHeldCl_mem_elem (hI : I ⊧ᴵP Γ c) [OvlOK c] {vs : List KoreAML.Var} {tbl : VarTable}
    {e : Valuation M} {s : Srt} {S' : Kore.KSort} {σ' : M} {v : Nat} {t : Term} {a : M}
    (hs : s < nRegSorts + c.sortNames.length)
    (hS' : ∀ b, (KoreAML.trSort tbl S').interpret I e b ↔ b = σ') (hσ' : IsSort I σ')
    (hv : InS I (c.sortName s) (e.evalEvar (tbl.ev (keyAt vs v))))
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' (.mem s (.var v) t))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e (e.evalEvar (tbl.ev (keyAt vs v))) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σs, hσs1, hσs2⟩ := sortSing hI hs
  rw [Cond.kore, KoreAML.tr] at hm
  unfold srtOf at hm
  rw [KoreAML.interp_sIn hD hc (S := KoreAML.trSort tbl (KoreAML.srt (c.sortName s)))
    (S' := KoreAML.trSort tbl S')
    (by rw [trSort_srt]; exact hσs1) hS' hσs2 hσ' (fun b hb => ?_) a] at hm
  · obtain ⟨⟨b, hb, hbt⟩, -⟩ := hm
    have hbe : b = e.evalEvar (tbl.ev (keyAt vs v)) := (tr_var v b).mp hb
    rw [← hbe]; exact hbt
  · have hbe : b = e.evalEvar (tbl.ev (keyAt vs v)) := (tr_var v b).mp hb
    rw [hbe]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσs1).mp hv

end MemElemS

section AtS
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
  [OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
  {L : List CtorSig} (hL : HeadsOK c L) {H : Sym → Bool}
  (hback : ∀ f k, c.isCtor f = false → H f = true → lookupSig (c.rhsCtx L).heads f = some k → HeldBack c I f k)
include hI hg htr hnm hvs hin hL hback

/-- **A variable held by a cut, at a value, inside a sort given as a pattern.** At a valuation of
the variables in their sorts that gives each variable of `bound` the element of a value, where
`pre` holds at some element inside a sort that denotes one sort element and each cut `V ∈ t` of
`pre` has V and t at the sort it names, a numbered one: the valuation gives each `memHeldH`
variable the element of a value of its sort. -/
theorem memHeldCl_witnessedAt {bound : List Nat} (hbound : ∀ v ∈ bound, Witnessed c I tbl vs vars e v)
    {pre : Cond}
    (hok : ∀ s v t, Cond.mem s (.var v) t ∈ pre.conjuncts → vars[v]? = some s ∧
      sortOfTerm (c.rhsCtx L) vars t = some s ∧ s < nRegSorts + c.sortNames.length)
    {S' : Kore.KSort} {σ' : M} (hS' : ∀ b, (KoreAML.trSort tbl S').interpret I e b ↔ b = σ')
    (hσ' : IsSort I σ') {a : M}
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' pre)).interpret I e a)
    (i : Nat) (hi : memHeldH c H bound pre i = true) : Witnessed c I tbl vs vars e i := by
  obtain ⟨s, v, t, hq, hvb, hti⟩ := memHeldH_parts hi
  obtain ⟨hvs', hts, hsn⟩ := hok s v t hq
  have hqm := conjuncts_spec (fun q => (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' q)).interpret I e a)
    (fun p q hp => by rw [Cond.kore, tr_and2, KoreAML.interp_sAnd] at hp; exact hp) pre hpre _ hq
  obtain ⟨w, hw, hwe⟩ := hbound v hvb
  rw [List.getD_eq_getElem?_getD, hvs', Option.getD_some] at hw
  have hinv := hin v (List.getElem?_eq_some_iff.mp hvs').1
  rw [List.getD_eq_getElem?_getD, hvs', Option.getD_some] at hinv
  have hmt := memHeldCl_mem_elem hI hsn hS' hσ' hinv hqm
  rw [← hwe] at hmt
  exact occsUnder_witnessed hI hg htr hnm hvs hin hL hback hts hw hmt i hti

end AtS

section Clause
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A variable held by a cut of a clause, at a value**, from the facts of the semantics the
clause's exclusion reads. In a model of `Γ`, at a valuation of the variables in their sorts
`vars` under which the clause's patterns, sorted at `vars`, hold at the elements of values of
their sorts, and `pre`, well sorted at `vars`, holds at some element inside a sort that denotes
one sort element: the valuation gives every variable that is `memHeldH` over the patterns'
variables the element of a value of its sort, for every H whose symbols that are no constructor
have `HeldBack` in the model. -/
theorem memHeld_clause_valuesF (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hg : genWf c = true)
    (hsc : SortCtx c) [OvlOK c] (hph : patHooksApart c = true) (hcso : collSortsOK c = true)
    (hcs : collsOK c = true) (hph' : patHeadsOK c = true) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {cl : Clause} {vars ss : List Srt}
    (hpats : sortsOfTerms c.patCtxAll vars cl.pats = some ss) (hok : c.condOK vars cl.pre = true)
    {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} (hvs : vs.length = vars.length)
    (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
    {ws : List GroundTerm} (hws : c.sortsOf ws = some ss)
    (hall : All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)))
    {S' : Kore.KSort} {σ' : M} (hS' : ∀ b, (KoreAML.trSort tbl S').interpret I e b ↔ b = σ')
    (hσ' : IsSort I σ') {a : M}
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' cl.pre)).interpret I e a)
    (i : Nat) (hi : memHeldH c H (varOccsList cl.pats) cl.pre i = true) :
    Witnessed c I tbl vs vars e i := by
  obtain ⟨-, hwitP⟩ := patVals_backC hI hph hcs hcso hg hsc.trans hnn.1 hvs hin
    (collPats_of_sorted hph' hpats) (OvlOK.nfs_bridge inferInstance hpats) hws hall
  exact memHeldCl_witnessedAt hI hg hsc.trans hnn.1 hvs hin fns_headsOK hback hwitP
    (fun s v t hq => conjuncts_memOK hok hq) hS' hσ' hpre i hi

/-- **A variable held by a cut of a clause, at a value**: in a model of `Γc` of a semantics
`coreOK` accepts, a valuation of the variables in their sorts under which the clause's patterns,
sorted at those sorts, hold at the elements of values of their sorts, and `pre`, well sorted at
them, holds at some element inside a sort that denotes one sort element, gives every variable that
is `memHeldH` over the patterns' variables the element of a value of its sort, for every H whose
symbols that are no constructor have `HeldBack` in the model. -/
theorem memHeld_clause_valuesB (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {cl : Clause} {vars ss : List Srt}
    (hpats : sortsOfTerms c.patCtxAll vars cl.pats = some ss) (hok : c.condOK vars cl.pre = true)
    {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} (hvs : vs.length = vars.length)
    (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
    {ws : List GroundTerm} (hws : c.sortsOf ws = some ss)
    (hall : All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)))
    {S' : Kore.KSort} {σ' : M} (hS' : ∀ b, (KoreAML.trSort tbl S').interpret I e b ↔ b = σ')
    (hσ' : IsSort I σ') {a : M}
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' cl.pre)).interpret I e a)
    (i : Nat) (hi : memHeldH c H (varOccsList cl.pats) cl.pre i = true) :
    Witnessed c I tbl vs vars e i := by
  obtain ⟨hok', hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok' hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  exact memHeld_clause_valuesF hIΓ hnn hg hsc hph hcso hcs hph' hback hpats hok hvs hin hws hall
    hS' hσ' hpre i hi

/-- `memHeld_clause_valuesB` at the landed `memHeld`: the held symbols are those of
`Semantics.holds`. -/
theorem memHeld_clause_values (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → c.holds f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {cl : Clause} {vars ss : List Srt}
    (hpats : sortsOfTerms c.patCtxAll vars cl.pats = some ss) (hok : c.condOK vars cl.pre = true)
    {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} (hvs : vs.length = vars.length)
    (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
    {ws : List GroundTerm} (hws : c.sortsOf ws = some ss)
    (hall : All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs cl.pats).map (KoreAML.tr ⟨tbl, []⟩))
      (ws.map (elemOf c I)))
    {S' : Kore.KSort} {σ' : M} (hS' : ∀ b, (KoreAML.trSort tbl S').interpret I e b ↔ b = σ')
    (hσ' : IsSort I σ') {a : M}
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs S' cl.pre)).interpret I e a)
    (i : Nat) (hi : memHeld c (varOccsList cl.pats) cl.pre i = true) :
    Witnessed c I tbl vs vars e i :=
  memHeld_clause_valuesB h hI hback hpats hok hvs hin hws hall hS' hσ' hpre i
    (by rw [← memHeld_eq_H]; exact hi)

end Clause

end KCore
