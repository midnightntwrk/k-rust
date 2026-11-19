/-
  KCore. L3 for the functions of a semantics whose clauses are asked CN-4's bodies
  (`Semantics.sortedOKCl`: `clauseSortedOpen` and `clausePlainOpen` in place of `clauseSorted` and
  `clausesPlain`), with no hypothesis on the sorts of the variables the patterns and conditions do
  not hold.

  `sortedOKCl` gives what the evaluation lemmas read of each clause of each function, the user's and
  the sort predicates' (`clauseOpenFacts_of_sortedOKCl`), and with `srReady` the sorts of the right
  sides (`sortCtx_of_allCl`). A negated clause's exclusion is empty where it fails
  (`neg_of_coreCl`, through `exclEmptyCl_ofCl`): its patterns and conditions are read in the model
  from `SortCtx`, the theory's sentences on confined sorts (`confinedAt_valueCl`) and `CondDecided`,
  with nothing assumed of the model. Then a function
  applied to arguments of its sorts is what its evaluation's result denotes (`eval_den4_coreCl`).
-/
import KcoreSpec.OpenClauseDen
import KcoreSpec.RightHeldStep
import KcoreSpec.HeldBackCl

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

/-- **`sortedOKCl` gives `ClauseOpenFacts` of every clause of every function** (the user's and the
sort predicates'). -/
theorem clauseOpenFacts_of_sortedOKCl {c : Semantics} (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFacts c fn L cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hs, hpl⟩ := (Semantics.sortedOKCl_parts hok).2.1 fn hu cl hcl
    exact ⟨c.fns.map Fn.sig, fns_headsOK, clauseOpenFacts_of (hpreTop := hpreTop) hs hpl (Semantics.clausesPreTop_spec hpreTop hu hcl)⟩
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    have hpp := sortPreds_topCl hp cl hcl
    refine ⟨[], fun k hk => absurd hk List.not_mem_nil,
      sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats, hpp.1, hpp.2,
      fun i hi => ?_, fun t ht => ?_, hrhs, fun t ht => ?_, Semantics.sortPreds_exs hp cl hcl⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (hb i hi))))
    · rw [ht] at hreq; simpa [reqOK] using hreq
    · rw [ht] at hens; simpa [reqOK] using hens

/-- **`sortedOKCl` gives `ClauseOpenFactsP` of every clause of every function**: the user's with a
well-sorted predicate in the premise (`clauseSortedOpen`), the sort predicates' with `\top`. -/
theorem clauseOpenFactsP_of_sortedOKCl {c : Semantics} (hok : c.sortedOKCl = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFactsP c fn L cl := by
  intro fn hfn cl hcl
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hs, hpl⟩ := (Semantics.sortedOKCl_parts hok).2.1 fn hu cl hcl
    exact ⟨c.fns.map Fn.sig, fns_headsOK, clauseOpenFactsP_of hs hpl⟩
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    have hpp := sortPreds_topCl hp cl hcl
    refine ⟨[], fun k hk => absurd hk List.not_mem_nil,
      sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats,
      by rw [hpp.1, Semantics.condOK], hpp.2,
      fun i hi => ?_, fun t ht => ?_, hrhs, fun t ht => ?_, Semantics.sortPreds_exs hp cl hcl⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (hb i hi))))
    · rw [ht] at hreq; simpa [reqOK] using hreq
    · rw [ht] at hens; simpa [reqOK] using hens

/-- A user clause with an open condition variable of a confined sort makes the definition read a
confined sort. -/
theorem readsConfined_of_openCl {c : Semantics} {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (h : cl.openCondVars.any (fun i => (cl.vars[i]?.map c.confined).getD false) = true) :
    c.readsConfined = true := by
  obtain ⟨i, hi, -⟩ := List.any_eq_true.mp h
  have hne : cl.opens ≠ [] := fun he => by simp [Clause.openCondVars, he] at hi
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨fn, hfn, cl, hcl, by simp [List.isEmpty_iff, hne]⟩

/-- A user clause with an open condition variable makes the definition read a confined sort. -/
theorem readsConfined_of_opensCl {c : Semantics} {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (h : cl.openCondVars ≠ []) : c.readsConfined = true := by
  have hne : cl.opens ≠ [] := fun he => h (by simp [Clause.openCondVars, he])
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨fn, hfn, cl, hcl, by simp [List.isEmpty_iff, hne]⟩

/-- A clause whose patterns bind every variable has no open condition variable. -/
theorem openCondVars_of_bindsCl {cl : Clause} (hb : binds cl.vars.length (varOccsList cl.pats) = true) :
    cl.openCondVars = [] := by
  simp [Clause.openCondVars, Clause.opens_of_binds hb]

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Each negated clause's exclusion is empty where it fails**, in a model of `Γc` of a semantics
with `sortedOKCl`, `srReady`, `OvlOK`, `faithCoreOK` and `patHooksApart`, whose clauses' conditions
are decided where `needsWitness` holds, and whose clauses' predicates other than `\top` are read in
the model (`PreRead`). An open condition variable a cut of the predicate holds is a value's: the
symbols `Semantics.holds` names have `HeldBack` (`heldBack_holdsCl`), the confined sorts' elements
being values' since a clause with an open condition variable makes the definition read them. -/
theorem neg_of_coreCl (hI : I ⊧ᴵP Γc c) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hpreR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → HoldsShape.PreRead c I cl) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl := by
  obtain ⟨hnn, hg, hcso, hcs, hph', hnk, -⟩ := faithCoreOK_parts hfa
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)
  have hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := fun hr s hs x hx =>
    confinedAt_valueCl hsc.trans (Model.namesApartK_spec hnk) (fun k hk hkr => (Semantics.raw_of_sortedOKCl hok hk hkr).2.2.2.1) hr hI _ s hs x hx
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hrw : ∀ k ∈ c.params, k.raw = true → instDecode? (c.symName k.sig.name) = none :=
    fun k hk hkr => (Semantics.raw_of_sortedOKCl hok hk hkr).2.2.2.1
  intro fn hfn cl hcl _ ws
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hs, hpl⟩ := (Semantics.sortedOKCl_parts hok).2.1 fn hu cl hcl
    obtain ⟨hpats, -, hreqS, -, -⟩ := Semantics.clauseSortedOpen_parts hs
    obtain ⟨-, -, hconj, -⟩ := Semantics.clausePlainOpen_partsP hpl
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv
      (Semantics.clauseSortedOpen_pats_nf hs)
      (Semantics.clauseSortedOpen_preOK hs) (hpreR fn hfn cl hcl) hreqS hconj
      (readsConfined_of_openCl hu hcl)
      (fun hany => by
        obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
        exact heldBack_holdsCl hIΓ hsc (namesNumbered_spec hnn) hg (Model.namesApartK_spec hnk) hrw hph hcs hcso
          (fun _ => confinedAt_valueCl hsc.trans (Model.namesApartK_spec hnk) hrw
            (readsConfined_of_opensCl hu hcl (List.ne_nil_of_mem hi)) hI))
      (hc fn hu cl hcl)
  · obtain ⟨hpats, -, hb, hreq, -, -⟩ := sortPreds_ctx hp cl hcl
    have hoc := openCondVars_of_bindsCl hb
    have hnw : cl.needsWitness c = false := by simp [Clause.needsWitness, Clause.reqOpen, hoc]
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv (L := [])
      (Semantics.sortPredPats_nf (hov.hyp hsc.trans).fnFacts hp hcl)
      (by rw [(sortPreds_topCl hp cl hcl).1, Semantics.condOK]) (fun hne => absurd (sortPreds_topCl hp cl hcl).1 hne)
      (fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq) (by simp [Clause.reqOpen, hoc])
      (fun h' => by simp [hoc] at h')
      (fun h' => by simp [hoc] at h')
      (fun h' => by rw [hnw] at h'; cases h')

/-- **L3 for the functions of a semantics whose clauses are asked CN-4's bodies**: in a model of
`Γc`, a function applied to the elements of arguments of its sorts is what its evaluation's result
denotes, defined or not (`eval_den4Cl`, with `neg_of_coreCl`'s hypotheses). -/
theorem eval_den4_coreCl (hI : I ⊧ᴵP Γc c) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hpreR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → HoldsShape.PreRead c I cl)
    {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm} (hev : Eval c f ws r) {fn : Fn}
    (hfn : c.lookupFn f = some fn) (hws : c.sortsOf ws = some fn.args) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m :=
  eval_den4ClPre (fun φ hφ => hI φ (Or.inl hφ)) (namesNumbered_spec (faithCoreOK_parts hfa).1)
    (sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)) hph (clauseOpenFactsP_of_sortedOKCl hok)
    (neg_of_coreCl hI hok hsr hfa hph hc hpreR) hpreR hev hfn hws e m

end

end Faithful

end KCore
