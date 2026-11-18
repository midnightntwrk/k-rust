/-
  KCore. `EvalTerm` is sound in every model of `Γc` of a semantics `coreOKEx` accepts
  (`HoldsShape.termSoundEx`), and the Holds lemma holds there (`HoldsShape.holds_entailsCEx`).

  A clause of a function with existential variables binds them outside its patterns
  (`clauseExOK`), so the clause has an open variable and the semantics reads confined sorts
  (`readsConfined_of_exsCEx`); `clauseExRead_of_coreEx` then gives the reading of every such clause
  in every model of `Γc` (`clauseExRead_all_of_coreEx`). With the facts every clause has
  (`clauseOpenFactsQ_of_sortedOKEx`), the negated clauses' emptiness (`neg_of_coreClEx`, over
  `sortedOKClEx`, which `sortedOKEx` gives) and the premises' readings (`preReadAll_of_coreEx`),
  OpenClauseDenQ.lean's block reads every evaluation of a term.
-/
import KcoreSpec.ClauseExDenCEx
import KcoreSpec.ClausePreCore
import KcoreSpec.CondCross

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A clause with existential variables makes the definition read a confined sort**: its
existential variables are in scope and in no pattern (`clauseExOK`), so each is an open variable
of the clause. -/
theorem readsConfined_of_exsCEx (h : c.coreOKEx = true) {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) (hne : cl.exs ≠ []) : c.readsConfined = true := by
  obtain ⟨-, hs, -, -⟩ :=
    Semantics.clausesPlainEx_spec (Semantics.sortedOKEx_parts (Semantics.coreOKEx_parts h).1).2.2.2.2.1 hfn hcl
  simp only [Semantics.clauseExOK, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨⟨hlt, -⟩, hleft⟩, -⟩ := hs
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
  have hio : i ∈ cl.opens := by
    have hl := hleft i hi
    simp only [Clause.leftVars, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.mem_append, not_or] at hl
    simp only [Clause.opens, List.mem_filter, List.mem_range, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact ⟨by simpa using hlt i hi, hl.1⟩
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  refine Or.inr ⟨fn, hfn, cl, hcl, ?_⟩
  simp [List.ne_nil_of_mem hio]

/-- **Every clause with existential variables has `ClauseExRead`** in every model of `Γc` of a
definition `coreOKEx` accepts (`clauseExRead_of_coreEx`, the definition reading confined sorts by
`readsConfined_of_exsCEx`); the sort predicates' clauses have none. -/
theorem clauseExRead_all_of_coreEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ClauseExRead c I fn cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · exact clauseExRead_of_coreEx h (readsConfined_of_exsCEx h hu hcl hne) hIc fn hfn cl hcl hne
  · exact absurd (Semantics.sortPreds_exs hp cl hcl) hne

/-- `neg_of_coreCl` over `sortedOKClEx`: the clauses a clause negates are empty in the model where
they fail; what it reads of a clause (`clausePlainOpenEx_parts`) is what it read of
`clausePlainOpen`. -/
theorem neg_of_coreClEx (hI : I ⊧ᴵP Γc c) (hok : c.sortedOKClEx = true) (hsr : c.srReady = true) [hov : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hpreR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → HoldsShape.PreRead c I cl) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl := by
  obtain ⟨hnn, hg, hcso, hcs, hph', hnk, -⟩ := faithCoreOK_parts hfa
  have hsc := sortCtx_of_allClEx hok hsr (OvlOK.ovlCase hov)
  have hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := fun hr s hs x hx =>
    confinedAt_valueCl hsc.trans (Model.namesApartK_spec hnk)
      (fun k hk hkr => (Semantics.raw_of_sortedOKClEx hok hk hkr).2.2.2.1) hr hI _ s hs x hx
  intro fn hfn cl hcl _ ws
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hs, hpl⟩ := (Semantics.sortedOKClEx_parts hok).2.1 fn hu cl hcl
    obtain ⟨hpats, -, hreqS, -, -⟩ := Semantics.clauseSortedOpen_parts hs
    obtain ⟨-, -, hconj, hnw⟩ := Semantics.clausePlainOpenEx_parts hpl
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv
      (Semantics.clauseSortedOpen_pats_nf hs)
      (Semantics.clauseSortedOpen_preOK hs) (fun hne => ⟨hpreR fn hfn cl hcl hne, hnw hne⟩) hreqS hconj
      (readsConfined_of_openCl hu hcl) (hc fn hu cl hcl)
  · obtain ⟨hpats, -, hb, hreq, -, -⟩ := sortPreds_ctx hp cl hcl
    have hoc := openCondVars_of_bindsCl hb
    have hnw : cl.needsWitness c = false := by simp [Clause.needsWitness, Clause.reqOpen, hoc]
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv (L := [])
      (Semantics.sortPredPats_nf (hov.hyp hsc.trans).fnFacts hp hcl)
      (by rw [(sortPreds_topCl hp cl hcl).1, Semantics.condOK]) (fun hne => absurd (sortPreds_topCl hp cl hcl).1 hne)
      (fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq) (by simp [Clause.reqOpen, hoc])
      (fun h' => by simp [hoc] at h') (fun h' => by rw [hnw] at h'; cases h')

/-- `termsInSort_of_core` for a semantics `coreOKEx` accepts. -/
theorem termsInSort_of_coreEx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) : TermsInSort c I := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  intro vars tbl e t s ht hs hin a ha
  exact termsInSort_of_model hI hg ht hs hin a ha

end

end Faithful

namespace HoldsShape

open ML Faithful

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Every model of `Γc` of a definition `coreOKEx` accepts reads each clause's predicate**
(`PreRead`), where it is not `\top` (`preReadAll_of_core`'s proof). -/
theorem preReadAll_of_coreEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → PreRead c I cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hok, hbd⟩ := Semantics.sortedOKEx_clausePre (Semantics.coreOKEx_parts h).1 hu hcl
    exact preRead_of (nodeFacts_of_coreEx h hIc)
      (fun hb => binderFacts_of_coreEx h (readsConfined_of_clausePre hu hcl hb) hIc)
      (termsInSort_of_coreEx h fun φ hφ => hIc φ (Or.inl hφ)) hok hbd
  · exact absurd (Semantics.sortPreds_pre hp cl hcl) hne

/-- **`TermSound` holds in every model of `Γc` of a semantics `coreOKEx` accepts**, under the
clause hypothesis of `sound_at`: OpenClauseDenQ.lean's block (`evalTerm_den4ClQ`) with every
clause's facts (`clauseOpenFactsQ_of_sortedOKEx`) and the reading of each clause with existential
variables (`clauseExRead_all_of_coreEx`). -/
theorem termSoundEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    TermSound c I := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hneg := neg_of_coreClEx hIc (Semantics.sortedOKClEx_of_sortedOKEx hok) hsr (Semantics.coreOKEx_parts h).2.1
    hph hc (preReadAll_of_coreEx h hIc)
  intro σ t r he vars vs tbl e s hσ hvs hag ht m
  exact evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok) hneg (preReadAll_of_coreEx h hIc)
    (clauseExRead_all_of_coreEx h hIc) he fns_headsOK hσ hvs hag ht m

/-- **The Holds lemma in every model of `Γc`** of a definition `coreOKEx` accepts, under the clause
hypothesis of `sound_at`, and `readsConfined` where the condition holds a binder. -/
theorem holds_entailsCEx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDen' c I p :=
  holds_den_binders' (atomFacts_of_coreEx h hIc (termSoundEx h hIc hc)) p
    fun hb => binderFacts_of_coreEx h (hrc hb) hIc

end

end HoldsShape

end KCore
