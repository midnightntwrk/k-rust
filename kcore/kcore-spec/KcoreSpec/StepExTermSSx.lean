/-
  KCore. `EvalTerm` is sound in every model of `Γc` of a semantics `coreOKEx` accepts
  (`HoldsShape.termSound_of_coreExSSx`), the reading the step lemmas over `coreOKEx` take of the
  functions' clauses.

  A clause of a function with existential variables binds them in scope and outside its patterns
  (`clauseExOK`), so each is an open variable of the clause and the semantics reads confined sorts
  (`readsConfined_of_exsSSx`); `clauseExRead_of_coreEx` then gives the reading of every such clause
  in every model of `Γc` (`clauseExRead_allSSx`). With the facts every clause has
  (`clauseOpenFactsQ_of_sortedOKEx`), the negated clauses' emptiness where they fail
  (`neg_of_coreExSSx`: a clause's sorts with its open variables are its sorts,
  `clauseSortedOpen_of_sorted`, and `clausesPlainEx` asks the two conjuncts the emptiness reads) and
  the premises' readings (`preReadAll_of_coreExSSx`), the block of OpenClauseDenQ.lean reads every
  evaluation of a term (`evalTerm_den4ClQ`).
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
theorem readsConfined_of_exsSSx (h : c.coreOKEx = true) {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause}
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
`readsConfined_of_exsSSx`); the sort predicates' clauses have none. -/
theorem clauseExRead_allSSx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ClauseExRead c I fn cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · exact clauseExRead_of_coreEx h (readsConfined_of_exsSSx h hu hcl hne) hIc fn hfn cl hcl hne
  · exact absurd (Semantics.sortPreds_exs hp cl hcl) hne

/-- **Each negated clause's exclusion is empty where it fails**, in a model of `Γc` of a semantics
`coreOKEx` accepts whose clauses' conditions are decided where `needsWitness` holds, and whose
clauses' predicates other than `\top` are read in the model (`PreRead`). A user clause is sorted
with its open variables (`clauseSortedOpen_of_sorted`), its open condition variables are of
confined sorts or its conditions are closed, and its premise's predicate is `\top` or it needs no
witness (`clausesPlainEx`). -/
theorem neg_of_coreExSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (hpreR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → HoldsShape.PreRead c I cl) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl := by
  obtain ⟨hok, hfa, -, -, -⟩ := Semantics.coreOKEx_parts h
  obtain ⟨-, hsr, -, -, hph, -, -, -, hov⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hov
  obtain ⟨hnn, hg, hcso, hcs, hph', hnk, -⟩ := faithCoreOK_parts hfa
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hov)
  have hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x := fun hr s hs x hx =>
    confinedAt_valueCl hsc.trans (Model.namesApartK_spec hnk)
      (fun k hk hkr => (Semantics.raw_of_sortedOKEx hok hk hkr).2.2.2.1) hr hI _ s hs x hx
  intro fn hfn cl hcl _ ws
  rcases List.mem_append.mp hfn with hu | hp
  · have hs := Semantics.clauseSortedOpen_of_sorted ((Semantics.sortedOKEx_parts hok).2.1 fn hu cl hcl)
    obtain ⟨hpats, -, hreqS, -, -⟩ := Semantics.clauseSortedOpen_parts hs
    obtain ⟨-, -, hpre, hconj⟩ := Semantics.clausesPlainEx_spec (Semantics.sortedOKEx_parts hok).2.2.2.2.1 hu hcl
    have hnw : cl.pre ≠ .top → cl.needsWitness c = false := fun hne => by
      have hnt : cl.pre.isTop = false := by
        cases hpt : cl.pre.isTop with
        | false => rfl
        | true => exact absurd (Cond.eq_top_of_isTop hpt) hne
      rw [hnt, Bool.false_or] at hpre
      simpa using hpre
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv hpats
      (Semantics.clauseSortedOpen_preOK hs) (fun hne => ⟨hpreR fn hfn cl hcl hne, hnw hne⟩) hreqS hconj
      (readsConfined_of_openCl hu hcl) (hc fn hu cl hcl)
  · obtain ⟨hpats, -, hb, hreq, -, -⟩ := sortPreds_ctx hp cl hcl
    have hoc := openCondVars_of_bindsCl hb
    have hnw : cl.needsWitness c = false := by simp [Clause.needsWitness, Clause.reqOpen, hoc]
    exact exclEmptyCl_ofCl hI (namesNumbered_spec hnn) hg hsc hph hcso hcs hph' hcv (L := [])
      (sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats)
      (by rw [(sortPreds_topCl hp cl hcl).1, Semantics.condOK]) (fun hne => absurd (sortPreds_topCl hp cl hcl).1 hne)
      (fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq) (by simp [Clause.reqOpen, hoc])
      (fun h' => by simp [hoc] at h') (fun h' => by rw [hnw] at h'; cases h')

/-- Every model of `Γ c` of a definition `coreOKEx` accepts reads the right sides' terms in their
sorts (`termsInSort_of_model`). -/
theorem termsInSort_of_coreExSSx (h : c.coreOKEx = true) (hI : I ⊧ᴵP Γ c) : TermsInSort c I := by
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
(`PreRead`), where it is not `\top`. -/
theorem preReadAll_of_coreExSSx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → PreRead c I cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hok, hbd⟩ := Semantics.sortedOKEx_clausePre (Semantics.coreOKEx_parts h).1 hu hcl
    exact preRead_of (nodeFacts_of_coreEx h hIc)
      (fun hb => binderFacts_of_coreEx h (readsConfined_of_clausePre hu hcl hb) hIc)
      (termsInSort_of_coreExSSx h fun φ hφ => hIc φ (Or.inl hφ)) hok hbd
  · exact absurd (Semantics.sortPreds_pre hp cl hcl) hne

/-- **`TermSound` holds in every model of `Γc` of a semantics `coreOKEx` accepts**, where the
clauses' conditions are decided where `needsWitness` holds: the block of OpenClauseDenQ.lean
(`evalTerm_den4ClQ`) with every clause's facts (`clauseOpenFactsQ_of_sortedOKEx`), the negated
clauses' emptiness (`neg_of_coreExSSx`), the premises' readings (`preReadAll_of_coreExSSx`) and the
reading of each clause with existential variables (`clauseExRead_allSSx`). -/
theorem termSound_of_coreExSSx (h : c.coreOKEx = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    TermSound c I := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, -, hph, -, -, -, hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  intro σ t r he vars vs tbl e s hσ hvs hag ht m
  exact evalTerm_den4ClQ hI hnn hsc hph (clauseOpenFactsQ_of_sortedOKEx hok)
    (neg_of_coreExSSx h hIc hc (preReadAll_of_coreExSSx h hIc)) (preReadAll_of_coreExSSx h hIc)
    (clauseExRead_allSSx h hIc) he fns_headsOK hσ hvs hag ht m

end

end HoldsShape

end KCore
