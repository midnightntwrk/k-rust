/-
  KCore. Every model of `Γc` of a definition `coreOK` accepts reads its clauses' predicates.

  `preReadAll_of_core`: what the clause lemmas ask of the model for a clause's predicate
  (`PreRead`), for each clause of each function: a user clause's predicate is well sorted with
  binders that range where values and elements agree (`clauseSorted`), a binder in it makes the
  definition read a confined sort, and a sort predicate's clause has the predicate `\top`. With it
  the evaluation lemmas hold for clauses with a predicate in the premise (`eval_den4ClPre`,
  `neg_of_coreCl`), so `EvalTerm` is sound (`termSound_of_core`) and the Holds lemma holds
  (`holds_entails`) in every such model.
-/
import KcoreSpec.ClausePreTie
import KcoreSpec.HoldsFactsCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful

namespace HoldsShape

section Core
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A clause of the definition whose predicate has a binder makes the definition read a confined
sort. -/
theorem readsConfined_of_clausePre {fn : Fn} (hfn : fn ∈ c.fns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hb : hasBinder cl.pre = true) : c.readsConfined = true := by
  simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨fn, hfn, cl, hcl, by simp [hb]⟩

/-- **Every model of `Γc` of a definition `coreOK` accepts reads each clause's predicate**
(`PreRead`), where it is not `\top`. -/
theorem preReadAll_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → PreRead c I cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hok, hbd⟩ := Semantics.sortedOK_clausePre (Semantics.coreOK_parts h).1 hu hcl
    exact preRead_of (nodeFacts_of_core h hIc)
      (fun hb => binderFacts_of_core h (readsConfined_of_clausePre hu hcl hb) hIc)
      (termsInSort_of_core h fun φ hφ => hIc φ (Or.inl hφ)) hok hbd
  · exact absurd (Semantics.sortPreds_pre hp cl hcl) hne

/-- `TermSound` holds in every model of `Γc` of a semantics `coreOK` accepts, under the clause
hypothesis of `sound_at`. -/
theorem termSound_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    TermSound c I := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hc (HoldsShape.preReadAll_of_core h hIc)
  intro σ t r he vars vs tbl e s hσ hvs hag ht m
  exact evalTerm_den4ClPre hI hnn hsc hph
    (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) he fns_headsOK hσ hvs hag ht m

/-- **The Holds lemma in every model of `Γc`**: for a definition `coreOK` accepts, under the clause
hypothesis of `sound_at`, and `readsConfined` where the condition holds a binder. -/
theorem holds_entails (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDen' c I p :=
  holds_den_binders' (atomFacts_of_core h hIc (termSound_of_core h hIc hc)) p
    fun hb => binderFacts_of_core h (hrc hb) hIc

end Core

end HoldsShape

end KCore
