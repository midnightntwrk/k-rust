/-
  KCore. Every model of `Γc` of a definition `coreOK` accepts reads its clauses' predicates over
  `Cond.bound`.

  `preRead_of_bound`: what the clause lemmas ask of the model for a clause's predicate
  (`PreRead`), for a predicate that is well sorted with binders `Cond.bound` bounds, in a model of
  `Γc`. The truth value with its terms' readings (`HoldsRead`) is read in I over `Cond.bound` by
  `CE.holdsReadT_holdsAt_bound` where the predicate holds a binder (the definition then reads a
  confined sort); a predicate without a binder reads no Bool, and is read over `Cond.boundConf`
  (`preRead_of`). `preReadAll_of_core`: it for each clause of each function (`clauseSorted`; a
  sort predicate's clause has the predicate `\top`).
-/
import KcoreSpec.HoldsDenFixed
import KcoreSpec.ClausePreCore

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace HoldsShape

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A model of `Γc` of a definition `coreOK` accepts reads a clause's predicate** (`PreRead`)
whose binders `Cond.bound` bounds, where a binder in it makes the definition read a confined
sort. -/
theorem preRead_of_bound (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) {cl : Clause}
    (hrc : hasBinder cl.pre = true → c.readsConfined = true) (hok : c.condOK cl.vars cl.pre = true)
    (hbd : Cond.bound c cl.vars.length cl.pre = true) : PreRead c I cl := by
  have F : NodeFacts c I := nodeFacts_of_core h hIc
  have hT : TermsInSort c I := termsInSort_of_core h fun φ hφ => hIc φ (Or.inl hφ)
  cases hb : hasBinder cl.pre with
  | false =>
    exact preRead_of F (fun h' => by rw [hb] at h'; cases h') hT hok
      (Cond.boundConf_of_noBinder c cl.pre cl.vars.length hb)
  | true =>
    exact preRead_ofB F hT hok hbd fun hh => CE.holdsReadT_holdsAt_bound h (hrc hb) hIc F hh

/-- **Every model of `Γc` of a definition `coreOK` accepts reads each clause's predicate**
(`PreRead`), where it is not `\top`. -/
theorem preReadAll_of_core (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → PreRead c I cl := by
  intro fn hfn cl hcl hne
  rcases List.mem_append.mp hfn with hu | hp
  · obtain ⟨hok, hbd⟩ := Semantics.sortedOK_clausePre (Semantics.coreOK_parts h).1 hu hcl
    exact preRead_of_bound h hIc (readsConfined_of_clausePre hu hcl) hok hbd
  · exact absurd (Semantics.sortPreds_pre hp cl hcl) hne

end

end HoldsShape

end KCore
