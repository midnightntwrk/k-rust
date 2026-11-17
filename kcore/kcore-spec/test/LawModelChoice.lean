/-
  `law_model_choice` (KcoreSpec/LawModelChoice.lean): its statement is the pinned
  `has_model_choice`'s with the laws' hypotheses and the conjunct of the laws' sentences. Without
  laws (`ls := []`) it gives the pinned statement, as a term (`type_of%`); its model also
  satisfies `consistent_with_laws`' conjunct.
  Run from the package root: `lake env lean test/LawModelChoice.lean`.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.LawModelChoiceTest

open KCore ML Faithful

#check @law_model_choice

/-- At no law, `law_model_choice` gives the pinned `has_model_choice`. -/
example : type_of% @has_model_choice := fun c h hf T hsub hall hsome =>
  let ⟨M, i, I, hI, hT, _⟩ := law_model_choice c h hf (ls := []) (fun _ hm => nomatch hm)
    (fun _ hm => nomatch hm) T hsub hall hsome
  ⟨M, i, I, hI, hT⟩

/-- Its model satisfies the laws' sentences, as `consistent_with_laws`' does. -/
example (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) {ls : List LawEq} (hl : FnLaws c ls)
    (hsort : ∀ l ∈ ls, lawSorted c l = true) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧ ∀ l ∈ ls, I ⊧ᴵ lawPattern c l :=
  let ⟨M, i, I, hI, _, hlaw⟩ := law_model_choice c h hf hl hsort (Step c) (fun _ _ hs => hs)
    (fun _ _ r σ hs _ => step_iff_by.mpr ⟨r, σ, hs⟩)
    (fun _ y r σ hs => ⟨y, σ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨r, σ, hs⟩⟩)
  ⟨M, i, I, hI, hlaw⟩

end KCore.LawModelChoiceTest

/-- info: 'KCore.law_model_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.law_model_choice
