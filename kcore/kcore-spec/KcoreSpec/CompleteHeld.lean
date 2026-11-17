/-
  KCore. Completeness at a configuration, for rules with `rulePlainHeldH`.

  `complete_at_held` is `complete_at_pp` with the per-rule fact `rulePlainHeldH c H` in place of
  `rulePlainPP`; the proof reads `ruleSorted` only, so H is any set of symbols.
-/
import KcoreSpec.CompletePP
import KcoreSpec.StepValuesHeld

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

open KoreAML (VarTable)

open HoldsShape (hasBinder Reads reads_of_agrees)

end Faithful

open ML Faithful

/-- **Completeness at a configuration, for rules with a `pre` and a `post`**: `complete_at`'s
statement from the per-rule facts `ruleSorted` and `rulePlainHeldH` (`rulePlainHeldH` is carried, not
read). -/
theorem complete_at_held (c : Semantics) {H : Sym → Bool} (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (x : Config c) (hd : StepDecided c x.val) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) := by
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  rw [interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [interpret_neg]
  intro hnext
  obtain ⟨b, hb, hcase⟩ := step_successor_pp h (fun r hr => (hrules r hr).1) x hd hI hcw e _ hnext
  rw [interpret_neg] at hb
  rcases hcase with ⟨y, r, σ, hop, hs, rfl⟩ | ⟨r, hr, hop, σ, hu, hfo⟩
  · exact hb (disjList_of_mem (List.mem_map_of_mem (hval y r σ hop hs))
      (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))
  · obtain ⟨σ', hag, hmem⟩ := hfam r hr hop σ hu
    refine hb (disjList_of_mem (List.mem_map_of_mem hmem) ?_)
    show (famOpen c r σ').interpret I e b
    rw [famOpen_congrOpen c r hag]
    exact hfo

end KCore
