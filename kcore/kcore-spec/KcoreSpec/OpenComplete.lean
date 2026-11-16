/-
  KCore. Completeness at a configuration, for a definition whose rules' left sides need not bind
  every variable, in any model of `Γc` with the step's closure.

  `famOpen c r σ` reads σ only through `fixK c r σ (varOccs r.lhs)`, that is at the variables of
  the left side: two substitutions that agree there give one pattern (`famOpen_congrOpen`). A
  successor of x is a `Step` value by a rule whose left side binds every variable, or lies in
  `famOpen c r σ` for an unblocked match σ of a rule with an open variable (`step_successor_open`);
  a list of outcomes holding each such value and, for each such match, a family at a substitution
  that agrees with it on the left side's variables, holds every successor (`complete_at_open`).
-/
import KcoreSpec.OpenSplit
import KcoreSpec.FaithfulFamilies
import KcoreSpec.StepOld

set_option autoImplicit false

namespace KCore

namespace Faithful

/-- `fixK` reads σ at the listed variables only. -/
theorem fixK_congrOpen (c : Semantics) (r : Rule) {σ σ' : Subst} {is : List Nat}
    (h : ∀ i ∈ is, σ'.lookup i = σ.lookup i) : fixK c r σ' is = fixK c r σ is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have ht := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    unfold fixK at ht ⊢
    simp only [List.filterMap_cons, h i (List.mem_cons_self ..)] at ht ⊢
    rw [ht]

/-- **The outcomes of a match depend on the match at the left side's variables only**: two
substitutions that agree on the variables of r's left side give one pattern `famOpen`. -/
theorem famOpen_congrOpen (c : Semantics) (r : Rule) {σ σ' : Subst}
    (h : ∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) : famOpen c r σ' = famOpen c r σ := by
  unfold famOpen
  rw [fixK_congrOpen c r h]

end Faithful

open ML Faithful

/-- **Completeness at a configuration, for a definition whose rules' left sides need not bind
every variable**: `complete_at`'s conclusion, for a semantics that `coreOK` accepts whose rules
have `ruleSorted` and `rulePlainOpen`, where the evaluations the step at x reads have results
(`StepDecided`): with the step's closure, every successor of x is in an outcome of `os`, any list
holding the successors by the rules whose left side binds every variable and, for each unblocked
match of another rule, a family at a substitution that agrees with it on the left side's
variables. -/
theorem complete_at_open (c : Semantics) (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
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
  obtain ⟨b, hb, hcase⟩ := step_successor_open h hrules x hd hI hcw e _ hnext
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
