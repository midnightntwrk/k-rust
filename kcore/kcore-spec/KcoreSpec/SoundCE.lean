/-
  KCore. Soundness at a step, completeness at a configuration and the one instance of a step by a
  rule without existential variables (`sound_at_ce`, `complete_at_ce`, `famEx_closed_ce`), for a
  semantics `coreOKEx` accepts: `sound_at`'s, `complete_at`'s and `famEx_closed`'s statements with
  `coreOKEx` for `coreOK`, so a function's clauses may bind variables by `\exists` (`clausesPlainEx`).
  None takes `FnHyp`. A clause with existential variables is read in every model of `Γc` through
  `ClauseExRead` (`Faithful.clauseExRead_all_of_coreEx`), so `EvalTerm` is sound there
  (`HoldsShape.termSoundEx`); the step lemmas are SoundCEx.lean's and CompleteCEx.lean's.
  `coreOK` is `coreOKEx` (`Semantics.coreOK_iff_ex`).
-/
import KcoreSpec.SoundCEx
import KcoreSpec.CompleteCEx
import KcoreSpec.CompletePP
import KcoreSpec.StepValuesHeld
import KcoreSpec.OvlHeldBack

set_option autoImplicit false

namespace KCore

/-- What `sortedOKEx` gives of each rule: `ruleSorted` and `rulePlainHO2`
(`ruleFactsHO2_of_sortedOK`'s proof; the rules' conjuncts of `sortedOKEx` are `sortedOK`'s). -/
theorem Semantics.ruleFactsHO2_of_sortedOKEx {c : Semantics} (h : c.sortedOKEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHO2 r = true := by
  intro r hr
  obtain ⟨-, -, hs, hp, -, -⟩ := Semantics.sortedOKEx_parts h
  exact ⟨List.all_eq_true.mp hs r hr, Semantics.rulesPlain_iff_memHeld.mp hp r hr⟩

/-- What `coreOKEx` gives of each rule: `ruleSorted` and `rulePlainHO2`. -/
theorem Semantics.ruleFactsHO2_of_coreEx {c : Semantics} (h : c.coreOKEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHO2 r = true :=
  Semantics.ruleFactsHO2_of_sortedOKEx (Semantics.coreOKEx_parts h).1

/-- What `coreOKEx` gives of each rule: `ruleSorted`, and `rulePlainHeldH` at the symbols
`Semantics.holds` names. -/
theorem Semantics.ruleFactsHeld_of_coreEx {c : Semantics} (h : c.coreOKEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true := fun r hr =>
  ⟨(Semantics.ruleFactsHO2_of_coreEx h r hr).1,
    Semantics.rulePlainHeldH_of_HO2 (Semantics.ruleFactsHO2_of_coreEx h r hr).2⟩

open ML Faithful Faithful.Model

/-- The symbols `Semantics.holds` names have `HeldBack` in every model of `Γc`, for a semantics
`coreOKEx` accepts. `hrc`: the definition reads a confined sort where an overload closure holds a
function. -/
theorem heldBackAll_holdsCEx {c : Semantics} (h : c.coreOKEx = true)
    (hrc : c.ovls.any (fun o => !(c.fnOverloads o.sig.name).isEmpty) = true → c.readsConfined = true) :
    HeldBackAll c c.holds := by
  intro M _ I hI f k hc hh hk
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSoundEx_of_coreEx h
  haveI : OvlOK c := hno
  exact heldBack_holdsCl (fun φ hφ => hI φ (Or.inl hφ)) (sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)) hnn hg
    (Model.namesApartK_spec (faithCoreOK_parts (Semantics.coreOKEx_parts h).2.1).2.2.2.2.2.1)
    (fun k hk hkr => (Semantics.raw_of_coreEx h hk hkr).2.2.2.1) hph hcs hcso
    (fun hany => confinedAt_valueCEx h (hrc hany) hI) f k hc hh hk

/-- What `coreOKEx` gives the statements over a set of held symbols: some set at which the rules
have `ruleSorted` and `rulePlainHeldH` and whose symbols have `HeldBack` in every model of `Γc`. -/
theorem Semantics.heldFacts_of_coreEx {c : Semantics} (h : c.coreOKEx = true) :
    ∃ H : Sym → Bool, (∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) ∧
      HeldBackAll c H :=
  heldFacts_of_rules (Semantics.ruleFactsHeld_of_coreEx h) fun hr => heldBackAll_holdsCEx h fun _ => hr


/-- **Soundness at a step by a rule with a `pre` and a `post`**: `sound_at`'s statement from the
per-rule facts `ruleSorted` and `rulePlainHeldH`. The competitors of r whose left side matches x have
decided closed conditions. -/
theorem sound_at_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) := by
  obtain ⟨hsr, hpr⟩ := hrules r hs.mem
  refine ⟨?_, ?_⟩
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    exact step_sound_heldCEx h hrules hI (hbk I hI) hcw hsr hpr (readsConfined_of_pre hs.mem) (readsConfined_of_post hs.mem)
      (sat_rules hIΓ (Or.inl ⟨_, List.mem_map.mpr ⟨r, hs.mem, rfl⟩, rfl⟩))
      (fun r' _ hlt => List.any_eq_true.mpr ⟨r, hs.mem, by simpa using hlt⟩) hs.hσ hs.hmatch hs.hreq hs.hpre
      hs.heval hs.hens hs.hpost hs.hprio hw e m
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    intro hm
    rw [((elemOf_spec hIΓ y.property e).1 m).mp hm]
    exact famEx_mem_ppCEx h hsr (readsConfined_of_post hs.mem) hs.hσ hs.heval hs.hens hs.hpost hI hcw e

/-- **Completeness at a configuration, for rules with a `pre` and a `post`**: `complete_at`'s
statement from the per-rule facts `ruleSorted` and `rulePlainHeldH` (`rulePlainHeldH` is carried, not
read). -/
theorem complete_at_heldCEx (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true)
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
  obtain ⟨b, hb, hcase⟩ := step_successor_ppCEx h (fun r hr => (hrules r hr).1) x hd hI hcw e _ hnext
  rw [interpret_neg] at hb
  rcases hcase with ⟨y, r, σ, hop, hs, rfl⟩ | ⟨r, hr, hop, σ, hu, hfo⟩
  · exact hb (disjList_of_mem (List.mem_map_of_mem (hval y r σ hop hs))
      (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))
  · obtain ⟨σ', hag, hmem⟩ := hfam r hr hop σ hu
    refine hb (disjList_of_mem (List.mem_map_of_mem hmem) ?_)
    show (famOpen c r σ').interpret I e b
    rw [famOpen_congrOpen c r hag]
    exact hfo

/-- **A step by a rule without existential variables has one instance**, whatever the rule's
`post` (`famEx_closed`'s statement): of what `coreOKEx` says of the rule, only `ruleSorted` is read
(`famEx_denPPCEx`), and `readsConfined` where `post` has a binder comes from the rule being one of
`c`'s. -/
theorem famEx_closed_postCEx (c : Semantics) (h : c.coreOKEx = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) := by
  intro M _ I hI e m
  rw [KoreAML.interp_equal (defOK fun φ hφ => hI φ (Or.inl hφ))]
  exact fun a => famEx_denPPCEx h (Semantics.ruleFactsHO2_of_coreEx h r hs.mem).1 hex
    (readsConfined_of_post hs.mem) hs.hσ hs.heval hs.hens hs.hpost hI hc e a

/-! ## The statements at a step and at a configuration over `coreOKEx` -/

/-- **A step by a rule without existential variables has one instance**, for a semantics
`coreOKEx` accepts (`famEx_closed`'s statement with `coreOKEx` for `coreOK`). -/
theorem famEx_closed_ce (c : Semantics) (h : c.coreOKEx = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) :=
  famEx_closed_postCEx c h hs hex hc

/-- **Soundness at a step** of a semantics that `coreOKEx` accepts (`sound_at`'s statement with
`coreOKEx` for `coreOK`): in every model, x has a successor among the instances of the
application, and y is one of them. The competitors of r whose left side matches x and the clauses
evaluation may reach have decided closed conditions. -/
theorem sound_at_ce (c : Semantics) (h : c.coreOKEx = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :=
  let ⟨_, hrules, hbk⟩ := Semantics.heldFacts_of_coreEx h
  sound_at_heldCEx c h hrules hbk x y r σ hs hw hc

/-- **Completeness at a configuration** of a semantics that `coreOKEx` accepts (`complete_at`'s
statement with `coreOKEx` for `coreOK`), where the evaluations the step at x reads have results
(`StepDecided`): with the step's closure, every successor of x is in an outcome of `os`, any list
holding the successors by the rules whose left side binds every variable and a family for each
unblocked match of the other rules. -/
theorem complete_at_ce (c : Semantics) (h : c.coreOKEx = true) (x : Config c) (hd : StepDecided c x.val)
    (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  complete_at_heldCEx c h (Semantics.ruleFactsHeld_of_coreEx h) x hd os hval hfam hc

end KCore
