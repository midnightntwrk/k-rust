/-
  KCore. The statements of the specification (KCORE-SPEC.md §9) over the matching-logic theory of
  a semantics (`Γc`, Faithful.lean): soundness, completeness and exactness, proved. The statements
  are SoundDefs.lean's.

  - `SoundC c`: `Γc c` with the step's closure (`Γstep`) has a model, and for every step of `Step`,
    by the rule r under σ (`StepBy`), in every model x has a successor among the instances of that
    application (`famEx`), and y is one of them. It holds of every semantics that `coreOK` accepts
    and whose functions meet `FnHyp` (`sound_hyp`).
  - `CompleteC c ref`: for an outcome function `ref` that lists, at each configuration, the
    successors by the rules whose left side binds every variable and a family for each unblocked
    match of the other rules (`OutIs`), with the step's closure every successor of x is in an
    outcome `ref` lists (`complete_hyp`).
  - `ExactC c`: `Step` is exactly the steps some model of the theory has, at values (`exact_hyp`).
  - `Consistent c`: the theory with the step's closure has a model (`consistent_of`: the value
    model at its own step, where the functions have one result and evaluation solves the
    equations). No totality is read: `Γ` holds no functional axiom of a function (with them:
    `has_model_total`).
  - Over the rules' facts `ruleSorted` and `rulePlainOpen`, given as a hypothesis: the theory has
    a model (`consistent_open`) and `Step` is exact (`exact_open`). Over `ruleSorted` and
    `rulePlainEx` a rule may have existential variables: `Step` is exact (`exact_ex`). Over
    `ruleSorted` and `rulePlainHeldH` at the symbols `Semantics.holds` names, which `coreOK` gives
    (`Semantics.ruleFactsHeld_of_core`), a rule may also have predicates and its right side may
    hold an open variable under those symbols: the statements at a step and at a configuration,
    exactness, the choice among instances and the consistency of the theory are those lemmas'
    instances (`sound_at_held`, `complete_at_held`, `exact_held`, `has_model_choice_held`,
    `famEx_values_held`, `consistent_held`; `famOpen_values_pp` reads `ruleSorted` only), the
    set of symbols and its `HeldBack` in every model being `Semantics.heldFacts_of_core`'s.
  - At one step and one configuration (`sound_at`, `complete_at`), under `coreOK` and the condition
    on the closed open conditions the step reads. For a definition whose shapes are the plain ones
    the step and the theory are the plain ones (`step_plain`, `Γc_plain`), and the statements over
    the plain step hold (`sound_hyp₀`, `complete_hyp₀`, `sound₀`, `complete₀`, `sound_at_plain`,
    `complete_at_plain`).
  - For a definition, `Sound d`, `Complete d ref` and `Exact d` are those of its semantics; they
    hold of every well-formed definition whose named obligations hold (`sound`, `complete`,
    `exact`), and for every interpretation of the parameter symbols (`sound_withHooks`,
    `complete_withHooks`).
-/
import KcoreSpec.SoundDefs
import KcoreSpec.OpenSound
import KcoreSpec.OpenComplete
import KcoreSpec.OpenChoice
import KcoreSpec.OpenExact
import KcoreSpec.OpenFamOpen
import KcoreSpec.ExExact
import KcoreSpec.ExFamOpen
import KcoreSpec.SoundPP
import KcoreSpec.ExactPP
import KcoreSpec.FamOpenValuesPP
import KcoreSpec.ClausePreFn
import KcoreSpec.SoundHeld
import KcoreSpec.CompleteHeld
import KcoreSpec.ExactHeld
import KcoreSpec.FamExValuesHeld
import KcoreSpec.OvlHeldBack

set_option autoImplicit false

namespace KCore

open ML Faithful

/-! ## The statements at a step and at a configuration -/

/-- A step by a rule without existential variables has one instance. -/
theorem famEx_closed (c : Semantics) (h : c.coreOK = true) {x y : Config c} {r : Rule} {σ : Subst}
    (hs : StepBy c r σ x y) (hex : r.exs = [])
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    Γc c ⊧ (famEx c r σ ≡ den c y.val) :=
  famEx_closed_post c h hs hex hc

/-- **Soundness at a step** of a semantics that `coreOK` accepts: in every model, x has a
successor among the instances of the application, and y is one of them. The competitors of r whose
left side matches x and the clauses evaluation may reach have decided closed conditions. -/
theorem sound_at (c : Semantics) (h : c.coreOK = true)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :=
  let ⟨_, hrules, hbk⟩ := Semantics.heldFacts_of_core h
  sound_at_held c h hrules hbk x y r σ hs hw hc

/-- **Completeness at a configuration** of a semantics that `coreOK` accepts, where the evaluations
the step at x reads have results (`StepDecided`): with the step's closure, every successor of x is
in an outcome of `os`, any list holding the successors by the rules whose left side binds every
variable and a family for each unblocked match of the other rules. -/
theorem complete_at (c : Semantics) (h : c.coreOK = true) (x : Config c) (hd : StepDecided c x.val)
    (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) :=
  complete_at_held c h (Semantics.ruleFactsHeld_of_core h) x hd os hval hfam hc

open Faithful.Model in
/-- **The theory of a definition whose rules' left sides need not bind every variable is
consistent**: for a semantics that `coreOK` accepts, whose functions have at most one result
(`FnDet`), whose evaluation solves the equations (`FnSolves`) and whose clauses' predicates have a
truth value wherever their patterns match (`ClausePreDecided`), and whose rules have `ruleSorted`
and `rulePlainOpen`, `Γc c` with the step's closure has a model: the value model
(`stdI_modelOpen`). -/
theorem consistent_open (c : Semantics) (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) : Consistent c :=
  ⟨Elem, inferInstance, stdI c, stdI_modelOpen c h (hypModel_of_fn h hd hs) hl hrules
    (satFnsGoal_decided (hypModel_of_fn h hd hs) (Semantics.fnsNoExs_of_coreOK h) hp)⟩

/-- **Exactness of a definition whose rules' left sides need not bind every variable**: `ExactC`,
for a semantics that `coreOK` accepts whose functions meet `FnHyp` and whose rules have
`ruleSorted` and `rulePlainOpen`. Left to right in the value model (`has_model_choice_open` at
`T := Step`), right to left in any model (`step_of_successorOpen`). -/
theorem exact_open (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) : ExactC c := by
  intro x y
  constructor
  · intro hs
    obtain ⟨M, hM, I, hI, hT⟩ := has_model_choice_open c h hf hrules (Step c) (fun _ _ hst => hst)
      (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
      (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
    exact ⟨M, hM, I, hI, (hT x y).mp hs⟩
  · rintro ⟨M, hM, I, hI, hn⟩
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret I e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret I e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [((elemOf_spec hIΓ x.property e).1 m).mp h1] at h2
    exact step_of_successorOpen c h hf hrules hI x y e h2

open Faithful.Model in
/-- **Consistency** of a semantics that `coreOK` accepts, whose functions have at most one result
at each argument list (`FnDet`), whose evaluation solves the equations (`FnSolves`), whose clauses'
predicates have a truth value wherever their patterns match (`ClausePreDecided`) and whose
interpretation satisfies the open generators' laws (`OpenLaws`): the value model at its own step
(`consistent_held`). -/
theorem consistent_of (c : Semantics) (h : c.coreOK = true) (hd : FnDet c) (hs : FnSolves c)
    (hp : ClausePreDecided c) (hl : OpenLaws c) : Consistent c :=
  consistent_held c h hd hs hp hl (Semantics.ruleFactsHeld_of_core h)

/-! ## The statements over a semantics, under the hypothesis on its functions -/

/-- **Soundness of a semantics** that `coreOK` accepts and whose functions meet `FnHyp`. -/
theorem sound_hyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) : SoundC c :=
  ⟨consistent_of c h (fnModel_of_fnHyp h hf).1 (fnModel_of_fnHyp h hf).2 (clausePreDecided_of_fnHyp h hf)
     hf.2.2.2.2.2,
   fun x y r σ hs => sound_at c h x y r σ hs (fun r' hr' _ hn _ => hf.2.2.2.2.1.1 r' hr' hn)
     hf.2.2.2.2.1.2⟩

/-- **Completeness of a semantics** that `coreOK` accepts and whose functions meet `FnHyp`. -/
theorem complete_hyp (c : Semantics) (ref : OutFn) (h : c.coreOK = true) (hf : FnHyp c) :
    CompleteC c ref :=
  fun href x => complete_at c h x (stepDecided_of_fnHyp h hf x) (ref x.val)
    (fun y r σ hop hs => ((href x).1 y.val).mpr ⟨y.property, r, σ, hop, hs⟩) (href x).2.2 hf.2.2.2.2.1.2

/-- **Exactness of a definition whose rules may have existential variables**: `ExactC`, for a
semantics that `coreOK` accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and
`rulePlainEx`. Left to right in the value model (`has_model_choice_ex` at `T := Step`), right to
left in any model (`step_of_successor_ex`). -/
theorem exact_ex (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true) : ExactC c := by
  intro x y
  constructor
  · intro hs
    obtain ⟨M, hM, I, hI, hT⟩ := has_model_choice_ex c h hf hrules (Step c) (fun _ _ hst => hst)
      (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
      (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)
    exact ⟨M, hM, I, hI, (hT x y).mp hs⟩
  · rintro ⟨M, hM, I, hI, hn⟩
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
    simp only [Interpretation.satisfies, Valuation.satifies] at hn
    obtain ⟨e, hn⟩ := Classical.not_forall.mp hn
    obtain ⟨m, hn⟩ := Classical.not_forall.mp hn
    rw [interpret_impl] at hn
    have h1 : (den c x.val).interpret I e m := Classical.byContradiction fun hc => hn fun h => absurd h hc
    have h2 : (KoreAML.sNext (den c y.val)).interpret I e m :=
      Classical.byContradiction fun hc => hn fun _ => interpret_neg.mpr hc
    rw [((elemOf_spec hIΓ x.property e).1 m).mp h1] at h2
    exact step_of_successor_ex c h hf hrules hI x y e h2

/-- **Exactness of a semantics** that `coreOK` accepts and whose functions meet `FnHyp`: left to
right in the value model, right to left in any model (`exact_held`, with the rules' facts `coreOK`
gives). -/
theorem exact_hyp (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) : ExactC c :=
  let ⟨_, hrules, hbk⟩ := Semantics.heldFacts_of_core h
  exact_held c h hf hrules hbk

/-! ## The lemmas that carry the strength -/

/-- **The choice among instances is free.** For a relation T that holds only steps of `Step`,
every step of a rule without existential variables, and for each application of a rule with
existential variables at least one of its instances: a model whose transition at values is T. -/
theorem has_model_choice (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice_held c h hf (Semantics.ruleFactsHeld_of_core h) T hsub hall hsome

/-- A value in the instances of an application is a step by it. -/
theorem famEx_values (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y :=
  let ⟨_, hrules, hbk⟩ := Semantics.heldFacts_of_core h
  famEx_values_held c h hf hrules hbk x y r σ hs hy

/-- The outcomes of a match are, in every model, among any values that hold its steps. -/
theorem famOpen_values (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) :=
  famOpen_values_pp c h hf x r hr (Semantics.ruleFactsHO2_of_core h r hr).1 σ hu hcf ys hys

/-- Where every rule's left side binds every variable, completeness lists values. -/
theorem completeC_closed (c : Semantics) (ref : StepFn) (hop : ∀ r ∈ c.rules, r.opens = []) :
    CompleteC c (fun x => (ref x).map Outcome.val) ↔
      (StepIs c ref → ∀ x : Config c, (Γc c ∪ Γstep c) ⊧
        (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c))))) := by
  have hmap : ∀ v, ((ref v).map Outcome.val).map (Outcome.pat c) = (ref v).map (den c) := fun v => by
    rw [List.map_map]; rfl
  have hval : ∀ (x : Config c) (y : GroundTerm),
      ((∃ (hy : c.sortOf y = some topCellSort) (r : Rule) (σ : Subst), r.opens = [] ∧ StepBy c r σ x ⟨y, hy⟩) ↔
        ∃ hy : c.sortOf y = some topCellSort, Step c x ⟨y, hy⟩) := fun x y =>
    ⟨fun ⟨hy, r, σ, _, hs⟩ => ⟨hy, step_iff_by.mpr ⟨r, σ, hs⟩⟩,
     fun ⟨hy, hs⟩ => let ⟨r, σ, hb⟩ := step_iff_by.mp hs; ⟨hy, r, σ, hop r hb.mem, hb⟩⟩
  have hmem : ∀ (l : List GroundTerm) (y : GroundTerm), Outcome.val y ∈ l.map Outcome.val ↔ y ∈ l :=
    fun l y => by simp
  have hiff : OutIs c (fun x => (ref x).map Outcome.val) ↔ StepIs c ref := by
    constructor
    · intro ho x y
      rw [← hmem, (ho x).1 y, hval]
    · intro hs x
      refine ⟨fun y => ?_, fun r σ hm => ?_, fun r hr hne => absurd (hop r hr) hne⟩
      · rw [hmem, hs x y, hval]
      · simp at hm
  unfold CompleteC
  simp only [hmap]
  rw [hiff]

/-! ## The statements over the plain step -/

/-- **Soundness at a step**, in the plain form: for a semantics `coreOK` accepts that reads no
confined sort, every step of `Step` is a theorem of `Γ c`, `⟦x⟧ → •⟦y⟧`. -/
theorem sound_at_step (c : Semantics) (h : c.coreOK = true) (hrc : c.readsConfined = false)
    (x y : Config c) (hs : Step c x y) :
    Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hod := openDecided_of_readsConfined hrc
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp hs
  obtain ⟨h1, -⟩ := sound_at c h x y r σ hb (fun r' hr' _ hn _ => hod.1 r' hr' hn) hod.2
  have hcl : Γc c ⊧ (famEx c r σ ≡ den c y.val) :=
    famEx_closed c h hb (Semantics.exs_nil_of_opens (Semantics.ruleFactsHO2_of_core h r hb.mem).1
      ((Semantics.opens_of_readsConfined hrc).1 r hb.mem)) hod.2
  rw [Γc_plain hrc] at h1 hcl
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK hI)).mp (hcl hI e m)) (hst hx)

/-- **Completeness at a configuration**, in the plain form: for a semantics `coreOK` accepts that
reads no confined sort, with the step's closure every successor of x is one of `ys`, any list
holding `Step`'s successors of x, where the evaluations the step at x reads have results. -/
theorem complete_at_step (c : Semantics) (h : c.coreOK = true) (hrc : c.readsConfined = false)
    (x : Config c) (hd : StepDecided c x.val)
    (ys : List GroundTerm) (hys : ∀ y : Config c, Step c x y → y.val ∈ ys) :
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den c)))) := by
  have : (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList
      ((ys.map Outcome.val).map (Outcome.pat c)))) := complete_at c h x hd (ys.map Outcome.val)
    (fun y r σ _ hs => List.mem_map_of_mem (hys y (step_iff_by.mpr ⟨r, σ, hs⟩)))
    (fun r hr hne => absurd ((Semantics.opens_of_readsConfined hrc).1 r hr) hne)
    (openDecided_of_readsConfined hrc).2
  have hm : (ys.map Outcome.val).map (Outcome.pat c) = ys.map (den c) := by rw [List.map_map]; rfl
  rw [Γc_plain hrc, hm] at this
  intro M _ I hI
  exact this hI

/-- `sound_at` for a plain definition, at one step: over `Γ`, from `coreOK` and `plain`. -/
theorem sound_at_plain (c : Semantics) (h : c.coreOK = true) (hp : c.plain = true)
    (x y : Config c) (hs : Step c x y) : Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  sound_at_step c h (Semantics.readsConfined_of_plain hp) x y hs

/-- `complete_at` for a plain definition, at one configuration: over `Γ ∪ Γstep`, from `coreOK` and `plain`. -/
theorem complete_at_plain (c : Semantics) (h : c.coreOK = true) (hp : c.plain = true) (x : Config c)
    (hd : StepDecided c x.val) (ys : List GroundTerm) (hys : ∀ y : Config c, Step c x y → y.val ∈ ys) :
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den c)))) :=
  complete_at_step c h (Semantics.readsConfined_of_plain hp) x hd ys hys

/-- `sound_hyp` over `Γ` and the plain step (`SoundC₀`), for a plain definition. -/
theorem sound_hyp₀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (hp : c.plain = true) : SoundC₀ c := by
  have hΓ := Γc_plain (Semantics.readsConfined_of_plain hp)
  obtain ⟨hmod, hsound⟩ := sound_hyp c h hf
  refine ⟨by rw [hΓ] at hmod; exact hmod, fun x y hs => ?_⟩
  obtain ⟨r, σ, hb⟩ := step_iff_by.mp ((step_plain hp x y).mpr hs)
  obtain ⟨h1, -⟩ := hsound x y r σ hb
  have hcl : Γc c ⊧ (famEx c r σ ≡ den c y.val) :=
    famEx_closed c h hb (Semantics.plain_rule hp hb.mem).1 hf.2.2.2.2.1.2
  rw [hΓ] at h1 hcl
  intro M _ I hI e m
  have hst := h1 hI e m
  rw [interpret_impl] at hst ⊢
  intro hx
  exact sNext_congr ((KoreAML.interp_equal (defOK hI)).mp (hcl hI e m)) (hst hx)

/-- `complete_hyp` over `Γ` and the plain step (`CompleteC₀`), for a plain definition. -/
theorem complete_hyp₀ (c : Semantics) (ref : StepFn) (h : c.coreOK = true) (hf : FnHyp c)
    (hp : c.plain = true) : CompleteC₀ c ref := by
  intro href x
  have hΓ := Γc_plain (Semantics.readsConfined_of_plain hp)
  have hop : ∀ r ∈ c.rules, r.opens = [] := fun r hr => Rule.opens_of_binds (Semantics.plain_rule hp hr).2.2.2
  have hs : StepIs c ref := fun x y => by
    rw [href x y]
    exact ⟨fun ⟨hy, hs⟩ => ⟨hy, (step_plain hp _ _).mpr hs⟩, fun ⟨hy, hs⟩ => ⟨hy, (step_plain hp _ _).mp hs⟩⟩
  have : (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (den c)))) :=
    (completeC_closed c ref hop).mp (complete_hyp c _ h hf) hs x
  rwa [hΓ] at this

/-- **The old theorems**, for a definition whose rules and clauses are plain. -/
theorem sound₀ (d : Definition) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false) : SoundC₀ d.sem :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  sound_hyp₀ d.sem (Definition.coreOK_of_wf hwf)
    (fnHyp_of_core (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) (Semantics.rightHeld_of_binds (Semantics.plain_parts hp).2.1) hob) hp
theorem complete₀ (d : Definition) (ref : StepFn) (hwf : wf d = true) (hob : Obligations d)
    (hp : d.sem.plain = true) (hc : d.sem.readsConfined = false) : CompleteC₀ d.sem ref :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  complete_hyp₀ d.sem ref (Definition.coreOK_of_wf hwf)
    (fnHyp_of_core (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) (Semantics.rightHeld_of_binds (Semantics.plain_parts hp).2.1) hob) hp

/-! ## The statements under the named obligations -/

/-- **Soundness of a semantics** that `coreOK` accepts, whose clauses' variables are held
(`RightHeld`), whose clauses' predicates are `\top` (`hpreTop`) and whose named obligations, with
the termination certificate `t`, hold: `sound_hyp`, the obligations giving `FnHyp`
(`fnHyp_of_core`). -/
theorem sound_core (c : Semantics) (t : Certificates) (h : c.coreOK = true) (hrh : c.RightHeld)
    (hob : CoreObligations c t) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) : SoundC c :=
  sound_hyp c h (fnHyp_of_core (hpreTop := hpreTop) h hrh hob)

/-- **Completeness of a semantics** that `coreOK` accepts, whose clauses' variables are held
(`RightHeld`) and whose named obligations, with the termination certificate `t`, hold:
`complete_hyp`, the obligations giving `FnHyp` (`fnHyp_of_core`). -/
theorem complete_core (c : Semantics) (t : Certificates) (ref : OutFn) (h : c.coreOK = true)
    (hrh : c.RightHeld) (hob : CoreObligations c t) (hpreTop : c.clausesPreTop = true := by first | decide +kernel | (simp only [Semantics.clausesPreTop_withHooks]; decide +kernel) | exact rfl) : CompleteC c ref :=
  complete_hyp c ref h (fnHyp_of_core (hpreTop := hpreTop) h hrh hob)

/-! ## The statements for a definition -/

/-- **Soundness** of a definition: `SoundC` of its semantics. -/
def Sound (d : Definition) : Prop := SoundC d.sem

/-- **Completeness** of a definition, for an outcome function `ref`: `CompleteC` of its semantics. -/
def Complete (d : Definition) (ref : OutFn) : Prop := CompleteC d.sem ref

/-- **Exactness** of a definition: `ExactC` of its semantics. -/
def Exact (d : Definition) : Prop := ExactC d.sem

/-- **Soundness of a well-formed definition** whose named obligations hold: `sound_core`, `wf`
giving `coreOK` (`Definition.coreOK_of_wf`). -/
theorem sound (d : Definition) (hwf : wf d = true) (hob : Obligations d)
    (hrh : d.sem.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) : Sound d :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  sound_core (hpreTop := hpreTop) d.sem d.cert (Definition.coreOK_of_wf hwf) hrh hob

/-- `sound` for every interpretation of the parameters, under the obligations stated for that
interpretation, of a definition without an open generator (`hr`, decided on the data). -/
theorem sound_withHooks (d : Definition) (hwf : wf d = true) (H : HookParams)
    (hob : Obligations { d with sem := d.sem.withHooks H })
    (hrh : d.sem.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ d.sem.params, k.raw = false := by decide +kernel) : Sound { d with sem := d.sem.withHooks H } :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  sound _ ((Definition.wf_withHooks d H).trans hwf) hob (Semantics.rightHeld_withHooks hrh H hr)

/-- **Completeness of a well-formed definition** whose named obligations hold: `complete_core`,
`wf` giving `coreOK` (`Definition.coreOK_of_wf`). -/
theorem complete (d : Definition) (ref : OutFn) (hwf : wf d = true) (hob : Obligations d)
    (hrh : d.sem.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) : Complete d ref :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  complete_core (hpreTop := hpreTop) d.sem d.cert ref (Definition.coreOK_of_wf hwf) hrh hob

/-- `complete` for every interpretation of the parameters, under the obligations stated for that
interpretation, of a definition without an open generator (`hr`, decided on the data). -/
theorem complete_withHooks (d : Definition) (ref : OutFn) (hwf : wf d = true) (H : HookParams)
    (hob : Obligations { d with sem := d.sem.withHooks H })
    (hrh : d.sem.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel))
    (hr : ∀ k ∈ d.sem.params, k.raw = false := by decide +kernel) :
    Complete { d with sem := d.sem.withHooks H } ref :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  complete _ ref ((Definition.wf_withHooks d H).trans hwf) hob (Semantics.rightHeld_withHooks hrh H hr)

/-- **Exactness of a well-formed definition** whose named obligations hold: `exact_hyp`, the
obligations giving `FnHyp` (`fnHyp_of_core`). -/
theorem exact (d : Definition) (hwf : wf d = true) (hob : Obligations d)
    (hrh : d.sem.RightHeld := by exact Semantics.rightHeld_of_valued (by decide +kernel)) : Exact d :=
  have hpreTop := Semantics.preTop_of_okAll (NamesApart.wf_parts hwf).2.2.2
  exact_hyp d.sem (Definition.coreOK_of_wf hwf) (fnHyp_of_core (hpreTop := hpreTop) (Definition.coreOK_of_wf hwf) hrh hob)

end KCore
