/-
  `has_model_choice`'s and `exact_hyp`'s statements with `coreOKEx` for `coreOK`
  (`has_model_choice_ce`, `exact_ce`, `step_of_successor_ce`), and the forms over the per-rule fact
  `rulePlainHeldH` they are instances of. `coreOK` gives `coreOKEx`, so each gives the statement over
  `coreOK` with no other hypothesis.
-/
import KcoreSpec.ExactHeldCEx

set_option autoImplicit false

namespace KCore.ExactHeldCExTest
open KCore ML Faithful Faithful.Model

/-! ## The statements -/

example : ∀ (c : Semantics), c.coreOKEx = true → FnHyp c → ExactC c := @exact_ce

example : ∀ (c : Semantics), c.coreOKEx = true → FnHyp c → ∀ (T : Config c → Config c → Prop),
    (∀ x y, T x y → Step c x y) →
    (∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y) →
    (∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') →
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  @has_model_choice_ce

example (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y :=
  step_of_successor_ce c h hf hI x y e hs

example (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H) :
    ExactC c := exact_heldCEx c h hf hrules hbk

example (c : Semantics) {H : Sym → Bool} (hm : HypModelCore c) (hp : ClausePreDecided c)
    (hq : ClausePostDecided c) (hl : OpenLaws c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) :
    stdI_T c (StepV c) ⊧ᴵP (Γc c ∪ Γstep c) :=
  stdI_T_model_heldCEx c hm hp hq hl hrules (StepV c) (fun _ _ _ _ hT => hT)
    (fun r σ _ _ hb _ => ⟨r, σ, hb⟩) (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩)

/-! ## Over `coreOK`: the statements of `exact_hyp` and `has_model_choice` -/

example : ∀ (c : Semantics), c.coreOK = true → FnHyp c → ExactC c :=
  fun c h hf => exact_ce c (Semantics.coreOKEx_of_coreOK h) hf

example (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice_ce c (Semantics.coreOKEx_of_coreOK h) hf T hsub hall hsome

/-- info: 'KCore.exact_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_ce
/-- info: 'KCore.has_model_choice_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms has_model_choice_ce
/-- info: 'KCore.step_of_successor_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_of_successor_ce

end KCore.ExactHeldCExTest
