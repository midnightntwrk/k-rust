/-
  KCore. The value of a parameter symbol at an interpretation, against a value the text might be
  taken to fix, with no assumption on the parameters of the semantics: the parameter may be an open
  generator (`raw`), whose application at values is a value itself where the interpretation gives
  none, and other parameters may be open generators too. `ParamSchema.param_undetermined` is the
  same shape for a semantics without open generators.

  Γ holds the graph of every parameter at values of its argument sorts (`ParamSchema.gamma_param`).
  At an interpretation `Hw` whose theory has a model (`Consistent`), where the application has the
  value `w`:
  - `param_not_bot_at`: Γ does not entail that the application has no value;
  - `param_not_other_at`: Γ does not entail that the application is `u`, another value of the
    result sort there (distinct values of one sort are distinct elements, `values_apart`;
    `param_other_absurd` in one model of Γ).

  `open_undetermined`: over all interpretations, Γ entails neither that the application has no
  value nor that it is `v`, from one interpretation where it has a value and one where its value is
  not `v`. An instance on an open generator with laws takes both interpretations among those
  satisfying the laws, since Γ has the laws as items at every interpretation.

  `fstH`, the interpretation giving the first argument: at an open generator of two arguments of
  its result sort it satisfies associativity and idempotence at values and gives a value at every
  argument list (`openAssoc_fstH`, `openIdem_fstH`, `openTotal_at_fstH`, `paramVal_fstH`).
-/
import KcoreSpec.ParamSchema
import KcoreSpec.LawHooks

set_option autoImplicit false

namespace KCore

open KCore ML Faithful ParamSchema

/-- At an interpretation `Hw` whose theory has a model, where the parameter's application at `vs`
has a value, Γ does not entail that it has none. -/
theorem param_not_bot_at (c : Semantics) {k : ParamSig} (hk : k ∈ c.params)
    {vs : List GroundTerm} {w : GroundTerm} {Hw : HookParams}
    (hc : Consistent (c.withHooks Hw))
    (hvs : (c.withHooks Hw).sortsOf vs = some k.sig.args)
    (hw : (c.withHooks Hw).paramVal k.sig.name vs = some w) :
    ¬ (Γ (c.withHooks Hw) ⊧ (paramApp (c.withHooks Hw) k.sig.name vs ≡ ⊥)) := by
  intro hent
  obtain ⟨M, _, I, hI⟩ := hc
  have hIΓ : I ⊧ᴵP Γ (c.withHooks Hw) := fun φ h => hI φ (Or.inl (Or.inl h))
  have hD := defOK hIΓ
  obtain ⟨k', -, hwH⟩ := Semantics.paramVal_sorted _ hw
  have hgp := hIΓ _ (gamma_param (c.withHooks Hw) (k := k) hk hvs)
  rw [hw] at hgp
  have hbot := hent hIΓ
  have h1 := (KoreAML.interp_equal hD).mp (hgp KoreAML.val0 default) (elemOf (c.withHooks Hw) I w)
  have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) (elemOf (c.withHooks Hw) I w)
  have hwe := ((elemOf_spec hIΓ hwH KoreAML.val0).1 _).mpr rfl
  exact absurd (h2.mp (h1.mpr hwe)) (by simp [Pattern.interpret])

/-- In a model of Γ at `Hw`, where the parameter's application at `vs` has the value `w`, the
application is not `u`, another value of the result sort there. -/
theorem param_other_absurd (c : Semantics) (hok : c.coreOK = true) {k : ParamSig} (hk : k ∈ c.params)
    {vs : List GroundTerm} {u w : GroundTerm} {Hw : HookParams}
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hIΓ : I ⊧ᴵP Γ (c.withHooks Hw))
    (hvs : (c.withHooks Hw).sortsOf vs = some k.sig.args)
    (hw : (c.withHooks Hw).paramVal k.sig.name vs = some w)
    (hlk : (c.withHooks Hw).lookupParam k.sig.name = some k)
    (hu : (c.withHooks Hw).sortOf u = some k.sig.result) (hne : u ≠ w) :
    ¬ (I ⊧ᴵ (paramApp (c.withHooks Hw) k.sig.name vs ≡ den (c.withHooks Hw) u)) := by
  intro hval
  have hD := defOK hIΓ
  have hokH : (c.withHooks Hw).coreOK = true := (Semantics.coreOK_withHooks c _).trans hok
  obtain ⟨hsok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core hokH
  haveI : OvlOK (c.withHooks Hw) := hno
  have hsc := sortCtx_of_all hsok hsr (OvlOK.ovlCase hno)
  have hwH : (c.withHooks Hw).sortOf w = some k.sig.result := by
    obtain ⟨k', hk', hs⟩ := Semantics.paramVal_sorted _ hw
    rw [hlk] at hk'; cases hk'; exact hs
  have hgp := hIΓ _ (gamma_param (c.withHooks Hw) (k := k) hk hvs)
  rw [hw] at hgp
  have h1 := (KoreAML.interp_equal hD).mp (hgp KoreAML.val0 default) (elemOf (c.withHooks Hw) I w)
  have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) (elemOf (c.withHooks Hw) I w)
  have hwe := ((elemOf_spec hIΓ hwH KoreAML.val0).1 _).mpr rfl
  have hue := ((elemOf_spec hIΓ hu KoreAML.val0).1 _).mp (h2.mp (h1.mpr hwe))
  exact hne (values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hu) hu hwH hue.symm)

/-- At an interpretation `Hw` whose theory has a model, where the parameter's application at `vs`
has the value `w`, Γ does not entail that it is `u`, another value of the result sort there. -/
theorem param_not_other_at (c : Semantics) (hok : c.coreOK = true) {k : ParamSig} (hk : k ∈ c.params)
    {vs : List GroundTerm} {u w : GroundTerm} {Hw : HookParams}
    (hc : Consistent (c.withHooks Hw))
    (hvs : (c.withHooks Hw).sortsOf vs = some k.sig.args)
    (hw : (c.withHooks Hw).paramVal k.sig.name vs = some w)
    (hlk : (c.withHooks Hw).lookupParam k.sig.name = some k)
    (hu : (c.withHooks Hw).sortOf u = some k.sig.result) (hne : u ≠ w) :
    ¬ (Γ (c.withHooks Hw) ⊧ (paramApp (c.withHooks Hw) k.sig.name vs ≡ den (c.withHooks Hw) u)) := by
  intro hent
  obtain ⟨M, _, I, hI⟩ := hc
  have hIΓ : I ⊧ᴵP Γ (c.withHooks Hw) := fun φ h => hI φ (Or.inl (Or.inl h))
  exact param_other_absurd c hok hk hIΓ hvs hw hlk hu hne (hent hIΓ)

/-- **`open_undetermined`**: at a parameter symbol of `c`, an open generator or not, at the
argument list `vs`, over all interpretations Γ entails neither that the application has no value
nor that it is `v`. Under `H₁` the application has a value in every model of Γ; under `H₂` its
value is `w`, a value other than `v` of the result sort; both theories have models. -/
theorem open_undetermined (c : Semantics) (hok : c.coreOK = true) {k : ParamSig} (hk : k ∈ c.params)
    (hlk : c.lookupParam k.sig.name = some k)
    {vs : List GroundTerm} {v w₁ w : GroundTerm} {H₁ H₂ : HookParams}
    (hc₁ : Consistent (c.withHooks H₁)) (hvs₁ : (c.withHooks H₁).sortsOf vs = some k.sig.args)
    (hw₁ : (c.withHooks H₁).paramVal k.sig.name vs = some w₁)
    (hc₂ : Consistent (c.withHooks H₂)) (hvs₂ : (c.withHooks H₂).sortsOf vs = some k.sig.args)
    (hw₂ : (c.withHooks H₂).paramVal k.sig.name vs = some w)
    (hv : (c.withHooks H₂).sortOf v = some k.sig.result) (hne : v ≠ w) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) :=
  ⟨fun hall => param_not_bot_at c hk hc₁ hvs₁ hw₁ (hall H₁),
   fun hall => param_not_other_at c hok hk hc₂ hvs₂ hw₂ hlk hv hne (hall H₂)⟩

/-! ## The interpretation giving the first argument -/

/-- The interpretation that gives, at every symbol, its first argument. -/
def fstH : HookParams := ⟨fun _ vs => vs.head?⟩

section
variable {c : Semantics} {k : ParamSig}

/-- **An open generator's value at `fstH`**: the first argument, at arguments of its argument sorts
where the first is of its result sort. -/
theorem paramVal_fstH (hs : LawShape c k) (hr : k.raw = true) {a : GroundTerm} {vs : List GroundTerm}
    (ha : (c.withHooks fstH).sortOf a = some k.sig.result) :
    (c.withHooks fstH).paramVal k.sig.name (a :: vs) = some a :=
  (paramVal_raw_sorted (c := c.withHooks fstH) hs.1 hr hs.2.2.1).mpr ⟨rfl, ha⟩

/-- `fstH` is associative at values, at an open generator of two arguments of its result sort. -/
theorem openAssoc_fstH (hs : LawShape c k) (hr : k.raw = true) :
    OpenAssoc (c.withHooks fstH) k.sig.name k.sig.result := by
  intro a b d hsorts
  obtain ⟨hsa, hsb, -⟩ := sorts3 hsorts
  rw [paramVal_fstH hs hr hsa, paramVal_fstH hs hr hsb, Option.bind_some, Option.bind_some,
    paramVal_fstH hs hr hsa, paramVal_fstH hs hr hsa]

/-- `fstH` is idempotent at values, at an open generator of two arguments of its result sort. -/
theorem openIdem_fstH (hs : LawShape c k) (hr : k.raw = true) :
    OpenIdem (c.withHooks fstH) k.sig.name k.sig.result :=
  fun _ ha => paramVal_fstH hs hr ha

/-- `fstH` gives an open generator of two arguments of its result sort a value at every argument
list of its sorts. -/
theorem openTotal_at_fstH (hs : LawShape c k) (hr : k.raw = true)
    (hb : k.sig.args = [k.sig.result, k.sig.result]) {vs : List GroundTerm}
    (hvs : (c.withHooks fstH).sortsOf vs = some k.sig.args) :
    ((c.withHooks fstH).paramVal k.sig.name vs).isSome = true := by
  rw [hb] at hvs
  obtain ⟨a, b, rfl, hsa, -⟩ := sorts2 hvs
  rw [paramVal_fstH hs hr hsa]; rfl

end

end KCore
