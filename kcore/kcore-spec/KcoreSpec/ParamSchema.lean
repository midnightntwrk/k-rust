/-
  The `param_undetermined` shape (DONE-0 C2, row `parameter`; C7 form (c)) at a parameter symbol no
  hook implements (`impl = none`), in every semantics `coreOK` accepts whose parameters are no open
  generator.

  A parameter symbol with `impl = none` and `raw = false` has, at an argument list of its sorts, the
  interpretation's value, kept where it has the result sort (`Semantics.paramVal`,
  `paramVal_implNone`), and Γ holds that graph (`gamma_param`): the application equals the value's
  element, or ⊥ where the interpretation gives none. So the text fixes no value there: over all
  interpretations H, Γ entails neither that the application has no value nor that it is a given
  value `v` of the result sort (`param_undetermined`). The pair of models: under `HookParams.none`
  the application is ⊥ in every model of Γ, under an interpretation giving `v` at that point it is
  `v` in every model, and both theories have models (`sound_hyp`, from `coreOK` and `FnHyp` at the
  two interpretations).

  Two interpretations that give `v` are named: `constH v`, `v` at every point
  (`param_undetermined_const`), and `pointH f vs v`, `v` at the one point and nothing elsewhere
  (`param_undetermined_point`), which differs from `HookParams.none` only there.

  `FnHyp` under every interpretation, from facts decided on the data: where the text has no
  function (`fnHyp_of_fns_nil`), and where the deciders name no fact at a call order
  (`fnHyp_decided`).

  An instance at the parameter named `n` reads its facts of the text as one decided test
  (`paramOK`: the parameter named, looked up by its number, no hook implementing it, the point's
  arguments values of its argument sorts and the given value one of its result sort), closed by
  `undetermined_of_paramOK`.
-/
import KcoreSpec.Sound
import KcoreSpec.FnObligations
import KcoreSpec.FaithfulStage1
import KcoreSpec.TotalsG
import KcoreSpec.RightHeld
import KcoreSpec.ParamsTotal
import KcoreSpec.Obligations
import KcoreSpec.DecreasingL
import KcoreSpec.CallGroups
import KcoreSpec.AgreeInst
import KcoreSpec.UniqLists

set_option autoImplicit false

namespace KCore.ParamSchema

open KCore ML Faithful

/-! ## Γ at a parameter's application -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev paramApp (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts: its value's
element, or ⊥ where it has none. -/
theorem gamma_param (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (paramApp c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- At a parameter no hook implements, in a semantics with no open generator, the value under H is
H's answer, kept where it has the result sort. -/
theorem paramVal_implNone (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    (vs : List GroundTerm) :
    (c.withHooks H).paramVal k.sig.name vs = (H.app k.sig.name vs).filter
      fun v => c.sortOf v == some k.sig.result := by
  have hk : k ∈ c.params := by
    rw [Semantics.lookupParam_eq] at hlk; exact List.mem_of_find?_eq_some hlk
  have hl : (c.withHooks H).lookupParam k.sig.name = some k := hlk
  unfold Semantics.paramVal
  rw [hl]
  simp only [hi, hr k hk, Bool.false_eq_true, ite_false, Semantics.sortOf_withHooks c H hr]
  rfl

/-! ## The schema -/

/-- **`param_undetermined`**: at a parameter symbol no hook implements, at values `vs` of its
argument sorts, over all interpretations Γ entails neither that the application has no value nor
that it is `v`, a value of its result sort. Under `HookParams.none` it is ⊥ in every model of Γ;
under `Hv`, any interpretation giving `v` at `vs`, it is `v` in every model; both theories have
models (`sound_hyp`, from `coreOK` and `FnHyp` at the two interpretations). -/
theorem param_undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    {Hv : HookParams} (hHv : Hv.app k.sig.name vs = some v)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks Hv)) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks Hv).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNone c hr _ hlk hi, hHv]
    simp [Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNone c hr _ hlk hi]; rfl
  constructor
  · -- under `Hv` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks Hv) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks Hv) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_param (c.withHooks Hv) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall Hv hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks Hv)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_param (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## Two interpretations giving `v` -/

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- The interpretation that gives `v` at `f` applied to `vs` and nothing elsewhere. -/
def pointH (f : Sym) (vs : List GroundTerm) (v : GroundTerm) : HookParams :=
  ⟨fun g ws => if g = f ∧ ws = vs then some v else none⟩

/-- `param_undetermined` with `constH v` as the interpretation giving `v`. -/
theorem param_undetermined_const (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) :=
  param_undetermined c hok hr hlk hi hvs hv (Hv := constH v) rfl hfn₀ hfnv

/-- `param_undetermined` with `pointH k.sig.name vs v` as the interpretation giving `v`: it differs
from `HookParams.none` at the one point. -/
theorem param_undetermined_point (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (pointH k.sig.name vs v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) :=
  param_undetermined c hok hr hlk hi hvs hv (Hv := pointH k.sig.name vs v) (by simp [pointH]) hfn₀ hfnv

/-! ## `FnHyp` under every interpretation, decided on the data -/

/-- In a semantics with no function, no open generator and no definition reading a confined sort,
`FnHyp` holds under every interpretation. -/
theorem fnHyp_of_fns_nil (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (hf : c.fns = [])
    (hrc : c.readsConfined = false) (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := hf
  have hrcH : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans hrc
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrcH, openLaws_of_plain (c := c.withHooks H) hr⟩ <;>
    intro fn hfn <;> rw [h] at hfn <;> exact absurd hfn List.not_mem_nil

/-- With no fact named by the deciders at the call order `ord` (termination, totality, agreement,
match independence), `FnHyp` holds under every interpretation. -/
theorem fnHyp_decided (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hrv : c.rightValued = true) (hpre : c.clausesPreTop = true) (hplain : c.plain = true)
    {ord : List Sym} (h1 : c.rankObligations ord ++ c.decObligationsL = [])
    (h2 : c.totalObligationsRP ord [] = []) (h3 : c.agreeObligationsI = [])
    (h4 : c.matchObligationsL = ([] : List (Nat × Nat))) (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_withHooks hok (Semantics.rightHeld_of_valued hrv) H ParamsTotal.nil
    (FnObligations.of_nil
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans h2)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans h3)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans h4)
      ((Semantics.plain_withHooks c H).trans hplain)) hr hpre

/-! ## An instance, decided on the text -/

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
def paramNamed (c : Semantics) (n : String) : ParamSig :=
  (c.params.find? fun k => c.symName k.sig.name == n).getD default

/-- What an instance asks of the text, as one decided test: the parameter named `n` is the one
`lookupParam` finds by its number, no hook implements it, `vs` are values of its argument sorts and
`v` a value of its result sort. -/
def paramOK (c : Semantics) (n : String) (vs : List GroundTerm) (v : GroundTerm) : Bool :=
  c.symName (paramNamed c n).sig.name == n &&
    c.lookupParam (paramNamed c n).sig.name == some (paramNamed c n) &&
    (paramNamed c n).impl == none && c.sortsOf vs == some (paramNamed c n).sig.args &&
    c.sortOf v == some (paramNamed c n).sig.result

/-- `param_undetermined_const` at the parameter named `n`, from the decided test `paramOK`. -/
theorem undetermined_of_paramOK (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hfn : ∀ H : HookParams, FnHyp (c.withHooks H)) {n : String} {vs : List GroundTerm} {v : GroundTerm}
    (h : paramOK c n vs v = true) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) (paramNamed c n).sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c n).sig.name vs ≡ den (c.withHooks H) v)) := by
  simp only [paramOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hl⟩, hi⟩, hvs⟩, hv⟩ := h
  exact param_undetermined_const c hok hr hl hi hvs hv (hfn _) (hfn _)

end KCore.ParamSchema
