/-
  The `param_undetermined` shape (findings/REVIEW-RN-reading-notes.md section 3, G6; DONE-0 C2, row
  `parameter`; C7 form (c)) at a parameter symbol no hook implements (`impl = none`), in every
  semantics `coreOK` accepts whose parameters are no open generator. Run from the package root:
  `lake env lean -j1 test/GuardsParam.lean`.

  A parameter symbol with `impl = none` and `raw = false` has, at an argument list of its sorts, the
  interpretation's value, kept where it has the result sort (`Semantics.paramVal`,
  `paramVal_implNone`), and Γ holds that graph (`gamma_param`): the application equals the value's
  element, or ⊥ where the interpretation gives none. So the text fixes no value there: over all
  interpretations H, Γ entails neither that the application has no value nor that it is a given
  value `v` of the result sort (`param_undetermined`). The pair of models: under `HookParams.none`
  the application is ⊥ in every model of Γ, under an interpretation giving `v` at that point it is
  `v` in every model, and both theories have models (`sound_hyp`, from `coreOK` and `FnHyp` at the
  two interpretations).

  Two interpretations that give `v` are named, so that `FnHyp` is asked where a text needs it:
  `constH v`, `v` at every point (`param_undetermined_const`, the form of test/HooksList.lean's
  `undetermined`), and `pointH f vs v`, `v` at the one point and nothing elsewhere
  (`param_undetermined_point`), which differs from `HookParams.none` only there. Where the text has
  no function, `FnHyp` holds under every interpretation (`fnHyp_of_fns_nil`). Each other hypothesis
  is a decidable fact about the data (`coreOK`, the parameters' `raw`, the lookup, `impl`, the sorts),
  closed on a text's literal by `decide +kernel` (or `decide_cheap` for `coreOK`).

  The instance below (`OneParam`, a semantics with one parameter `P : Int → Int` and no function)
  closes every hypothesis so: `P(0)` is not determined.
-/
import KcoreSpec

set_option autoImplicit false

namespace KCore.Guards

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

/-! ## `FnHyp` where the text has no function -/

/-- In a semantics with no function, no open generator and no definition reading a confined sort,
`FnHyp` holds under every interpretation. -/
theorem fnHyp_of_fns_nil (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (hf : c.fns = [])
    (hrc : c.readsConfined = false) (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := hf
  have hrcH : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans hrc
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrcH, openLaws_of_plain (c := c.withHooks H) hr⟩ <;>
    intro fn hfn <;> rw [h] at hfn <;> exact absurd hfn List.not_mem_nil

/-! ## An instance: one parameter `P : Int → Int`, no function -/

namespace OneParam

/-- A semantics with the configuration `<k> K </k>`, the generated counter and one parameter symbol
`P : Int → Int` that no hook implements. -/
def P : Sym := nRegSyms + 4
def kP : ParamSig := ⟨⟨P, [Srt.int], Srt.int⟩, none, false, false, false⟩
def nc : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "LblP"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
    ctors := [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
      ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
      ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
    fns := []
    params := [kP]
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [] }

theorem nc_coreOK : nc.coreOK = true := by decide_cheap
theorem nc_noRaw : ∀ k ∈ nc.params, k.raw = false := by decide +kernel
theorem nc_fns : nc.fns = [] := rfl
theorem nc_readsConfined : nc.readsConfined = false := by decide +kernel

/-- **`P(0)` is not determined**: over all interpretations Γ entails neither `P(0) = ⊥` nor
`P(0) = 0`. -/
theorem P0_undetermined :
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧ (paramApp (nc.withHooks H) kP.sig.name [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (nc.withHooks H) ⊧
      (paramApp (nc.withHooks H) kP.sig.name [int 0] ≡ den (nc.withHooks H) (int 0))) :=
  param_undetermined_point nc nc_coreOK nc_noRaw (k := kP) (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) (fnHyp_of_fns_nil nc nc_noRaw nc_fns nc_readsConfined _)
    (fnHyp_of_fns_nil nc nc_noRaw nc_fns nc_readsConfined _)

end OneParam

end KCore.Guards

/-- info: 'KCore.Guards.param_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Guards.param_undetermined
/-- info: 'KCore.Guards.param_undetermined_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Guards.param_undetermined_const
/-- info: 'KCore.Guards.param_undetermined_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Guards.param_undetermined_point
/-- info: 'KCore.Guards.OneParam.P0_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Guards.OneParam.P0_undetermined
