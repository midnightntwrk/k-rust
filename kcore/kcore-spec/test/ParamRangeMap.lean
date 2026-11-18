/-
  RANGEMAP's three parameters on the fixture e6-param-rangemap's kompiled text
  (`f2-examples/e6-param-rangemap.kompile.kore`, the text whose sha256 the fixture's kompile.txt
  records, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory
  relative to the tree): `choice` (domains.md 682), `keys_list` (634) and `values` (652), each
  applied once by a rule of the text (`go(1, X)`, `go(2, X)`, `go(3, X)`). The reader reads each as
  a parameter symbol no hook implements (`impl = none`, `raw = false`; the fixture's params.txt):
  its value at an argument list is the interpretation's (`paramVal`), and Γ holds its graph
  (`ΓDomains`), ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undetermined`). The pair of models: under `HookParams.none` the
  application is ⊥ in every model of Γ, under `constH v` it is `v` in every model, and both
  theories have models (`sound_hyp`; `FnHyp` holds under every H, the text having no function).
  The points: `choice` and `values` at the map `[0, 3) ↦ 7`, `keys_list` at the same map; the values
  are `7` as a KItem (`choice`) and the list holding it (`keys_list`, `values`). Whatever value the
  prose would name there, none is entailed: the text leaves the chosen key and the lists' order open
  (domains.md 634, 652, 682), and Γ holds the interpretation's value.

  Run from the package root: `lake env lean -j1 test/ParamRangeMap.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamRangeMap

open KCore ML Faithful

/-! ## The schema, at a parameter no hook implements -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev appPR (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts. -/
theorem gamma_paramPR (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (appPR c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- The interpretation that gives `v` everywhere. -/
def constHPR (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a parameter no hook implements and no open generator, the value under H is H's answer,
kept where it has the result sort. -/
theorem paramVal_implNonePR (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
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

/-- **The `param_undetermined` shape** at a parameter no hook implements. Over all
interpretations, Γ entails neither that the application has no value nor that it is `v`: under
`HookParams.none` it is ⊥ in every model, under `constHPR v` it is `v` in every model, and both
theories have models (`sound_hyp`). -/
theorem param_undeterminedPR (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constHPR v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPR (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPR (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks (constHPR v)).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNonePR c hr _ hlk hi]
    simp [constHPR, Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNonePR c hr _ hlk hi]; rfl
  constructor
  · -- under `constHPR v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constHPR v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constHPR v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPR (c.withHooks (constHPR v)) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall (constHPR v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constHPR v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPR (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## The text -/

definition_of defn from "f2-examples/e6-param-rangemap.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := fns_nil
  have hrc : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c.withHooks H) noRaw⟩ <;>
    intro fn hfn <;> rw [h] at hfn <;> exact absurd hfn List.not_mem_nil

/-! ## The three parameters -/

/-- The map `[0, 3) ↦ 7`. -/
def m7 : GroundTerm := rmV [(rangeT 0 3, kint 7)]
/-- The list holding `7`. -/
def l7 : GroundTerm := .list Srt.list [kint 7]

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def choiceK : ParamSig := (paramOf "LblRangeMap'Coln'choice").getD default
noncomputable def keysListK : ParamSig :=
  (paramOf "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").getD default
noncomputable def valuesK : ParamSig :=
  (paramOf "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").getD default

/-- Each is a parameter of the text, looked up by its number, no hook implements it, and `m7` is a
value of its argument sort and `7` (as a KItem) or `l7` a value of its result sort. -/
theorem params_ok :
    (paramOf "LblRangeMap'Coln'choice").isSome = true ∧
    (paramOf "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").isSome = true ∧
    (paramOf "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").isSome = true ∧
    c.lookupParam choiceK.sig.name = some choiceK ∧ c.lookupParam keysListK.sig.name = some keysListK ∧
    c.lookupParam valuesK.sig.name = some valuesK ∧
    choiceK.impl = none ∧ keysListK.impl = none ∧ valuesK.impl = none ∧
    c.sortsOf [m7] = some choiceK.sig.args ∧ c.sortsOf [m7] = some keysListK.sig.args ∧
    c.sortsOf [m7] = some valuesK.sig.args ∧
    c.sortOf (kint 7) = some choiceK.sig.result ∧ c.sortOf l7 = some keysListK.sig.result ∧
    c.sortOf l7 = some valuesK.sig.result := by
  decide +kernel

/-- **`choice(M)` is not determined by the text**: over all H, Γ entails neither that `choice` at
`[0, 3) ↦ 7` has no value nor that it is `7`. -/
theorem choice_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPR (c.withHooks H) choiceK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPR (c.withHooks H) choiceK.sig.name [m7] ≡ den (c.withHooks H) (kint 7))) :=
  param_undeterminedPR c coreOK noRaw params_ok.2.2.2.1 params_ok.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`keys_list(M)` is not determined by the text**: over all H, Γ entails neither that it has no
value at `[0, 3) ↦ 7` nor that it is the list of `7`. -/
theorem keysList_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPR (c.withHooks H) keysListK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPR (c.withHooks H) keysListK.sig.name [m7] ≡ den (c.withHooks H) l7)) :=
  param_undeterminedPR c coreOK noRaw params_ok.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`values(M)` is not determined by the text**: over all H, Γ entails neither that it has no
value at `[0, 3) ↦ 7` nor that it is the list of `7`. -/
theorem values_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPR (c.withHooks H) valuesK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPR (c.withHooks H) valuesK.sig.name [m7] ≡ den (c.withHooks H) l7)) :=
  param_undeterminedPR c coreOK noRaw params_ok.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (fnHyp _) (fnHyp _)

end KCore.ParamRangeMap

/-- info: 'KCore.ParamRangeMap.choice_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.choice_undetermined
/-- info: 'KCore.ParamRangeMap.keysList_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.keysList_undetermined
/-- info: 'KCore.ParamRangeMap.values_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.values_undetermined
