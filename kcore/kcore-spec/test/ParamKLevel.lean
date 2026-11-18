/-
  The K-level parameter symbols on two construct fixtures' kompiled texts (each the text its
  kompile.txt hashes, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's
  directory relative to the tree):

  - `f2-examples/e3-param-cases.kompile.kore` (fixture e3-param-cases): `syntax {S} S ::= pick(Bool,
    S, S)` and `syntax {P} Bool ::= isZeroOf(P, Int)`, whose rules become equations of the instances
    `Lblpick{SortK{}}` and `LblisZeroOf{SortK{}}`, while the rule `a(X) => b(isZeroOf(a(X), pick(true,
    X, 0)))` applies the instances `Lblpick{SortInt{}}` and `LblisZeroOf{SortExp{}}`, of which the
    text states no equation.
  - `f2-examples/e8-hook-namespaces.kompile.kore` (fixture e8-hook-namespaces, `--hook-namespaces
    FOO`): `hooked-symbol Lblfh{}(SortInt{}) : SortInt{}` with `hook{}("FOO.bar")`, a hook no
    registry entry names, and no equation (the text declares it and applies it nowhere).

  The reader reads each of the three as a parameter symbol no hook implements (`impl = none`,
  `raw = false`; `kcore sem-fields` of the text): its value at an argument list is the
  interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undeterminedPK`). The pair of models: under `HookParams.none` the
  application is ⊥ in every model of Γ, under `constHPK v` it is `v` in every model, and both
  theories have models (`sound_hyp`; `FnHyp` holds under every H, each text's functions owing no
  fact: `fnHyp`). The points: `pick{Int}` at `(true, 0, 0)` with `0`, `isZeroOf{Exp}` at `(a(0), 0)`
  with `true`, `fh` at `0` with `0`. Each value is the one the K prose would suggest, and none is
  entailed: the text states no sentence of these instances' graphs.

  Run from the package root: `lake env lean -j1 test/ParamKLevel.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamKLevel

open KCore ML Faithful

/-! ## The schema, at a parameter no hook implements -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev appPK (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts. -/
theorem gamma_paramPK (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (appPK c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- The interpretation that gives `v` everywhere. -/
def constHPK (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a parameter no hook implements and no open generator, the value under H is H's answer,
kept where it has the result sort. -/
theorem paramVal_implNonePK (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
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
`HookParams.none` it is ⊥ in every model, under `constHPK v` it is `v` in every model, and both
theories have models (`sound_hyp`). -/
theorem param_undeterminedPK (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constHPK v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPK (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks (constHPK v)).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNonePK c hr _ hlk hi]
    simp [constHPK, Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNonePK c hr _ hlk hi]; rfl
  constructor
  · -- under `constHPK v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constHPK v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constHPK v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPK (c.withHooks (constHPK v)) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall (constHPK v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constHPK v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPK (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## e3-param-cases: `pick{Int}` and `isZeroOf{Exp}` -/

namespace E3Cases

definition_of defn from "f2-examples/e3-param-cases.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The rank the text's two functions (`pick{K}`, `isZeroOf{K}`) are decided at. -/
def callOrder : List Nat := [387, 388]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (c.withHooks H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- The functions owe no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def pickK : ParamSig := (paramOf "Lblpick{Int}").getD default
noncomputable def isZeroOfK : ParamSig := (paramOf "LblisZeroOf{Exp}").getD default

/-- The constructor `a : Int → Exp`. -/
noncomputable def aSym : Sym := ((c.ctors.find? fun ct => c.symName ct.name == "Lbla").map (·.name)).getD 0

/-- `a(0)`, a value of sort Exp. -/
noncomputable def a0 : GroundTerm := .ctor aSym [int 0]

/-- Each is a parameter of the text, looked up by its number, no hook implements it, the points'
arguments are values of its argument sorts and the given values of its result sort. -/
theorem params_ok :
    (paramOf "Lblpick{Int}").isSome = true ∧ (paramOf "LblisZeroOf{Exp}").isSome = true ∧
    c.lookupParam pickK.sig.name = some pickK ∧ c.lookupParam isZeroOfK.sig.name = some isZeroOfK ∧
    pickK.impl = none ∧ isZeroOfK.impl = none ∧
    c.sortsOf [bool true, int 0, int 0] = some pickK.sig.args ∧
    c.sortsOf [a0, int 0] = some isZeroOfK.sig.args ∧
    c.sortOf (int 0) = some pickK.sig.result ∧ c.sortOf (bool true) = some isZeroOfK.sig.result := by
  decide +kernel

/-- **`pick{Int}(true, 0, 0)` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `0`. -/
theorem pickInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) pickK.sig.name [bool true, int 0, int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) pickK.sig.name [bool true, int 0, int 0] ≡ den (c.withHooks H) (int 0))) :=
  param_undeterminedPK c coreOK noRaw params_ok.2.2.1 params_ok.2.2.2.2.1 params_ok.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`isZeroOf{Exp}(a(0), 0)` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `true`. -/
theorem isZeroOfExp_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) isZeroOfK.sig.name [a0, int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) isZeroOfK.sig.name [a0, int 0] ≡ den (c.withHooks H) (bool true))) :=
  param_undeterminedPK c coreOK noRaw params_ok.2.2.2.1 params_ok.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2 (fnHyp _) (fnHyp _)

end E3Cases

/-! ## e8-hook-namespaces: `fh`, hooked to `FOO.bar` -/

namespace E8HookNs

definition_of defn from "f2-examples/e8-hook-namespaces.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The rank the text's function (`f`) is decided at. -/
def callOrder : List Nat := [397]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (c.withHooks H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- The function owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def fhK : ParamSig := (paramOf "Lblfh").getD default

/-- `fh` is a parameter of the text, looked up by its number, no hook implements it, `0` is a value
of its argument sort and of its result sort. -/
theorem params_ok :
    (paramOf "Lblfh").isSome = true ∧ c.lookupParam fhK.sig.name = some fhK ∧ fhK.impl = none ∧
    c.sortsOf [int 0] = some fhK.sig.args ∧ c.sortOf (int 0) = some fhK.sig.result := by
  decide +kernel

/-- **`fh(0)` is not determined by the text**: over all H, Γ entails neither that it has no value
nor that it is `0`. -/
theorem fh_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPK (c.withHooks H) fhK.sig.name [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPK (c.withHooks H) fhK.sig.name [int 0] ≡ den (c.withHooks H) (int 0))) :=
  param_undeterminedPK c coreOK noRaw params_ok.2.1 params_ok.2.2.1 params_ok.2.2.2.1
    params_ok.2.2.2.2 (fnHyp _) (fnHyp _)

end E8HookNs

end KCore.ParamKLevel

/-- info: 'KCore.ParamKLevel.E3Cases.pickInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E3Cases.pickInt_undetermined
/-- info: 'KCore.ParamKLevel.E3Cases.isZeroOfExp_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E3Cases.isZeroOfExp_undetermined
/-- info: 'KCore.ParamKLevel.E8HookNs.fh_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E8HookNs.fh_undetermined
