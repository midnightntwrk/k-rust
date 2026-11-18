/-
  The parameter hooks of FLOAT, STRING, MAP, BYTES, SET and INT on the construct fixtures
  e6-param-float, e6-param-string, e6-param-map, e6-param-bytes, e6-param-set and e6-param-int
  (`f2-examples/e6-param-*.kompile.kore`, each the text its fixture's kompile.txt hashes, BUILTIN/
  restored as K's builtin directory and FIXTURE/ as the fixture's directory relative to the tree).
  Each text applies every hooked function of its module that no registry hook interprets once, in a
  rule's right side (`go(N, …)`); the reader reads each as a parameter symbol no hook implements
  (`impl = none`, `raw = false`; the fixture's params.txt): its value at an argument list is the
  interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undeterminedPL`). The pair of models: under `HookParams.none` the
  application is ⊥ in every model of Γ, under `constHPL v` it is `v` in every model, and both
  theories have models (`sound_hyp`). An instance reads its facts of the text as one decided test
  (`okPL`: the parameter named, looked up by its number, no hook implementing it, the point's
  arguments values of its argument sorts and the given value one of its result sort).

  `FnHyp` under every H: the texts of FLOAT, STRING, MAP, BYTES and SET have no function
  (`fnHyp_of_fnsNilPL`). INT's has one, K's `append` (`srandInt` gives a K, so the rule's right
  side appends it to the rest of the cell), declared total, which the totality decider confirms
  (its clauses cover K × K, the cover check splitting K over `kseq` and `dotk`); the deciders name
  no fact (`fnHyp_decidedPL`).

  The points are values of the argument sorts (`1`, `"a"`, `0.0`, `b"a"`, `1 |-> 7`,
  `SetItem(1)`, `ListItem(1)`, the Id `x`) and the given values one of the result sort. Whatever
  value the K prose would name there, none is entailed: the text states no sentence of these
  symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamE6Lib.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE6Lib

open KCore ML Faithful

/-! ## The schema, at a parameter no hook implements -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev appPL (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts. -/
theorem gamma_paramPL (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (appPL c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- The interpretation that gives `v` everywhere. -/
def constHPL (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a parameter no hook implements and no open generator, the value under H is H's answer,
kept where it has the result sort. -/
theorem paramVal_implNonePL (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
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
`HookParams.none` it is ⊥ in every model, under `constHPL v` it is `v` in every model, and both
theories have models (`sound_hyp`). -/
theorem param_undeterminedPL (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constHPL v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPL (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks (constHPL v)).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNonePL c hr _ hlk hi]
    simp [constHPL, Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNonePL c hr _ hlk hi]; rfl
  constructor
  · -- under `constHPL v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constHPL v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constHPL v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPL (c.withHooks (constHPL v)) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall (constHPL v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constHPL v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPL (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## An instance, decided on the text -/

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
def paramPL (c : Semantics) (n : String) : ParamSig :=
  (c.params.find? fun k => c.symName k.sig.name == n).getD default

/-- What an instance asks of the text, as one decided test: the parameter named `n` is the one
`lookupParam` finds by its number, no hook implements it, `vs` are values of its argument sorts and
`v` a value of its result sort. -/
def okPL (c : Semantics) (n : String) (vs : List GroundTerm) (v : GroundTerm) : Bool :=
  c.symName (paramPL c n).sig.name == n && c.lookupParam (paramPL c n).sig.name == some (paramPL c n) &&
    (paramPL c n).impl == none && c.sortsOf vs == some (paramPL c n).sig.args &&
    c.sortOf v == some (paramPL c n).sig.result

/-- `param_undeterminedPL` at the parameter named `n`, from the decided test `okPL`. -/
theorem undetermined_of_okPL (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hfn : ∀ H : HookParams, FnHyp (c.withHooks H)) {n : String} {vs : List GroundTerm} {v : GroundTerm}
    (h : okPL c n vs v = true) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPL (c.withHooks H) (paramPL c n).sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c n).sig.name vs ≡ den (c.withHooks H) v)) := by
  simp only [okPL, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hl⟩, hi⟩, hvs⟩, hv⟩ := h
  exact param_undeterminedPL c hok hr hl hi hvs hv (hfn _) (hfn _)

/-- With no function and no condition reading an open generator, `FnHyp` holds under every
interpretation. -/
theorem fnHyp_of_fnsNilPL (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (hfns : c.fns = [])
    (hrc : c.readsConfined = false) (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := hfns
  have hrcH : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans hrc
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrcH, openLaws_of_plain (c := c.withHooks H) hr⟩ <;>
    intro fn hfn <;> rw [h] at hfn <;> exact absurd hfn List.not_mem_nil

/-! ## The points -/

def strV : GroundTerm := .dv Srt.string (.tok "a")
/-- The Float `0.0` of double precision. -/
def floatV : GroundTerm := .dv Srt.float (.float 53 11 0)
def bytesV : GroundTerm := .dv Srt.bytes (.tok "a")
def idV : GroundTerm := .dv Srt.ident (.tok "x")
def mapV : GroundTerm := .map Srt.map [(kint 1, kint 7)]
def setV : GroundTerm := .set Srt.set [kint 1]
def listV : GroundTerm := .list Srt.list [kint 1]
/-- The empty K. -/
def kDot : GroundTerm := .ctor dotk []
def ioIntV : GroundTerm := .inj Srt.int Srt.ioInt (int 1)
def ioStrV : GroundTerm := .inj Srt.string Srt.ioString strV
/-- The symbol named `n`, by number. -/
def symPL (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0
/-- `#tempFile("a", 1)`. -/
def ioFileV (c : Semantics) : GroundTerm := .ctor (symPL c "Lbl'Hash'tempFile") [strV, int 1]
/-- `#ffi_sint`. -/
def ffiTypeV (c : Semantics) : GroundTerm := .ctor (symPL c "Lbl'Hash'ffi'Unds'sint") []
/-- JSON's `null`. -/
def jsonV (c : Semantics) : GroundTerm := .ctor (symPL c "LblJSONnull") []


/-! ## `FnHyp` by the deciders -/

/-- With no fact named by the deciders at the call order `ord` (termination, totality, agreement,
match independence), `FnHyp` holds under every interpretation. -/
theorem fnHyp_decidedPL (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
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

/-! ## e6-param-float: FLOAT -/

namespace Float6

definition_of defn from "f2-examples/e6-param-float.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPL c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem powFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsXor-'Float'UndsUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 1. -/
theorem float2Int_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloat2Int'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem acosFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblacosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem asinFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblasinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem atan2Float_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblatan2Float'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem atanFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblatanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem cosFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblcosFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem expFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblexpFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 1. -/
theorem exponentFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblexponentFloat'LParUndsRParUnds'FLOAT'Unds'Int'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem logFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbllogFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem maxFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblmaxFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 0.0) nor that it is 0.0. -/
theorem minFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblminFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Float").sig.name [floatV, floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, 1) nor that it is 0.0. -/
theorem rootFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int").sig.name [floatV, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblrootFloat'LParUndsCommUndsRParUnds'FLOAT'Unds'Float'Unds'Float'Unds'Int").sig.name [floatV, int 1] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is true. -/
theorem signFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsignFloat'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem sinFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsinFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is 0.0. -/
theorem tanFloat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbltanFloat'LParUndsRParUnds'FLOAT'Unds'Float'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end Float6

/-! ## e6-param-string: STRING -/

namespace String6

definition_of defn from "f2-examples/e6-param-string.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPL c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is "a". -/
theorem base2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBase2String'LParUndsCommUndsRParUnds'STRING-COMMON'Unds'String'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0) nor that it is "a". -/
theorem float2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float").sig.name [floatV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloat2String'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'Float").sig.name [floatV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblFloatFormat` is not determined by the text**: over all H, Γ entails neither that it has
no value at (0.0, "a") nor that it is "a". -/
theorem floatFormat_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloatFormat").sig.name [floatV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblFloatFormat").sig.name [floatV, strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the Id `x`) nor that it is "a". -/
theorem id2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id").sig.name [idV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblId2String'LParUndsRParUnds'ID-COMMON'Unds'String'Unds'Id").sig.name [idV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 0.0. -/
theorem string2Float_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Float'LParUndsRParUnds'STRING-COMMON'Unds'Float'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (floatV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the Id `x`. -/
theorem string2Id_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Id'LParUndsRParUnds'ID-COMMON'Unds'Id'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (idV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is "a". -/
theorem categoryChar_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblcategoryChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is "a". -/
theorem directionalityChar_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbldirectionalityChar'LParUndsRParUnds'STRING-COMMON'Unds'String'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblnewUUID'Unds'STRING-COMMON'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is "a". -/
theorem newUUID_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblnewUUID'Unds'STRING-COMMON'Unds'String").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblnewUUID'Unds'STRING-COMMON'Unds'String").sig.name [] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end String6

/-! ## e6-param-map: MAP -/

namespace Map6

definition_of defn from "f2-examples/e6-param-map.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPL c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is 1 |-> 7. -/
theorem differenceMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds'-Map'UndsUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (mapV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is true. -/
theorem inclusionMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds-LT-Eqls'Map'UndsUnds'MAP'Unds'Bool'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblMap'Coln'choice` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is 1 (a KItem). -/
theorem choiceMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblMap'Coln'choice").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblMap'Coln'choice").sig.name [mapV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is ListItem(1). -/
theorem keysListMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblkeys'Unds'list'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7, 1 |-> 7) nor that it is 1 |-> 7. -/
theorem updateMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblupdateMap'LParUndsCommUndsRParUnds'MAP'Unds'Map'Unds'Map'Unds'Map").sig.name [mapV, mapV] ≡ den (c.withHooks H) (mapV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 |-> 7) nor that it is ListItem(1). -/
theorem valuesMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lblvalues'LParUndsRParUnds'MAP'Unds'List'Unds'Map").sig.name [mapV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end Map6

/-! ## e6-param-bytes: BYTES -/

namespace Bytes6

definition_of defn from "f2-examples/e6-param-bytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPL c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is "a". -/
theorem bytes2Hex_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBytes2Hex'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is "a". -/
theorem bytes2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblBytes2String'LParUndsRParUnds'BYTES-HOOKED'Unds'String'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is b"a". -/
theorem string2Bytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblString2Bytes'LParUndsRParUnds'BYTES-HOOKED'Unds'Bytes'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", b"a") nor that it is "a". -/
theorem decodeBytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes").sig.name [strV, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LbldecodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'String'Unds'String'Unds'Bytes").sig.name [strV, bytesV] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is b"a". -/
theorem encodeBytes_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblencodeBytes'LParUndsCommUndsRParUnds'BYTES-STRING-ENCODE'Unds'Bytes'Unds'String'Unds'String").sig.name [strV, strV] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end Bytes6

/-! ## e6-param-set: SET -/

namespace Set6

definition_of defn from "f2-examples/e6-param-set.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPL c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List` is not determined by the text**: over all H, Γ entails neither that it has
no value at (ListItem(1)) nor that it is SetItem(1). -/
theorem list2Set_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List").sig.name [listV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblList2Set'LParUndsRParUnds'COLLECTIONS'Unds'Set'Unds'List").sig.name [listV] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblSet'Coln'choice` is not determined by the text**: over all H, Γ entails neither that it has
no value at (SetItem(1)) nor that it is 1 (a KItem). -/
theorem choiceSet_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblSet'Coln'choice").sig.name [setV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblSet'Coln'choice").sig.name [setV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set` is not determined by the text**: over all H, Γ entails neither that it has
no value at (SetItem(1)) nor that it is ListItem(1). -/
theorem set2List_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set").sig.name [setV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblSet2List'LParUndsRParUnds'COLLECTIONS'Unds'List'Unds'Set").sig.name [setV] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end Set6

/-! ## e6-param-int: INT -/

namespace Int6

definition_of defn from "f2-examples/e6-param-int.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 385) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPL c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Tild'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1. -/
theorem notInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Tild'Int'Unds'").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Tild'Int'Unds'").sig.name [int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Unds'xorInt'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem xorInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds'xorInt'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'Unds'xorInt'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'UndsAnd-'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem andInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsAnd-'Int'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsAnd-'Int'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'UndsPipe'Int'Unds'` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is 1. -/
theorem orInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsPipe'Int'Unds'").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "Lbl'UndsPipe'Int'Unds'").sig.name [int 1, int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1. -/
theorem randInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblrandInt'LParUndsRParUnds'INT-COMMON'Unds'Int'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem srandInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPL (c.withHooks H) (paramPL c "LblsrandInt'LParUndsRParUnds'INT-COMMON'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPL c coreOK noRaw fnHyp (by decide +kernel)

end Int6

end KCore.ParamE6Lib

/-- info: 'KCore.ParamE6Lib.Float6.powFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.powFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.float2Int_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.float2Int_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.acosFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.acosFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.asinFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.asinFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.atan2Float_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.atan2Float_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.atanFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.atanFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.cosFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.cosFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.expFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.expFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.exponentFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.exponentFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.logFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.logFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.maxFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.maxFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.minFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.minFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.rootFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.rootFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.signFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.signFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.sinFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.sinFloat_undetermined
/-- info: 'KCore.ParamE6Lib.Float6.tanFloat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Float6.tanFloat_undetermined
/-- info: 'KCore.ParamE6Lib.String6.base2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.base2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.float2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.float2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.floatFormat_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.floatFormat_undetermined
/-- info: 'KCore.ParamE6Lib.String6.id2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.id2String_undetermined
/-- info: 'KCore.ParamE6Lib.String6.string2Float_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.string2Float_undetermined
/-- info: 'KCore.ParamE6Lib.String6.string2Id_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.string2Id_undetermined
/-- info: 'KCore.ParamE6Lib.String6.categoryChar_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.categoryChar_undetermined
/-- info: 'KCore.ParamE6Lib.String6.directionalityChar_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.directionalityChar_undetermined
/-- info: 'KCore.ParamE6Lib.String6.newUUID_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.String6.newUUID_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.differenceMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.differenceMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.inclusionMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.inclusionMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.choiceMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.choiceMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.keysListMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.keysListMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.updateMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.updateMap_undetermined
/-- info: 'KCore.ParamE6Lib.Map6.valuesMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Map6.valuesMap_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.bytes2Hex_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.bytes2Hex_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.bytes2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.bytes2String_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.string2Bytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.string2Bytes_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.decodeBytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.decodeBytes_undetermined
/-- info: 'KCore.ParamE6Lib.Bytes6.encodeBytes_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Bytes6.encodeBytes_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.list2Set_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.list2Set_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.choiceSet_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.choiceSet_undetermined
/-- info: 'KCore.ParamE6Lib.Set6.set2List_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Set6.set2List_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.notInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.notInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.xorInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.xorInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.andInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.andInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.orInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.orInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.randInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.randInt_undetermined
/-- info: 'KCore.ParamE6Lib.Int6.srandInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Lib.Int6.srandInt_undetermined
