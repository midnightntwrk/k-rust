/-
  The parameter hooks of K-IO, FFI, K-REFLECTION, TIMER, UNIFICATION and JSON on the construct
  fixtures e6-param-io, e6-param-ffi, e6-param-kreflection, e6-param-timer, e6-param-unification and
  e6-param-json (`f2-examples/e6-param-*.kompile.kore`, each the text its fixture's kompile.txt
  hashes, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory relative
  to the tree). Each text applies every hooked function of its module that no registry hook
  interprets once, in a rule's right side (`go(N, …)`); the reader reads each as a parameter symbol
  no hook implements (`impl = none`, `raw = false`; the fixture's params.txt): its value at an
  argument list is the interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the
  interpretation gives none. The hooked functions of FFI, TIMER and UNIFICATION are sentences of K
  builtin files no library text states, read as the definition's own (`Parse.isOwnBuiltin`).

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undeterminedPS`). The pair of models: under `HookParams.none` the
  application is ⊥ in every model of Γ, under `constHPS v` it is `v` in every model, and both
  theories have models (`sound_hyp`). An instance reads its facts of the text as one decided test
  (`okPS`: the parameter named, looked up by its number, no hook implementing it, the point's
  arguments values of its argument sorts and the given value one of its result sort).

  `FnHyp` under every H: JSON's text has no function (`fnHyp_of_fnsNilPS`). The other five have
  K's `append` (a parameter giving a K is appended to the rest of the cell), declared total, which
  the totality decider confirms (its clauses cover K × K, the cover check splitting K over `kseq`
  and `dotk`); FFI's text also has the function `#ffiCall` of six arguments. The deciders name no
  fact (`fnHyp_decidedPS`).

  The points are values of the argument sorts (`1`, `"a"`, `b"a"`, `1` as a KItem, the empty K,
  `ListItem(1)`, `#ffi_sint`) and the given values one of the result sort (an IOInt, an IOString,
  `#tempFile("a", 1)`, `SetItem(1)`, `null`, ...). Whatever value the K prose would name there,
  none is entailed: the text states no sentence of these symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamE6Sys.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE6Sys

open KCore ML Faithful

/-! ## The schema, at a parameter no hook implements -/

/-- The symbol `f` applied to the values `vs`, as Γ writes it. -/
abbrev appPS (c : Semantics) (f : Sym) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c f (GroundTerm.koreList c vs))

/-- Γ holds the graph of every parameter symbol at values of its argument sorts. -/
theorem gamma_paramPS (c : Semantics) {k : ParamSig} (hk : k ∈ c.params) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.sig.args) :
    Γ c (appPS c k.sig.name vs ≡ (match c.paramVal k.sig.name vs with
      | some v => den c v
      | none => ⊥)) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨k, vs, hk, hvs, rfl⟩))))))

/-- The interpretation that gives `v` everywhere. -/
def constHPS (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- At a parameter no hook implements and no open generator, the value under H is H's answer,
kept where it has the result sort. -/
theorem paramVal_implNonePS (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (H : HookParams)
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
`HookParams.none` it is ⊥ in every model, under `constHPS v` it is `v` in every model, and both
theories have models (`sound_hyp`). -/
theorem param_undeterminedPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : ParamSig} (hlk : c.lookupParam k.sig.name = some k) (hi : k.impl = none)
    {vs : List GroundTerm} (hvs : c.sortsOf vs = some k.sig.args)
    {v : GroundTerm} (hv : c.sortOf v = some k.sig.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constHPS v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPS (c.withHooks H) k.sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) k.sig.name vs ≡ den (c.withHooks H) v)) := by
  have hk : k ∈ c.params := by
    have h := hlk
    rw [Semantics.lookupParam_eq] at h; exact List.mem_of_find?_eq_some h
  have hvsH : ∀ H : HookParams, (c.withHooks H).sortsOf vs = some k.sig.args := fun H => by
    rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs
  have hpv : (c.withHooks (constHPS v)).paramVal k.sig.name vs = some v := by
    rw [paramVal_implNonePS c hr _ hlk hi]
    simp [constHPS, Option.filter, hv]
  have hp0 : (c.withHooks HookParams.none).paramVal k.sig.name vs = none := by
    rw [paramVal_implNonePS c hr _ hlk hi]; rfl
  constructor
  · -- under `constHPS v` the application is `v`'s element, so not ⊥
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constHPS v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constHPS v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPS (c.withHooks (constHPS v)) (k := k) hk (hvsH _))
    rw [hpv] at hg
    have hbot := hall (constHPS v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constHPS v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hg := hIΓ _ (gamma_paramPS (c.withHooks HookParams.none) (k := k) hk (hvsH _))
    rw [hp0] at hg
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hg KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

/-! ## An instance, decided on the text -/

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
def paramPS (c : Semantics) (n : String) : ParamSig :=
  (c.params.find? fun k => c.symName k.sig.name == n).getD default

/-- What an instance asks of the text, as one decided test: the parameter named `n` is the one
`lookupParam` finds by its number, no hook implements it, `vs` are values of its argument sorts and
`v` a value of its result sort. -/
def okPS (c : Semantics) (n : String) (vs : List GroundTerm) (v : GroundTerm) : Bool :=
  c.symName (paramPS c n).sig.name == n && c.lookupParam (paramPS c n).sig.name == some (paramPS c n) &&
    (paramPS c n).impl == none && c.sortsOf vs == some (paramPS c n).sig.args &&
    c.sortOf v == some (paramPS c n).sig.result

/-- `param_undeterminedPS` at the parameter named `n`, from the decided test `okPS`. -/
theorem undetermined_of_okPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    (hfn : ∀ H : HookParams, FnHyp (c.withHooks H)) {n : String} {vs : List GroundTerm} {v : GroundTerm}
    (h : okPS c n vs v = true) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appPS (c.withHooks H) (paramPS c n).sig.name vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c n).sig.name vs ≡ den (c.withHooks H) v)) := by
  simp only [okPS, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hl⟩, hi⟩, hvs⟩, hv⟩ := h
  exact param_undeterminedPS c hok hr hl hi hvs hv (hfn _) (hfn _)

/-- With no function and no condition reading an open generator, `FnHyp` holds under every
interpretation. -/
theorem fnHyp_of_fnsNilPS (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) (hfns : c.fns = [])
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
def symPS (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0
/-- `#tempFile("a", 1)`. -/
def ioFileV (c : Semantics) : GroundTerm := .ctor (symPS c "Lbl'Hash'tempFile") [strV, int 1]
/-- `#ffi_sint`. -/
def ffiTypeV (c : Semantics) : GroundTerm := .ctor (symPS c "Lbl'Hash'ffi'Unds'sint") []
/-- JSON's `null`. -/
def jsonV (c : Semantics) : GroundTerm := .ctor (symPS c "LblJSONnull") []


/-! ## `FnHyp` by the deciders -/

/-- With no fact named by the deciders at the call order `ord` (termination, totality, agreement,
match independence), `FnHyp` holds under every interpretation. -/
theorem fnHyp_decidedPS (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
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

/-! ## e6-param-io: K-IO -/

namespace IO6

definition_of defn from "f2-examples/e6-param-io.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 385) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem accept_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'accept'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem close_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'close'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem getc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getc'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem lock_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'lock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'log` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem log_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'log").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'log").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'logToFile` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is the empty K. -/
theorem logToFile_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'logToFile").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'logToFile").sig.name [strV, strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is #tempFile("a", 1). -/
theorem mkstemp_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'mkstemp'LParUndsRParUnds'K-IO'Unds'IOFile'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (ioFileV c))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a", "a") nor that it is 1 (an IOInt). -/
theorem open_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String").sig.name [strV, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'open'LParUndsCommUndsRParUnds'K-IO'Unds'IOInt'Unds'String'Unds'String").sig.name [strV, strV] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem putc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'putc'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is "a" (an IOString). -/
theorem read_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'read'LParUndsCommUndsRParUnds'K-IO'Unds'IOString'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (ioStrV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem remove_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'remove'LParUndsRParUnds'K-IO'Unds'K'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem seek_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seek'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem seekEnd_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'seekEnd'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is the empty K. -/
theorem shutdownWrite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'shutdownWrite'LParUndsRParUnds'K-IO'Unds'K'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1 (a KItem). -/
theorem system_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'system'LParUndsRParUnds'K-IO'Unds'KItem'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1) nor that it is 1 (an IOInt). -/
theorem tell_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'tell'LParUndsRParUnds'K-IO'Unds'IOInt'Unds'Int").sig.name [int 1] ≡ den (c.withHooks H) (ioIntV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is 1. -/
theorem time_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'time'LParRParUnds'K-IO'Unds'Int").sig.name [] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'trace` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem)) nor that it is the empty K. -/
theorem trace_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'trace").sig.name [kint 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'trace").sig.name [kint 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'traceK` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is the empty K. -/
theorem traceK_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'traceK").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'traceK").sig.name [kDot] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, 1) nor that it is the empty K. -/
theorem unlock_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unlock'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'Int").sig.name [int 1, int 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, "a") nor that it is the empty K. -/
theorem write_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String").sig.name [int 1, strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'write'LParUndsCommUndsRParUnds'K-IO'Unds'K'Unds'Int'Unds'String").sig.name [int 1, strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end IO6

/-! ## e6-param-ffi: FFI -/

namespace FFI6

definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 412) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (b"a") nor that it is 1. -/
theorem bytesAddress_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes").sig.name [bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'address'LParUndsRParUnds'FFI'Unds'Int'Unds'Bytes").sig.name [bytesV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem), 1, 1) nor that it is b"a". -/
theorem alloc_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int").sig.name [kint 1, int 1, int 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'alloc'LParUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'KItem'Unds'Int'Unds'Int").sig.name [kint 1, int 1, int 1] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, ListItem(1), ListItem(1), ListItem(1), #ffi_sint) nor that it is b"a". -/
theorem ffiCallVariadic_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, listV, ffiTypeV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, listV, ffiTypeV c] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, ListItem(1), ListItem(1), #ffi_sint) nor that it is b"a". -/
theorem ffiCall_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, ffiTypeV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'ffiCall'LParUndsCommUndsCommUndsCommUndsRParUnds'FFI'Unds'Bytes'Unds'Int'Unds'List'Unds'List'Unds'FFIType").sig.name [int 1, listV, listV, ffiTypeV c] ≡ den (c.withHooks H) (bytesV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1 (a KItem)) nor that it is the empty K. -/
theorem free_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem").sig.name [kint 1] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'free'LParUndsRParUnds'FFI'Unds'K'Unds'KItem").sig.name [kint 1] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1. -/
theorem functionAddress_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'functionAddress'LParUndsRParUnds'FFI'Unds'Int'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, b"a") nor that it is the empty K. -/
theorem nativeRead_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeRead'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes` is not determined by the text**: over all H, Γ entails neither that it has
no value at (1, b"a") nor that it is the empty K. -/
theorem nativeWrite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'nativeWrite'LParUndsCommUndsRParUnds'FFI'Unds'K'Unds'Int'Unds'Bytes").sig.name [int 1, bytesV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end FFI6

/-! ## e6-param-kreflection: K-REFLECTION -/

namespace KReflection6

definition_of defn from "f2-examples/e6-param-kreflection.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 386) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is ListItem(1). -/
theorem argv_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List").sig.name [] ≡ den (c.withHooks H) (listV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem configuration_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is 1 (a KItem). -/
theorem fresh_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is the empty K. -/
theorem getenv_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String").sig.name [strV] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is "a". -/
theorem kompiledDirectory_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String").sig.name [] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is "a". -/
theorem sort_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is 1 (a KItem). -/
theorem getsymbol_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end KReflection6

/-! ## e6-param-timer: TIMER -/

namespace Timer6

definition_of defn from "f2-examples/e6-param-timer.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 385) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`LbltimerStart'LParRParUnds'TIMER'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem timerStart_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStart'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStart'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LbltimerStop'LParRParUnds'TIMER'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value (no argument) nor that it is the empty K. -/
theorem timerStop_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStop'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LbltimerStop'LParRParUnds'TIMER'Unds'K").sig.name [] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end Timer6

/-! ## e6-param-unification: UNIFICATION -/

namespace Unification6

definition_of defn from "f2-examples/e6-param-unification.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- K's `append` (number 386) is total by the decider, and the deciders name no fact: `FnHyp`
under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decidedPS c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is SetItem(1). -/
theorem metaKVariables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'metaKVariables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is the empty K. -/
theorem renameVariables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'renameVariables'LParUndsRParUnds'UNIFICATION'Unds'K'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kDot))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K, the empty K) nor that it is true. -/
theorem unifiable_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K").sig.name [kDot, kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'unifiable'LParUndsCommUndsRParUnds'UNIFICATION'Unds'Bool'Unds'K'Unds'K").sig.name [kDot, kDot] ≡ den (c.withHooks H) (bool true))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is SetItem(1). -/
theorem variables_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variables'LParUndsRParUnds'UNIFICATION'Unds'Set'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (setV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K` is not determined by the text**: over all H, Γ entails neither that it has
no value at (the empty K) nor that it is 1 (a KItem). -/
theorem variablesMap_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K").sig.name [kDot] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "Lbl'Hash'variablesMap'LParUndsRParUnds'UNIFICATION'Unds'KItem'Unds'K").sig.name [kDot] ≡ den (c.withHooks H) (kint 1))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end Unification6

/-! ## e6-param-json: JSON -/

namespace JSON6

definition_of defn from "f2-examples/e6-param-json.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fnsNilPS c noRaw (by decide +kernel) (by decide +kernel) H

/-- **`LblJSON2String` is not determined by the text**: over all H, Γ entails neither that it has
no value at (null) nor that it is "a". -/
theorem jSON2String_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblJSON2String").sig.name [jsonV c] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblJSON2String").sig.name [jsonV c] ≡ den (c.withHooks H) (strV))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

/-- **`LblString2JSON` is not determined by the text**: over all H, Γ entails neither that it has
no value at ("a") nor that it is null. -/
theorem string2JSON_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblString2JSON").sig.name [strV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appPS (c.withHooks H) (paramPS c "LblString2JSON").sig.name [strV] ≡ den (c.withHooks H) (jsonV c))) :=
  undetermined_of_okPS c coreOK noRaw fnHyp (by decide +kernel)

end JSON6

end KCore.ParamE6Sys

/-- info: 'KCore.ParamE6Sys.IO6.accept_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.accept_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.close_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.close_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.getc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.getc_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.lock_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.lock_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.log_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.log_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.logToFile_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.logToFile_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.mkstemp_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.mkstemp_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.open_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.open_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.putc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.putc_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.read_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.read_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.remove_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.remove_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.seek_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.seek_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.seekEnd_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.seekEnd_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.shutdownWrite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.shutdownWrite_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.system_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.system_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.tell_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.tell_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.time_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.time_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.trace_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.trace_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.traceK_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.traceK_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.unlock_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.unlock_undetermined
/-- info: 'KCore.ParamE6Sys.IO6.write_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.IO6.write_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.bytesAddress_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.bytesAddress_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.alloc_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.alloc_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.ffiCallVariadic_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.ffiCallVariadic_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.ffiCall_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.ffiCall_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.free_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.free_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.functionAddress_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.functionAddress_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.nativeRead_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.nativeRead_undetermined
/-- info: 'KCore.ParamE6Sys.FFI6.nativeWrite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.FFI6.nativeWrite_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.argv_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.argv_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.configuration_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.configuration_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.fresh_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.fresh_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.getenv_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.getenv_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.kompiledDirectory_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.kompiledDirectory_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.sort_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.sort_undetermined
/-- info: 'KCore.ParamE6Sys.KReflection6.getsymbol_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.KReflection6.getsymbol_undetermined
/-- info: 'KCore.ParamE6Sys.Timer6.timerStart_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Timer6.timerStart_undetermined
/-- info: 'KCore.ParamE6Sys.Timer6.timerStop_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Timer6.timerStop_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.metaKVariables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.metaKVariables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.renameVariables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.renameVariables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.unifiable_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.unifiable_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.variables_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.variables_undetermined
/-- info: 'KCore.ParamE6Sys.Unification6.variablesMap_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.Unification6.variablesMap_undetermined
/-- info: 'KCore.ParamE6Sys.JSON6.jSON2String_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.JSON6.jSON2String_undetermined
/-- info: 'KCore.ParamE6Sys.JSON6.string2JSON_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KCore.ParamE6Sys.JSON6.string2JSON_undetermined
