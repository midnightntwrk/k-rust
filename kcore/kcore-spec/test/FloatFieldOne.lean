/-
  What KCore states of K's Float formats with a field of 1 (`pNx1`, `p1xM`). Run from the package
  root: `lake env lean test/FloatFieldOne.lean`.

  K's `domains.md` (FLOAT-SYNTAX) names a format `pNxM` for all positive integers N and M: "exactly N
  bits of precision and M bits of exponent". KCore computes on the formats of Lean core's
  `Float.Model.Format`, whose precision and exponent width are at least 2 (`KFloat.spec?`), and at
  every format with a field of 1 (`thinAt`) by the same formulas over the rounding to the nearest
  datum of that format (`thinHooks`, FloatThin.lean); a format with a field of 1 has values
  (`KFloat.thinOK`), whose data are the encoding rule read at precision 1 (±0, ±2^x, ±∞, NaN) and at
  one exponent bit (±0, the subnormal data ±f·2^(2-p), ±∞, NaN). There:
  - the four operations that take a format as two Ints (`roundFloat`, `Int2Float`, `maxValueFloat`,
    `minValueFloat`) have their values (`roundFloat(1.0, 1, 8)` and `Int2Float(1, 1, 8)` are
    `1.0p1x8`, `maxValueFloat(1, 8)` is 2^127, `minValueFloat(1, 11)` is 2^-1022;
    `roundFloat(1.0, 53, 1)` is `1.0p53x1`, `maxValueFloat(53, 1)` is 2 - 2^-51), and Γ states each
    under every interpretation (`roundFloat_p1_val`, `int2Float_p1_val`, `maxValue_p1_val`,
    `roundFloat_x1_val`, `int2Float_x1_val`, `maxValue_x1_val`, `FltAdd.determined_thin`), so
    `precisionFloat(roundFloat(1.0, 1, 8)) = 1`, which the text states ("The resulting `Float` will
    yield the specified values when calling `precisionFloat`"), is `hook`'s;
  - the operations on such a value compute (`--Float 1.0p1x8` is `-1.0p1x8`, `1.0p1x8 +Float
    1.0p1x8` is `2.0p1x8`, `1.0p2x1 *Float 1.0p2x1` is `1.0p2x1`), and an exact result halfway between
    two data of precision 1, or above the largest finite datum, has no value and is silent
    (`1.0p1x8 +Float 2.0p1x8`, 3 between 2 and 4: `precision_one`; `1.0p2x1 +Float 1.0p2x1`, 2:
    `exponent_one`).
  At `p1x1`, whose finite data are the two zeros, `maxValueFloat(1, 1)` and `minValueFloat(1, 1)` (no
  largest finite value of a sign, no positive one) give no value, nor `roundFloat` and `Int2Float` at
  a value it does not hold; those points are silent (`silentTable`), so Γ states each such
  application equal to the interpretation's value of sort Float: ⊥ under the interpretation that
  gives nothing (`HookParams.none`, `maxValue_11_bot`), and over all interpretations neither ⊥ nor a
  particular value (`FltAdd.undetermined_four`, at the semantics of
  `f2-examples/fltadd.kompile.kore`).
  A literal of a format with a field of 1 (`1.0p1x8`, `NaNp53x1`) is not read (`Parse.floatLit?` gives
  none, the reader's `literal` refusal), but its data are values (`dvOK`): the encodings in the
  format's `p + e` bits that are no NaN pattern, and the NaN code `2 ^ (p + e)`; their text is
  `1.0p1x8`, `NaNp1x8`, … (`KFloat.text`). `precisionFloat` and `exponentBitsFloat` read such a
  value's format (`precision_one`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore ML Faithful

def f64 (b : Nat) : GroundTerm := .dv Srt.float (.float 53 11 b)

/-- `1.0p1x8`, the value 1.0 of the format `p1x8`. -/
def t18 : GroundTerm := .dv Srt.float (.float 1 8 127)

/-- `2.0p1x8`: the exponent field 128 (bias 127), no significand field. -/
def two18 : GroundTerm := .dv Srt.float (.float 1 8 128)

/-- `1.0p53x1`: one exponent bit, so bias 0 and every finite datum subnormal, f·2^-51; 1.0 is the
significand field 2^51. -/
def one531 : GroundTerm := .dv Srt.float (.float 53 1 (2 ^ 51))

/-- `1.0p2x1`, the one positive finite datum of `p2x1` (the significand field 1, f·2^0). -/
def t21 : GroundTerm := .dv Srt.float (.float 2 1 1)

/-- **At a field of 1 the four operations have their values**: `1.0` of `p1x8` (the exponent field
127); the largest finite datum of `p1x8`, 2^127 (the exponent field 254, below the field of the
infinities); the smallest positive datum of `p1x11`, 2^-1022 (the exponent field 1: with no
significand field there is no subnormal datum). At one exponent bit: `1.0` of `p53x1` and of
`p24x1` (the significand fields 2^51 and 2^22); the largest finite datum of `p53x1`,
(2^52 - 1)·2^-51 (the significand field of all ones); the smallest positive datum of `p2x1`, 1. At a
field of 0 or below, which names no format, and at `p1x1`, whose finite data are the two zeros
(no largest of a sign, no positive one; 1.0 is none of them), they give no value, and those points
are silent. -/
example : hook floatRound [f64 0x3FF0000000000000, int 1, int 8] = some (some t18) ∧
    hook floatRound [f64 0x3FF0000000000000, int 53, int 1] = some (some one531) ∧
    hook int2Float [int 1, int 1, int 8] = some (some t18) ∧
    hook int2Float [int 1, int 24, int 1] = some (some (.dv Srt.float (.float 24 1 (2 ^ 22)))) ∧
    hook floatMaxValue [int 1, int 8] = some (some (.dv Srt.float (.float 1 8 254))) ∧
    hook floatMaxValue [int 53, int 1] = some (some (.dv Srt.float (.float 53 1 (2 ^ 52 - 1)))) ∧
    hook floatMinValue [int 1, int 11] = some (some (.dv Srt.float (.float 1 11 1))) ∧
    hook floatMinValue [int 2, int 1] = some (some t21) ∧
    hook floatMaxValue [int 0, int 8] = some none ∧
    hook floatRound [f64 0x3FF0000000000000, int 2, int 2] = some (some (.dv Srt.float (.float 2 2 2))) ∧
    hook floatRound [f64 0x3FF0000000000000, int 1, int 1] = some none ∧
    hook int2Float [int 1, int 1, int 1] = some none ∧
    hook floatMaxValue [int 1, int 1] = some none ∧ hook floatMinValue [int 1, int 1] = some none ∧
    silent floatRound [f64 0x3FF0000000000000, int 1, int 1] = true ∧
    silent int2Float [int 1, int 1, int 1] = true ∧
    silent floatMaxValue [int 1, int 1] = true ∧ silent floatMinValue [int 1, int 1] = true := by
  decide +kernel

/-- No literal of such a format is read; its data are values: at `p1x8` every encoding of the 9 bits
(no pattern of them is a NaN) and the NaN code 512; at `p8x1` the encodings of the 9 bits but the
NaN patterns (exponent bit set, significand nonzero), and the NaN code 512; nothing at a field of
0. The text of each reads as its datum. -/
example : Parse.floatLit? "1.0p1x8" = none ∧ Parse.floatLit? "NaNp53x1" = none ∧
    Parse.floatLit? "1.0p2x2" = some (.float 2 2 2) ∧
    (∀ b < 2 ^ 9, dvOK {} Srt.float (.float 1 8 b) = true) ∧ dvOK {} Srt.float (.float 1 8 512) = true ∧
    dvOK {} Srt.float (.float 1 8 513) = false ∧
    dvOK {} Srt.float (.float 8 1 (2 ^ 7 + 1)) = false ∧ dvOK {} Srt.float (.float 8 1 (2 ^ 7)) = true ∧
    dvOK {} Srt.float (.float 8 1 512) = true ∧ dvOK {} Srt.float (.float 0 8 0) = false ∧
    KFloat.text 1 8 127 = "1.0p1x8" ∧ KFloat.text 1 8 512 = "NaNp1x8" ∧
    KFloat.text 1 8 (2 ^ 8 + 127) = "-1.0p1x8" ∧ KFloat.text 1 8 255 = "Infinityp1x8" ∧
    KFloat.text 8 1 (2 ^ 7) = "Infinityp8x1" ∧ KFloat.text 8 1 512 = "NaNp8x1" := by
  decide +kernel

/-- **A value of format `p1x8` has precision 1 and exponent width 8**, is compared by its datum
(`1.0p1x8 <Float 0.0` is false), and the operations compute on it: `--Float 1.0p1x8` is `-1.0p1x8`
(the sign bit 8), `1.0p1x8 +Float 1.0p1x8` is `2.0p1x8`; `1.0p1x8 +Float 2.0p1x8`, exactly 3,
halfway between the data 2 and 4, has no value and is silent. -/
theorem precision_one : hook floatPrecision [t18] = some (some (int 1)) ∧
    hook floatExponentBits [t18] = some (some (int 8)) ∧
    hook floatNeg [t18] = some (some (.dv Srt.float (.float 1 8 (256 + 127)))) ∧
    hook floatLt [t18, f64 0] = some (some (bool false)) ∧
    hook floatAdd [t18, t18] = some (some two18) ∧
    hook floatAdd [t18, two18] = some none ∧ silent floatAdd [t18, two18] = true := by
  decide +kernel

/-- **A value of format `p2x1` has precision 2 and exponent width 1**, is compared by its datum
(`1.0p2x1 <Float 0.0` is false), and the operations compute on it: `--Float 1.0p2x1` is `-1.0p2x1`
(the sign bit 2), `1.0p2x1 *Float 1.0p2x1` is `1.0p2x1`; `1.0p2x1 +Float 1.0p2x1`, exactly 2, above
the largest finite datum 1, has no value and is silent. -/
theorem exponent_one : hook floatPrecision [t21] = some (some (int 2)) ∧
    hook floatExponentBits [t21] = some (some (int 1)) ∧
    hook floatNeg [t21] = some (some (.dv Srt.float (.float 2 1 5))) ∧
    hook floatLt [t21, f64 0] = some (some (bool false)) ∧
    hook floatMul [t21, t21] = some (some t21) ∧
    hook floatAdd [t21, t21] = some none ∧ silent floatAdd [t21, t21] = true := by
  decide +kernel

/-- A Float value and two Ints have the sorts `[Float, Int, Int]` in every semantics. -/
theorem sortsOf_fii (c : Semantics) {b : Nat} (hb : KFloat.ok 53 11 b = true) (p e : Int) :
    c.sortsOf [f64 b, int p, int e] = some [Srt.float, Srt.int, Srt.int] := by
  simp [Semantics.sortsOf, Semantics.sortOf, f64, int, dvOK, hb]

theorem sortsOf_ii (c : Semantics) (p e : Int) : c.sortsOf [int p, int e] = some [Srt.int, Srt.int] := by
  simp [Semantics.sortsOf, Semantics.sortOf, int, dvOK]

theorem sortsOf_iii (c : Semantics) (n p e : Int) :
    c.sortsOf [int n, int p, int e] = some [Srt.int, Srt.int, Srt.int] := by
  simp [Semantics.sortsOf, Semantics.sortOf, int, dvOK]

/-! ## Under the interpretation that gives nothing, ⊥ (through `ΓFallback`) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

theorem gamma_fallback (c : Semantics) (H : HookParams) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : (c.withHooks H).sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    Γ (c.withHooks H) (appP (c.withHooks H) k vs ≡ (match (c.withHooks H).fallback k.name vs with
      | some v => den (c.withHooks H) v
      | none => ⊥)) :=
  Or.inr (Or.inl ⟨k, vs, (lookupSig_spec hks).1, hvs, hh, hs, rfl⟩)

theorem fallback_none (c : Semantics) (k : CtorSig) (vs : List GroundTerm) :
    (c.withHooks HookParams.none).fallback k.name vs = none := by
  unfold Semantics.fallback; split <;> rfl

/-- At a silent point, Γ under `HookParams.none` states ⊥. -/
theorem gamma_none (c : Semantics) {k : CtorSig} (hks : lookupSig hookSigs k.name = some k)
    {vs : List GroundTerm} (hvs : (c.withHooks HookParams.none).sortsOf vs = some k.args)
    (hh : hook k.name vs = some none) (hs : silent k.name vs = true) :
    Γ (c.withHooks HookParams.none) (appP (c.withHooks HookParams.none) k vs ≡ ⊥) := by
  have h := gamma_fallback c HookParams.none hks hvs hh hs
  rw [fallback_none] at h
  exact h

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-- **The theory of every semantics states `roundFloat(1.0, 1, 8) = 1.0p1x8`**, under every
interpretation. -/
theorem roundFloat_p1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩
        [f64 0x3FF0000000000000, int 1, int 8] ≡ den (c.withHooks H) t18) :=
  gamma_val _ (by decide +kernel) (sortsOf_fii _ (by decide) 1 8) (by decide +kernel)

/-- `Int2Float(1, 1, 8) = 1.0p1x8`. -/
theorem int2Float_p1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨int2Float, [Srt.int, Srt.int, Srt.int], Srt.float⟩ [int 1, int 1, int 8] ≡
        den (c.withHooks H) t18) :=
  gamma_val _ (by decide +kernel) (sortsOf_iii _ 1 1 8) (by decide +kernel)

/-- `maxValueFloat(1, 8)` is 2^127, the literal of the exponent field 254. -/
theorem maxValue_p1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩ [int 1, int 8] ≡
        den (c.withHooks H) (.dv Srt.float (.float 1 8 254))) :=
  gamma_val _ (by decide +kernel) (sortsOf_ii _ 1 8) (by decide +kernel)

/-- **The theory of every semantics states `roundFloat(1.0, 53, 1) = 1.0p53x1`**, under every
interpretation: a format of one exponent bit. -/
theorem roundFloat_x1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩
        [f64 0x3FF0000000000000, int 53, int 1] ≡ den (c.withHooks H) one531) :=
  gamma_val _ (by decide +kernel) (sortsOf_fii _ (by decide) 53 1) (by decide +kernel)

/-- `Int2Float(1, 24, 1) = 1.0p24x1`. -/
theorem int2Float_x1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨int2Float, [Srt.int, Srt.int, Srt.int], Srt.float⟩ [int 1, int 24, int 1] ≡
        den (c.withHooks H) (.dv Srt.float (.float 24 1 (2 ^ 22)))) :=
  gamma_val _ (by decide +kernel) (sortsOf_iii _ 1 24 1) (by decide +kernel)

/-- `maxValueFloat(53, 1)` is (2^52 - 1)·2^-51 and `minValueFloat(53, 1)` is 2^-51. -/
theorem maxValue_x1_val (c : Semantics) (H : HookParams) :
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩ [int 53, int 1] ≡
        den (c.withHooks H) (.dv Srt.float (.float 53 1 (2 ^ 52 - 1)))) ∧
    Γ (c.withHooks H)
      (appP (c.withHooks H) ⟨floatMinValue, [Srt.int, Srt.int], Srt.float⟩ [int 53, int 1] ≡
        den (c.withHooks H) (.dv Srt.float (.float 53 1 1))) :=
  ⟨gamma_val _ (by decide +kernel) (sortsOf_ii _ 53 1) (by decide +kernel),
   gamma_val _ (by decide +kernel) (sortsOf_ii _ 53 1) (by decide +kernel)⟩

/-- **Under `HookParams.none`, the theory of every semantics states `maxValueFloat(1, 1) = ⊥` and
`minValueFloat(1, 1) = ⊥`**: the format whose finite data are the two zeros. -/
theorem maxValue_11_bot (c : Semantics) :
    Γ (c.withHooks HookParams.none)
      (appP (c.withHooks HookParams.none) ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩ [int 1, int 1] ≡ ⊥) ∧
    Γ (c.withHooks HookParams.none)
      (appP (c.withHooks HookParams.none) ⟨floatMinValue, [Srt.int, Srt.int], Srt.float⟩ [int 1, int 1] ≡ ⊥) :=
  ⟨gamma_none c (by decide +kernel) (sortsOf_ii _ 1 1) (by decide +kernel) (by decide +kernel),
   gamma_none c (by decide +kernel) (sortsOf_ii _ 1 1) (by decide +kernel) (by decide +kernel)⟩

/-! ## Over all interpretations, neither ⊥ nor a value -/

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

theorem fallback_const (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) (vs : List GroundTerm) {v : GroundTerm}
    (hv : c.sortOf v = some k.result) : (c.withHooks (constH v)).fallback k.name vs = some v := by
  unfold Semantics.fallback; rw [hks, Semantics.sortOf_withHooks c _ hr]
  simp [Semantics.withHooks, constH, Option.filter, hv]

/-- `undetermined` of test/SilentPoints.lean: over all interpretations Γ entails neither that the
application at a silent point has no value nor that it is `v`. -/
theorem undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true)
    {v : GroundTerm} (hv : c.sortOf v = some k.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ den (c.withHooks H) v)) := by
  constructor
  · intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks (constH v)) ((Semantics.coreOK_withHooks c _).trans hok) hfnv).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks (constH v)) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c (constH v) hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_const c hr hks vs hv] at hfb
    have hbot := hall (constH v) hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks (constH v))
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hbot KoreAML.val0 default) a
    exact absurd ((h2.mp (h1.mpr ((ha a).mpr rfl)))) (by simp [Pattern.interpret])
  · intro hall
    obtain ⟨M, _, I, hI⟩ := (sound_hyp (c.withHooks HookParams.none) ((Semantics.coreOK_withHooks c _).trans hok) hfn₀).1
    have hIΓ : I ⊧ᴵP Γ (c.withHooks HookParams.none) := fun φ h => hI φ (Or.inl (Or.inl h))
    have hD := defOK hIΓ
    have hfb := hIΓ _ (gamma_fallback c HookParams.none hks (by rw [Semantics.sortsOf_withHooks c _ hr]; exact hvs) hh hs)
    rw [fallback_none c k vs] at hfb
    have hval := hall HookParams.none hIΓ
    obtain ⟨a, ha, -⟩ := den_single hIΓ (c := c.withHooks HookParams.none)
      (by rw [Semantics.sortOf_withHooks c _ hr]; exact hv) KoreAML.val0
    have h1 := (KoreAML.interp_equal hD).mp (hfb KoreAML.val0 default) a
    have h2 := (KoreAML.interp_equal hD).mp (hval KoreAML.val0 default) a
    exact absurd (h1.mp (h2.mpr ((ha a).mpr rfl))) (by simp [Pattern.interpret])

namespace FltAdd

definition_of defn from "f2-examples/fltadd.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

tables_of T from "f2-examples/fltadd.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

set_option maxHeartbeats 1000000 in
open Faithful.Model in
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := fns_nil
  have hrc : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c.withHooks H) (show ∀ k ∈ c.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- `0.0` of binary64, a value of sort Float. -/
theorem zero_sorted : c.sortOf (f64 0) = some Srt.float := by decide +kernel

/-- `1.0p1x8`, a value of sort Float. -/
theorem t18_sorted : c.sortOf t18 = some Srt.float := by decide +kernel

/-- **`roundFloat(1.0, 1, 8)` is determined, a value of its own format**: under every
interpretation Γ states it is `1.0p1x8`. -/
theorem determined_thin (H : HookParams) :
    Γ (c.withHooks H) (appP (c.withHooks H) ⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩
        [f64 0x3FF0000000000000, int 1, int 8] ≡ den (c.withHooks H) t18) :=
  roundFloat_p1_val c H

/-- **`roundFloat(1.0, 1, 1)`, `Int2Float(1, 1, 1)`, `maxValueFloat(1, 1)`, `minValueFloat(1, 1)`
are undetermined**: over all interpretations Γ entails neither ⊥ nor `0.0` at each. -/
theorem undetermined_four :
    (¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩
        [f64 0x3FF0000000000000, int 1, int 1] ≡ ⊥)) ∧
      ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatRound, [Srt.float, Srt.int, Srt.int], Srt.float⟩
        [f64 0x3FF0000000000000, int 1, int 1] ≡ den (c.withHooks H) (f64 0)))) ∧
    (¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨int2Float, [Srt.int, Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1, int 1] ≡ ⊥)) ∧
      ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨int2Float, [Srt.int, Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1, int 1] ≡ den (c.withHooks H) (f64 0)))) ∧
    (¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1] ≡ ⊥)) ∧
      ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatMaxValue, [Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1] ≡ den (c.withHooks H) (f64 0)))) ∧
    (¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatMinValue, [Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1] ≡ ⊥)) ∧
      ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) ⟨floatMinValue, [Srt.int, Srt.int], Srt.float⟩
        [int 1, int 1] ≡ den (c.withHooks H) (f64 0)))) :=
  ⟨undetermined c coreOK (by decide +kernel) (by decide +kernel) (sortsOf_fii c (by decide) 1 1) (by decide +kernel)
      (by decide +kernel) zero_sorted (fnHyp _) (fnHyp _),
   undetermined c coreOK (by decide +kernel) (by decide +kernel) (sortsOf_iii c 1 1 1) (by decide +kernel)
      (by decide +kernel) zero_sorted (fnHyp _) (fnHyp _),
   undetermined c coreOK (by decide +kernel) (by decide +kernel) (sortsOf_ii c 1 1) (by decide +kernel)
      (by decide +kernel) zero_sorted (fnHyp _) (fnHyp _),
   undetermined c coreOK (by decide +kernel) (by decide +kernel) (sortsOf_ii c 1 1) (by decide +kernel)
      (by decide +kernel) zero_sorted (fnHyp _) (fnHyp _)⟩

end FltAdd

#print axioms roundFloat_p1_val
#print axioms int2Float_p1_val
#print axioms maxValue_p1_val
#print axioms roundFloat_x1_val
#print axioms int2Float_x1_val
#print axioms maxValue_x1_val
#print axioms maxValue_11_bot
#print axioms exponent_one
#print axioms FltAdd.undetermined_four
#print axioms precision_one
#print axioms FltAdd.determined_thin
