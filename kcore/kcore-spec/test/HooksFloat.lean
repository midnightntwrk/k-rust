/-
  The supported hook rows of FLOAT (23) of test/constructs/rows.toml (`hook:FLOAT.*` with status
  `supported`): the sort row `FLOAT.Float` and the twenty-two operations of `rows`. Each has its
  three statements (DONE-0 C2, evidence of a `supported` hook): one in-domain value; for each region
  the builtin prose leaves unstated, that Γ over all interpretations entails neither ⊥ nor a value
  at a point of it; and that the hook's silent predicate in `silentTable` is that region, or why the
  prose covers every argument list. Run from the package root: `lake env lean test/HooksFloat.lean`.

  The expected side is the builtin prose: DOM is K 7.1.337's
  k-distribution/include/kframework/builtin/domains.md, cited by line. No expected value is taken
  from a run or from an implementation: each is derived by hand, and marked by its source:
  - **[P]** the prose's own sentence or example.
  - **[A]** an attribute of the production: `smt-hook((fp.add roundNearestTiesToEven #1 #2))` and
    its like on `*Float`, `/Float`, `%Float`, `+Float`, `-Float` (DOM 1565-1570), the only place the
    text gives a rounding direction for an operation.
  - **[S]** IEEE 754, which the prose names without a clause: the section's title (DOM 1461), "based
    on a generalization of the IEEE 754 standard" (1464-1466), "represented like an IEEE754
    floating-point type" (1482), "in IEEE 754 arithmetic" (1638). What is marked [S] follows from
    the named standard and not from a sentence of the prose. This file was made without a copy of
    the standard: each [S] names the standard's operation or rule as recalled, without a clause, and
    is a reading to confirm against it.
  FLOAT's prose writes no `#False` and no `#Bottom`: no row has a point where it states that there
  is no value. "Unstated" is DOM 14-16.

  Not rows here: `isInfinite`, `sqrtFloat` and `=/=Float` have no `hook` attribute (DOM 1545, 1624,
  1646; an equation each, 1673, 1671, 1648); `^Float`, `rootFloat`, `expFloat`, `logFloat`, the
  trigonometric ones, `maxFloat`, `minFloat`, `exponentFloat`, `signFloat`, `Float2Int` are
  parameter rows.

  The rows, by the region where `hook` gives no value (the `*_none` theorems, at every argument list
  of literals; under `floatShapeOK`, which `coreOK` gives, every value of sort Float is a literal of
  a format `(p, e)`, `float_only`). A format has a model here when `p ≥ 2` and `e ≥ 2`; a *thin*
  format has `p = 1` or `e = 1`, both positive.

  | rows | prose | where `hook` gives no value |
  |---|---|---|
  | `FLOAT.precision`, `FLOAT.exponentBits` | DOM 1508, 1516 "the number of bits of precision / of exponent range in a `Float`"; `total` 1511, 1519 | nowhere at a Float value (`covered_fmt`) |
  | `FLOAT.neg`, `abs`, `floor`, `ceil`, `trunc` | DOM 1552-1554, 1578, 1583-1588; `total` 1562, 1608, 1610-1612 | an operand of a thin format (`unary_none`) |
  | `FLOAT.isNaN` | DOM 1541; `total` 1544 | an operand of a thin format (`isNaN_none`) |
  | `FLOAT.le`, `lt`, `ge`, `gt`, `eq` | DOM 1631-1638; 1641-1645, no `total` | an operand of a thin format (`cmp_none`) |
  | `FLOAT.add`, `sub`, `mul`, `div`, `rem` | DOM 1556-1559; 1565-1570, no `total` | an operand of a thin format; two operands of two formats (`arith_none`) |
  | `FLOAT.round` | DOM 1579-1582; 1609, no `total` | an operand of a thin format; a precision or exponentBits below 2 (`round_none`) |
  | `FLOAT.int2float` | DOM 1653-1654; 1661, no `total` | a precision or exponentBits below 2 (`int2Float_none`) |
  | `FLOAT.maxValue`, `FLOAT.minValue` | DOM 1601-1604; 1625, 1626, no `total` | a precision or exponentBits below 2 (`at_none`) |

  `precisionFloat` and `exponentBitsFloat` are no key of `silentTable`. The other twenty are keys
  whose predicate is true at every argument list (`keys_silent`), so the silent points of each are
  exactly the argument lists of the third column. Against the prose that region has three parts:
  - **two formats** (`+Float`, `-Float`, `*Float`, `/Float`, `%Float`): the prose computes "the sum …
    of two floats" (1556-1559) and nowhere says which format the result has when the two differ:
    unstated. Points: `pts`.
  - **no format** (`roundFloat`, `Int2Float`, `maxValueFloat`, `minValueFloat` at a precision or
    exponentBits ≤ 0): `pNxM` names a format for positive N and M only (1475): unstated. Points:
    `pts`.
  - **a thin format** (every key: an operand of one, or a precision or exponentBits of 1): finding
    1. Here the silent region is NOT shown to be a region the prose leaves unstated. Points: `thin`.

  Statements:
  - **(1)** `vals`: points with the value derived as marked; `hook` gives it (`vals_ok`), it is the
    result under every interpretation and Γ states it (`vals_gamma`), in the semantics of
    `f2-examples/strbytes.kompile.kore` (`coreOK`, no function; a Float literal is a value of Float
    in every semantics, `float_value`). The prose's "The resulting `Float` will yield the specified
    values when calling `precisionFloat` and `exponentBitsFloat`" (1580-1582) at every value of
    `roundFloat` (`round_format`), and the same of `Int2Float`, `maxValueFloat`, `minValueFloat`
    ("with the specified precision and exponent range", 1653-1654, 1601-1604: `int2Float_format`,
    `at_format`).
  - **(2)** `pts`: a point of each row of the two unstated parts; Γ over all interpretations entails
    neither ⊥ nor a value there (`pts_undetermined`). The same at a point of each key in the thin
    part (`thin_undetermined`), which is a fact about Γ and, by finding 1, not a reading of the prose.
  - **(3)** `groups`, `keys_silent`, the `*_none` theorems, `covered_fmt`.

  The sort row `FLOAT.Float` (DOM 1464-1490, 1494-1497): a value is a datum of a format `(p, e)`, the
  precision and the exponent bits of the literal's suffix (1483-1487), `p24x8` for `f` and `p53x11`
  for `d` or no suffix (1484-1490; `lits_read`: the reader takes each literal of `lits` to the
  encoding written there by hand). Every such literal is a value of sort Float in every semantics
  (`float_value`), two encodings are two values (`float_inj`: `0.0` and `-0.0` are two, 1553-1554),
  and nothing else is one (`float_only`); a sort has no argument list. The encoding (the format's
  sign, biased exponent and significand fields) is KCore's representation of the datum; of a NaN the
  syntax (1497) writes neither sign nor payload, and KCore has one per format (`KFloat.ok`).

  Findings (prose against `hook` and `silentTable`), none of which makes a statement here
  unprovable:
  1. Thin formats (`p1xM`, `pNx1`), two readings. DOM 1475 names `pNxM` for "positive integers" N
     and M, and 1481-1483 gives the value of such a literal "in a floating-point type represented
     like an IEEE754 floating-point type, with the number of bits of precision and exponent
     specified by the suffix". (A) the generalization (1465) covers them: then `1.0p1x8` is a datum,
     `isNaN(1.0p1x8)` is false, `--Float 1.0p1x8` is `-1.0p1x8`, `maxValueFloat(1, 8)` is 2^127, and
     so on, and Γ states less than the prose at every point of `thin` (Hooks.lean's comment on
     `silentTable` says the same: "less than the text's IEEE 754 description"). (B) [S] IEEE 754
     defines no format of one significand digit or of one exponent bit (with e = 1 the largest
     exponent is below the smallest; with p = 1 an encoding has no significand field to tell a NaN
     from an infinity), and the prose does not say how it generalizes there: unstated. `silentTable`
     is right under (B) and too wide under (A). KCore's carrier holds values of thin formats
     (`KFloat.thinOK`), `hook` computes none of the twenty operations on them, and the reader takes
     no literal of one (test/FloatLib.lean: `1.0p1x8` is not read). `precisionFloat` and
     `exponentBitsFloat` have their values there (`covered_fmt`).
  2. Rounding. The prose gives a direction only for literals ("rounded to the nearest possible
     value", 1481-1482, without a rule for a tie) and, as attributes, for the five arithmetic
     operations ([A]). `roundFloat` ("Round a floating-point number to a specified precision",
     1579) and `Int2Float` ("convert an integer to a floating-point number", 1653) at a value the
     format does not hold have no direction in the text. `hook` rounds every one to nearest, ties to
     even, and no such point is silent (`beyond`). Reading (A): [S] the named standard's default
     rounding (roundTiesToEven) applies: stated. (B) unstated, and `silentTable` is too
     narrow there. `vals` holds no inexact point of `roundFloat` or `Int2Float`.
  3. Special data. The prose's sentences for `floorFloat`, `ceilFloat`, `truncFloat` ("the next lowest
     floating-point value which is an integer", 1583-1588) describe no value at an infinity or a NaN
     and no sign for a zero result; `/Float` and `%Float` at a zero divisor, and every operation at a
     NaN or an infinity, are not mentioned. Each is [S] only (roundToIntegral; the sign of a
     zero; invalid operation and division by zero; NaN propagation). `hook` gives the [S]
     value and none is silent. The three rounding rows are declared `total`; the arithmetic ones and
     the comparisons are not, though the prose names no input without a value.
  4. Comparisons of two formats. The prose compares "a float … to another float" (1631-1632) and
     says nothing of two formats; `hook` compares the exact values, with a value at every pair of
     model formats, not silent (`beyond`: `1.0 ==Float 1.0f` is true), where the arithmetic of two
     formats is silent. Reading (A): a comparison's result is a Bool, the values of the two data are
     given, and [S] the standard's comparisons take operands of different formats: stated. (B) unstated, as for
     the arithmetic.
  5. `%Float`: "computed based on rounding the quotient of the two floats to the nearest integer"
     (1557-1558) gives no rule for a quotient halfway between two integers; [A] 1567 and [S]
     (remainder) take the even one. `vals` has one point of each kind, marked.
  6. A NaN's sign. [S] negate and abs act on the sign of a NaN; K's syntax writes one NaN
     per format (1497) and KCore's carrier has one, so `--Float NaN` is `NaN`. No supported row
     reads a NaN's sign (`signFloat` is a parameter row).
  Readings, marked: "the next lowest / next highest floating-point value which is an integer" is
  the integer itself at an integer (so `floorFloat(2.0f)` is `2.0f`; no point of `vals` is at an
  integer); "the smallest positive finite value" (1603-1604) counts subnormal data ([S]).
  The prose's typos, read as meant: "A suffix of `f` or `f`" (1484) is `f` or `F` (the syntax, 1495);
  `smt-hook(fg.gt)` (1644).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HooksFloatTest

open KCore ML Faithful

/-! ## Γ at an interpreted symbol's application (as test/HooksString.lean writes it) -/

/-- The interpreted symbol `k` applied to the values `vs`, as Γ writes it. -/
abbrev appP (c : Semantics) (k : CtorSig) (vs : List GroundTerm) : KoreAML.P :=
  KoreAML.den (symApp c k.name (GroundTerm.koreList c vs))

def sig (f : Sym) : CtorSig := (lookupSig hookSigs f).getD default

/-- The interpretation that gives `v` everywhere. -/
def constH (v : GroundTerm) : HookParams := ⟨fun _ _ => some v⟩

/-- Where `hook` gives a value, Γ states it, in every semantics. -/
theorem gamma_val (c : Semantics) {k : CtorSig} (hk : k ∈ hookSigs) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) {v : GroundTerm} (hh : hook k.name vs = some (some v)) :
    Γ c (appP c k vs ≡ den c v) :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨k, vs, some v, hk, hvs, hh, nofun, rfl⟩)))))

/-- At a silent point, `Γ (c.withHooks H)` holds the fallback's graph. -/
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

theorem fallback_const (c : Semantics) (hr : ∀ k ∈ c.params, k.raw = false) {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) (vs : List GroundTerm) {v : GroundTerm}
    (hv : c.sortOf v = some k.result) : (c.withHooks (constH v)).fallback k.name vs = some v := by
  unfold Semantics.fallback; rw [hks, Semantics.sortOf_withHooks c _ hr]
  simp [Semantics.withHooks, constH, Option.filter, hv]

/-- **Γ does not determine a silent point.** Over all interpretations, Γ entails neither that the
application has no value nor that it is `v`: under `HookParams.none` it is ⊥ in every model, under
`constH v` it is `v` in every model, and both theories have models (`sound_hyp`). -/
theorem undetermined (c : Semantics) (hok : c.coreOK = true) (hr : ∀ k ∈ c.params, k.raw = false)
    {k : CtorSig}
    (hks : lookupSig hookSigs k.name = some k) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some k.args) (hh : hook k.name vs = some none) (hs : silent k.name vs = true)
    {v : GroundTerm} (hv : c.sortOf v = some k.result)
    (hfn₀ : FnHyp (c.withHooks HookParams.none)) (hfnv : FnHyp (c.withHooks (constH v))) :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) k vs ≡ den (c.withHooks H) v)) := by
  constructor
  · -- under `constH v` the application is `v`'s element, so not ⊥
    intro hall
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
  · -- under `HookParams.none` the application is ⊥, so not `v`
    intro hall
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

/-! ## Values -/

/-- The Float literal of the format `(p, e)` with the encoding `b`. -/
def fv (p e b : Nat) : GroundTerm := .dv Srt.float (.float p e b)

/-- binary32, `p24x8` (DOM 1484, 1488-1489). -/
def f32 (b : Nat) : GroundTerm := fv 24 8 b

/-- binary64, `p53x11` (DOM 1485, 1489-1490). -/
def f64 (b : Nat) : GroundTerm := fv 53 11 b

theorem hook_at {f : Sym} {h : List GroundTerm → Option GroundTerm}
    (hf : hookTable.find? (·.1 == f) = some (f, h)) (vs : List GroundTerm) : hook f vs = some (h vs) := by
  rw [hook_eq, hf]; rfl

theorem asInt_int (i : Int) : asInt (int i) = some i := by simp [asInt, int]

theorem asFloat_fv (p e b : Nat) :
    asFloat (fv p e b) = (KFloat.spec? p e).map fun sp => (p, e, sp, KFloat.unpackBits sp b) := by
  simp [asFloat, fv]

/-! ## `hook` by the helper of each row -/

theorem hk_add (vs : List GroundTerm) : hook floatAdd vs = some (fl2 Float.Model.UnpackedFloat.add vs) :=
  hook_at rfl vs
theorem hk_sub (vs : List GroundTerm) : hook floatSub vs = some (fl2 Float.Model.UnpackedFloat.sub vs) :=
  hook_at rfl vs
theorem hk_mul (vs : List GroundTerm) : hook floatMul vs = some (fl2 Float.Model.UnpackedFloat.mul vs) :=
  hook_at rfl vs
theorem hk_div (vs : List GroundTerm) : hook floatDiv vs = some (fl2 Float.Model.UnpackedFloat.div vs) :=
  hook_at rfl vs
theorem hk_rem (vs : List GroundTerm) : hook floatRem vs = some (fl2 KFloat.remainder vs) :=
  hook_at rfl vs
theorem hk_neg (vs : List GroundTerm) :
    hook floatNeg vs = some (fl1 (fun _ => Float.Model.UnpackedFloat.neg) vs) := hook_at rfl vs
theorem hk_abs (vs : List GroundTerm) :
    hook floatAbs vs = some (fl1 (fun _ => Float.Model.UnpackedFloat.abs) vs) := hook_at rfl vs
theorem hk_floor (vs : List GroundTerm) :
    hook floatFloor vs = some (fl1 (fun s => KFloat.roundToIntegral s .down) vs) := hook_at rfl vs
theorem hk_ceil (vs : List GroundTerm) :
    hook floatCeil vs = some (fl1 (fun s => KFloat.roundToIntegral s .up) vs) := hook_at rfl vs
theorem hk_trunc (vs : List GroundTerm) :
    hook floatTrunc vs = some (fl1 (fun s => KFloat.roundToIntegral s .zero) vs) := hook_at rfl vs
theorem hk_le (vs : List GroundTerm) :
    hook floatLe vs = some (flCmp (fun o => o == some .lt || o == some .eq) vs) := hook_at rfl vs
theorem hk_lt (vs : List GroundTerm) : hook floatLt vs = some (flCmp (fun o => o == some .lt) vs) :=
  hook_at rfl vs
theorem hk_ge (vs : List GroundTerm) :
    hook floatGe vs = some (flCmp (fun o => o == some .gt || o == some .eq) vs) := hook_at rfl vs
theorem hk_gt (vs : List GroundTerm) : hook floatGt vs = some (flCmp (fun o => o == some .gt) vs) :=
  hook_at rfl vs
theorem hk_eq (vs : List GroundTerm) : hook floatEq vs = some (flCmp (fun o => o == some .eq) vs) :=
  hook_at rfl vs
theorem hk_isNaN (vs : List GroundTerm) : hook floatIsNaN vs = some (flTest KFloat.isNaN vs) :=
  hook_at rfl vs
theorem hk_prec (vs : List GroundTerm) : hook floatPrecision vs = some (flFmt (fun p _ => (p : Int)) vs) :=
  hook_at rfl vs
theorem hk_expb (vs : List GroundTerm) : hook floatExponentBits vs = some (flFmt (fun _ e => (e : Int)) vs) :=
  hook_at rfl vs
theorem hk_round (vs : List GroundTerm) : hook floatRound vs = some (flTo KFloat.convertFormat vs) :=
  hook_at rfl vs
theorem hk_ofInt (vs : List GroundTerm) : hook int2Float vs = some (flOfInt vs) := hook_at rfl vs
theorem hk_max (vs : List GroundTerm) : hook floatMaxValue vs = some (flAt KFloat.maxValue vs) :=
  hook_at rfl vs
theorem hk_min (vs : List GroundTerm) : hook floatMinValue vs = some (flAt KFloat.minValue vs) :=
  hook_at rfl vs

/-! ## Where the helpers give no value -/

/-- A format has a model exactly when its precision and its exponent bits are both at least 2. -/
theorem spec_none (p e : Nat) : KFloat.spec? p e = none ↔ (p < 2 ∨ e < 2) := by
  unfold KFloat.spec?
  split
  · rename_i h; exact ⟨fun h' => (nomatch h'), fun h' => by omega⟩
  · rename_i h; exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem spec_pos {p e : Nat} {sp : Float.Model.Format} (h : KFloat.spec? p e = some sp) : 2 ≤ p ∧ 2 ≤ e := by
  by_cases hc : p < 2 ∨ e < 2
  · rw [(spec_none p e).mpr hc] at h; cases h
  · omega

theorem fl1_none (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (p e b : Nat) : fl1 op [fv p e b] = none ↔ KFloat.spec? p e = none := by
  simp only [fl1, asFloat_fv]
  cases KFloat.spec? p e <;> simp

theorem flTest_none (t : Float.Model.UnpackedFloat → Bool) (p e b : Nat) :
    flTest t [fv p e b] = none ↔ KFloat.spec? p e = none := by
  simp only [flTest, asFloat_fv]
  cases KFloat.spec? p e <;> simp

theorem fl2_none
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (p e b p' e' b' : Nat) : fl2 op [fv p e b, fv p' e' b'] = none ↔
      (KFloat.spec? p e = none ∨ KFloat.spec? p' e' = none ∨ ¬(p = p' ∧ e = e')) := by
  simp only [fl2, asFloat_fv]
  cases KFloat.spec? p e <;> cases KFloat.spec? p' e' <;> simp

theorem flCmp_none (t : Option Ordering → Bool) (p e b p' e' b' : Nat) :
    flCmp t [fv p e b, fv p' e' b'] = none ↔ (KFloat.spec? p e = none ∨ KFloat.spec? p' e' = none) := by
  simp only [flCmp, asFloat_fv]
  cases KFloat.spec? p e <;> cases KFloat.spec? p' e' <;> simp

theorem flAt_none (op : Float.Model.Format → Float.Model.UnpackedFloat) (x y : Int) :
    flAt op [int x, int y] = none ↔ KFloat.spec? x.toNat y.toNat = none := by
  simp only [flAt, asInt_int, Option.bind_some]
  cases KFloat.spec? x.toNat y.toNat <;> simp

theorem flTo_none (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (p e b : Nat) (x y : Int) : flTo op [fv p e b, int x, int y] = none ↔
      (KFloat.spec? p e = none ∨ KFloat.spec? x.toNat y.toNat = none) := by
  simp only [flTo, asFloat_fv, asInt_int, Option.bind_some]
  cases KFloat.spec? p e <;> cases KFloat.spec? x.toNat y.toNat <;> simp

theorem flOfInt_none (n x y : Int) :
    flOfInt [int n, int x, int y] = none ↔ KFloat.spec? x.toNat y.toNat = none := by
  simp only [flOfInt, asInt_int, Option.bind_some]
  cases KFloat.spec? x.toNat y.toNat <;> simp

/-! ## The rows -/

/-- The twenty-two supported operation rows: the symbol and its `hook` attribute in the prose's
productions (DOM 1511 `FLOAT.precision`, 1519 `exponentBits`, 1544 `isNaN`, 1562 `neg`, 1565 `mul`,
1566 `div`, 1567 `rem`, 1569 `add`, 1570 `sub`, 1608 `abs`, 1609 `round`, 1610 `floor`, 1611 `ceil`,
1612 `trunc`, 1625 `maxValue`, 1626 `minValue`, 1641 `le`, 1642 `lt`, 1643 `ge`, 1644 `gt`, 1645
`eq`, 1661 `int2float`). The twenty-third row is the sort (`FLOAT.Float`, DOM 1494). -/
def rows : List (Sym × String) :=
  [(floatPrecision, "FLOAT.precision"), (floatExponentBits, "FLOAT.exponentBits"), (floatIsNaN, "FLOAT.isNaN"),
   (floatNeg, "FLOAT.neg"), (floatMul, "FLOAT.mul"), (floatDiv, "FLOAT.div"), (floatRem, "FLOAT.rem"),
   (floatAdd, "FLOAT.add"), (floatSub, "FLOAT.sub"), (floatAbs, "FLOAT.abs"), (floatRound, "FLOAT.round"),
   (floatFloor, "FLOAT.floor"), (floatCeil, "FLOAT.ceil"), (floatTrunc, "FLOAT.trunc"),
   (floatMaxValue, "FLOAT.maxValue"), (floatMinValue, "FLOAT.minValue"),
   (floatLe, "FLOAT.le"), (floatLt, "FLOAT.lt"), (floatGe, "FLOAT.ge"), (floatGt, "FLOAT.gt"),
   (floatEq, "FLOAT.eq"), (int2Float, "FLOAT.int2float")]

def fmts : List Sym := [floatPrecision, floatExponentBits]
def unary : List Sym := [floatNeg, floatAbs, floatFloor, floatCeil, floatTrunc]
def cmps : List Sym := [floatLe, floatLt, floatGe, floatGt, floatEq]
def arith : List Sym := [floatAdd, floatSub, floatMul, floatDiv, floatRem]
def ats : List Sym := [floatMaxValue, floatMinValue]

/-- The twenty keys of `silentTable` among the rows. -/
def keys : List Sym := unary ++ [floatIsNaN] ++ cmps ++ arith ++ [floatRound, int2Float] ++ ats

/-- The rows are the registry's entries with a `FLOAT.` hook, and `fmts` and `keys` part them. -/
theorem rows_registry :
    ((regHookNames.filter (fun e => e.2.toList.take 6 == "FLOAT.".toList)).all rows.contains &&
    rows.all regHookNames.contains &&
    rows.all (fun r => (fmts ++ keys).count r.1 == 1) &&
    (fmts ++ keys).all (fun f => rows.any (·.1 == f)) &&
    rows.all (fun r => decide (sig r.1 ∈ hookSigs) && (sig r.1).name == r.1)) = true := by
  decide +kernel

/-! ## Statement 3 -/

/-- **The groups against `silentTable` and `partialHooks`**: `precisionFloat` and
`exponentBitsFloat` are no key (and among `partialHooks`: a value of sort Float that is no literal
would have none, which `floatShapeOK` excludes); each of the twenty others is a key. -/
theorem groups :
    (fmts.all (fun f => !silentKey f && partialHooks.contains f) && keys.all silentKey) = true := by
  decide +kernel

/-- **Each of the twenty keys has a predicate true at every argument list**: its silent points are
the argument lists where `hook` gives no value. -/
theorem keys_silent : ∀ f ∈ keys, ∀ vs : List GroundTerm, silent f vs = true := by
  intro f hf vs
  simp only [keys, unary, cmps, arith, ats, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The silent predicate of `precisionFloat` and `exponentBitsFloat` is true nowhere. -/
theorem fmts_not_silent : ∀ f ∈ fmts, ∀ vs : List GroundTerm, silent f vs = false := by
  intro f hf vs
  refine silent_of_not_silentKey ?_ vs
  simp only [fmts, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> decide +kernel

/-- `--Float`, `absFloat`, `floorFloat`, `ceilFloat`, `truncFloat`: no value exactly at an operand of
a format without a model. -/
theorem unary_none : ∀ f ∈ unary, ∀ p e b : Nat, hook f [fv p e b] = some none ↔ (p < 2 ∨ e < 2) := by
  intro f hf p e b
  simp only [unary, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · rw [hk_neg, Option.some.injEq, fl1_none, spec_none]
  · rw [hk_abs, Option.some.injEq, fl1_none, spec_none]
  · rw [hk_floor, Option.some.injEq, fl1_none, spec_none]
  · rw [hk_ceil, Option.some.injEq, fl1_none, spec_none]
  · rw [hk_trunc, Option.some.injEq, fl1_none, spec_none]

/-- `isNaN`: the same. -/
theorem isNaN_none (p e b : Nat) : hook floatIsNaN [fv p e b] = some none ↔ (p < 2 ∨ e < 2) := by
  rw [hk_isNaN, Option.some.injEq, flTest_none, spec_none]

/-- The five comparisons: no value exactly where an operand is of a format without a model; a value
at two operands of two formats. -/
theorem cmp_none : ∀ f ∈ cmps, ∀ p e b p' e' b' : Nat,
    hook f [fv p e b, fv p' e' b'] = some none ↔ ((p < 2 ∨ e < 2) ∨ (p' < 2 ∨ e' < 2)) := by
  intro f hf p e b p' e' b'
  simp only [cmps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · rw [hk_le, Option.some.injEq, flCmp_none, spec_none, spec_none]
  · rw [hk_lt, Option.some.injEq, flCmp_none, spec_none, spec_none]
  · rw [hk_ge, Option.some.injEq, flCmp_none, spec_none, spec_none]
  · rw [hk_gt, Option.some.injEq, flCmp_none, spec_none, spec_none]
  · rw [hk_eq, Option.some.injEq, flCmp_none, spec_none, spec_none]

/-- The five arithmetic operations: no value exactly where an operand is of a format without a
model, or the two operands are of two formats. -/
theorem arith_none : ∀ f ∈ arith, ∀ p e b p' e' b' : Nat,
    hook f [fv p e b, fv p' e' b'] = some none ↔
      ((p < 2 ∨ e < 2) ∨ (p' < 2 ∨ e' < 2) ∨ ¬(p = p' ∧ e = e')) := by
  intro f hf p e b p' e' b'
  simp only [arith, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · rw [hk_add, Option.some.injEq, fl2_none, spec_none, spec_none]
  · rw [hk_sub, Option.some.injEq, fl2_none, spec_none, spec_none]
  · rw [hk_mul, Option.some.injEq, fl2_none, spec_none, spec_none]
  · rw [hk_div, Option.some.injEq, fl2_none, spec_none, spec_none]
  · rw [hk_rem, Option.some.injEq, fl2_none, spec_none, spec_none]

/-- `roundFloat`: no value exactly where the operand is of a format without a model, or the
precision or the exponent bits asked for are below 2. -/
theorem round_none (p e b : Nat) (x y : Int) : hook floatRound [fv p e b, int x, int y] = some none ↔
    ((p < 2 ∨ e < 2) ∨ (x < 2 ∨ y < 2)) := by
  rw [hk_round, Option.some.injEq, flTo_none, spec_none, spec_none]
  constructor <;> intro h <;> omega

/-- `Int2Float`: no value exactly at a precision or exponent bits below 2. -/
theorem int2Float_none (n x y : Int) : hook int2Float [int n, int x, int y] = some none ↔ (x < 2 ∨ y < 2) := by
  rw [hk_ofInt, Option.some.injEq, flOfInt_none, spec_none]
  constructor <;> intro h <;> omega

/-- `maxValueFloat`, `minValueFloat`: the same. -/
theorem at_none : ∀ f ∈ ats, ∀ x y : Int, hook f [int x, int y] = some none ↔ (x < 2 ∨ y < 2) := by
  intro f hf x y
  simp only [ats, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [hk_max, Option.some.injEq, flAt_none, spec_none]; constructor <;> intro h <;> omega
  · rw [hk_min, Option.some.injEq, flAt_none, spec_none]; constructor <;> intro h <;> omega

/-! ## The sort row `FLOAT.Float` -/

/-- Every encoding of a format is a value of sort Float (DOM 1464-1466, 1494), in every semantics. -/
theorem float_value (c : Semantics) {p e b : Nat} (h : KFloat.ok p e b = true) :
    c.sortOf (fv p e b) = some Srt.float :=
  sortOf_dv.mpr ⟨by simp [dvOK, h], rfl⟩

/-- Two encodings, or two formats, are two values. -/
theorem float_inj {p e b p' e' b' : Nat} (h : fv p e b = fv p' e' b') : p = p' ∧ e = e' ∧ b = b' := by
  simp only [fv, GroundTerm.dv.injEq, Lit.float.injEq, true_and] at h; exact h

/-- Nothing else is a value of sort Float (under `floatShapeOK`, which `coreOK` gives,
`floatShapeOK_of_coreOK`): the prose gives Float no constructor, only the tokens of DOM 1495-1497. -/
theorem float_only {c : Semantics} (hf : c.floatShapeOK = true) {v : GroundTerm}
    (h : c.sortOf v = some Srt.float) : ∃ p e b, v = fv p e b ∧ KFloat.ok p e b = true :=
  shape_float hf h

/-- The precision and the exponent bits of a value are positive (DOM 1475). -/
theorem ok_pos {p e b : Nat} (h : KFloat.ok p e b = true) : 1 ≤ p ∧ 1 ≤ e := by
  unfold KFloat.ok at h
  cases hs : KFloat.spec? p e with
  | some s => have := spec_pos hs; omega
  | none =>
    rw [hs] at h
    simp only [KFloat.thinOK, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

/-- `precisionFloat` and `exponentBitsFloat` at a literal of positive precision and exponent bits. -/
theorem fmt_at (p e b : Nat) (hp : 1 ≤ p) (he : 1 ≤ e) :
    hook floatPrecision [fv p e b] = some (some (int p)) ∧
    hook floatExponentBits [fv p e b] = some (some (int e)) := by
  rw [hk_prec, hk_expb]
  simp [flFmt, fv, hp, he]

/-- **`precisionFloat` and `exponentBitsFloat` have their value at every argument list of the
signature**: a Float value is a literal of a format `(p, e)`, and they are `p` and `e` (DOM 1508,
1516, 1483-1487). -/
theorem covered_fmt {c : Semantics} (hf : c.floatShapeOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.float]) : ∃ p e b, vs = [fv p e b] ∧
      hook floatPrecision vs = some (some (int p)) ∧ hook floatExponentBits vs = some (some (int e)) := by
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  obtain ⟨p, e, b, rfl, hok⟩ := float_only hf hw
  obtain ⟨hp, he⟩ := ok_pos hok
  exact ⟨p, e, b, rfl, fmt_at p e b hp he⟩

/-- An argument list of two Floats is two literals (with `cmp_none`, `arith_none`). -/
theorem covered_ff {c : Semantics} (hf : c.floatShapeOK = true) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some [Srt.float, Srt.float]) :
    ∃ p e b p' e' b', vs = [fv p e b, fv p' e' b'] := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := sortsOf_two hvs
  obtain ⟨p, e, b, rfl, -⟩ := float_only hf h₁
  obtain ⟨p', e', b', rfl, -⟩ := float_only hf h₂
  exact ⟨p, e, b, p', e', b', rfl⟩

/-! ## The format of a result (DOM 1580-1582, 1653-1654, 1601-1604) -/

theorem fmt_floatV (p e : Nat) (sp : Float.Model.Format) (u : Float.Model.UnpackedFloat) (hp : 1 ≤ p)
    (he : 1 ≤ e) : hook floatPrecision [floatV p e sp u] = some (some (int p)) ∧
      hook floatExponentBits [floatV p e sp u] = some (some (int e)) :=
  fmt_at p e _ hp he

/-- **"The resulting `Float` will yield the specified values when calling `precisionFloat` and
`exponentBitsFloat`"** (DOM 1580-1582), at every value of `roundFloat`. -/
theorem round_format (p e b : Nat) (x y : Int) {v : GroundTerm}
    (h : hook floatRound [fv p e b, int x, int y] = some (some v)) :
    hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
  rw [hk_round, Option.some.injEq] at h
  simp only [flTo, asFloat_fv, asInt_int, Option.bind_some] at h
  cases h1 : KFloat.spec? p e with
  | none => rw [h1] at h; simp at h
  | some sp =>
    cases h2 : KFloat.spec? x.toNat y.toNat with
    | none => rw [h1, h2] at h; simp at h
    | some sq =>
      rw [h1, h2] at h
      simp at h
      obtain ⟨hx, hy⟩ := spec_pos h2
      have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
      have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
      have := fmt_floatV x.toNat y.toNat sq (KFloat.convertFormat sq (KFloat.unpackBits sp b)) (by omega) (by omega)
      rw [h, hx', hy'] at this
      exact this

/-- The same of `Int2Float` ("with the specified precision and exponent range", DOM 1653-1654). -/
theorem int2Float_format (n x y : Int) {v : GroundTerm}
    (h : hook int2Float [int n, int x, int y] = some (some v)) :
    hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
  rw [hk_ofInt, Option.some.injEq] at h
  simp only [flOfInt, asInt_int, Option.bind_some] at h
  cases h2 : KFloat.spec? x.toNat y.toNat with
  | none => rw [h2] at h; simp at h
  | some sq =>
    rw [h2] at h
    simp at h
    obtain ⟨hx, hy⟩ := spec_pos h2
    have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
    have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
    have := fmt_floatV x.toNat y.toNat sq (Float.Model.UnpackedFloat.ofInt sq n) (by omega) (by omega)
    rw [h, hx', hy'] at this
    exact this

/-- The same of `maxValueFloat` and `minValueFloat` ("expressible in a specified precision and
exponent range", DOM 1601-1604). -/
theorem at_format : ∀ f ∈ ats, ∀ (x y : Int) {v : GroundTerm}, hook f [int x, int y] = some (some v) →
    hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
  have key : ∀ (op : Float.Model.Format → Float.Model.UnpackedFloat) (x y : Int) {v : GroundTerm},
      flAt op [int x, int y] = some v →
      hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
    intro op x y v h
    simp only [flAt, asInt_int, Option.bind_some] at h
    cases h2 : KFloat.spec? x.toNat y.toNat with
    | none => rw [h2] at h; simp at h
    | some sq =>
      rw [h2] at h
      simp at h
      obtain ⟨hx, hy⟩ := spec_pos h2
      have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
      have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
      have := fmt_floatV x.toNat y.toNat sq (op sq) (by omega) (by omega)
      rw [h, hx', hy'] at this
      exact this
  intro f hf x y v h
  simp only [ats, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [hk_max, Option.some.injEq] at h; exact key _ x y h
  · rw [hk_min, Option.some.injEq] at h; exact key _ x y h

/-! ## The semantics of `strbytes` (`coreOK`, no function) -/

definition_of defn from "f2-examples/strbytes.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

tables_of T from "f2-examples/strbytes.kompile.kore"

theorem T_eq : T = tables c := by decide +kernel

set_option maxHeartbeats 1000000 in
open Faithful.Model in
theorem coreOK : c.coreOK = true :=
  Semantics.coreOK_of_T T_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide_cheap)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) := by
  have h : (c.withHooks H).fns = [] := fns_nil
  have hrc : (c.withHooks H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c
  refine ⟨?_, ?_, ?_, ?_, openDecided_of_readsConfined hrc, openLaws_of_plain (c := c.withHooks H) (show ∀ k ∈ c.params, k.raw = false by decide +kernel)⟩ <;> intro fn hfn <;> rw [h] at hfn <;>
    exact absurd hfn List.not_mem_nil

/-- Every value of sort Float of `strbytes` is a literal. -/
theorem floatShape : c.floatShapeOK = true := floatShapeOK_of_coreOK coreOK

/-! ## The data of the points, each encoding derived by hand

[S] The encoding of a datum of `p24x8`, IEEE 754 binary32 (DOM 1488-1489; the interchange
encoding): from the top, 1 sign bit, 8 bits of the exponent plus 127, 23 bits of the significand after
its leading 1. `±1.f × 2^x` is the sign, then `x + 127`, then `f`. A zero is all zero bits after the
sign; an infinity has the exponent field all ones and the significand field zero; the smallest
positive datum 2^-149 is the significand field 1 alone; the largest finite one has the exponent
field 254 and the significand field all ones. `p53x11`, binary64: 1, 11 (the exponent plus 1023) and
52 bits. The NaN's encoding (exponent field all ones, the top significand bit) is KCore's choice of
one NaN per format (the syntax, DOM 1497, writes neither sign nor payload). -/

/-- `0.0f` and `-0.0f`. -/
def z : GroundTerm := f32 0x00000000
def nz : GroundTerm := f32 0x80000000
/-- `1.0f` = 1.0 × 2^0: exponent field 127 = 0111 1111, so 0 01111111 000… = 0x3F800000. -/
def one : GroundTerm := f32 0x3F800000
def mone : GroundTerm := f32 0xBF800000
/-- `0.5f` = 1.0 × 2^-1: exponent field 126, 0 01111110 000… = 0x3F000000. `-0.5f` with the sign. -/
def half : GroundTerm := f32 0x3F000000
def mhalf : GroundTerm := f32 0xBF000000
/-- `1.5f` = 1.1b × 2^0: 0x3F800000 with the top significand bit, 0x00400000. -/
def oneHalf : GroundTerm := f32 0x3FC00000
/-- `2.0f` = 1.0 × 2^1: exponent field 128, 0 10000000 000… = 0x40000000. -/
def two : GroundTerm := f32 0x40000000
def mtwo : GroundTerm := f32 0xC0000000
/-- `2.5f` = 1.01b × 2^1: 0x40000000 with the second significand bit, 0x00200000. -/
def twoHalf : GroundTerm := f32 0x40200000
def mtwoHalf : GroundTerm := f32 0xC0200000
/-- `3.0f` = 1.1b × 2^1: 0x40000000 with 0x00400000. -/
def three : GroundTerm := f32 0x40400000
def mthree : GroundTerm := f32 0xC0400000
/-- `5.0f` = 1.01b × 2^2: exponent field 129, 0 10000001 000… = 0x40800000, with 0x00200000. -/
def five : GroundTerm := f32 0x40A00000
/-- `6.0f` = 1.1b × 2^2: 0x40800000 with 0x00400000. -/
def six : GroundTerm := f32 0x40C00000
/-- `Infinityf`, `-Infinityf`: exponent field 255, significand field 0. -/
def inf : GroundTerm := f32 0x7F800000
def minf : GroundTerm := f32 0xFF800000
/-- `NaNf`. -/
def nan : GroundTerm := f32 0x7FC00000
/-- 2^-24 = 1.0 × 2^-24: exponent field 103 = 0110 0111, 0 01100111 000… = 0x33800000. -/
def tiny : GroundTerm := f32 0x33800000
/-- 1 + 2^-23 and 1 + 2^-22: `1.0f` with the significand field 1 and 2. -/
def onePlus : GroundTerm := f32 0x3F800001
def onePlus2 : GroundTerm := f32 0x3F800002
/-- The largest finite datum of binary32, (2 - 2^-23) × 2^127: exponent field 254, significand field
all ones. The smallest positive one, 2^-149: the significand field 1 alone. -/
def max32 : GroundTerm := f32 0x7F7FFFFF
def min32 : GroundTerm := f32 0x00000001
/-- binary64: `0.0`, `-0.0` (the sign bit, bit 63), `1.0` (exponent field 1023 = 0x3FF), `1.5` (with
the top significand bit, bit 51), `-2.0` (the sign, exponent field 1024 = 0x400), `NaN`. -/
def z64 : GroundTerm := f64 0x0000000000000000
def nz64 : GroundTerm := f64 0x8000000000000000
def one64 : GroundTerm := f64 0x3FF0000000000000
def oneHalf64 : GroundTerm := f64 0x3FF8000000000000
def mtwo64 : GroundTerm := f64 0xC000000000000000
def nan64 : GroundTerm := f64 0x7FF8000000000000

/-- Literals of the prose's syntax (DOM 1469-1490, 1495-1497) with the datum each names: the suffix
`f` is `p24x8`, `d` or none `p53x11` (1484-1490). -/
def lits : List (String × GroundTerm) :=
  [("0.0f", z), ("-0.0f", nz), ("1.0f", one), ("-1.0f", mone), ("0.5f", half), ("1.5f", oneHalf),
   ("2.0f", two), ("2.5f", twoHalf), ("-2.5f", mtwoHalf), ("3.0f", three), ("5.0f", five), ("6.0f", six),
   ("1.0p24x8", one), ("1.5e0f", oneHalf), ("Infinityf", inf), ("-Infinityf", minf), ("NaNf", nan),
   ("0.0", z64), ("0.0d", z64), ("0.0p53x11", z64), ("-0.0", nz64), ("1.0", one64), ("1.5", oneHalf64),
   ("-2.0", mtwo64), ("NaN", nan64)]

/-- **The reader takes each literal to the datum written by hand.** -/
theorem lits_read : lits.all (fun l => (Parse.floatLit? l.1).map (GroundTerm.dv Srt.float) == some l.2) = true := by
  decide +kernel

structure Pt where
  f : Sym
  vs : List GroundTerm
  v : GroundTerm
  deriving DecidableEq

/-! ## Statement 1: in-domain values -/

/-- The expected values, each derived by hand and marked by its source (the header).
- `precisionFloat`, `exponentBitsFloat` [P] (DOM 1484-1490): `1.0f` is `p24x8`, 24 and 8; `1.0` is
  `p53x11`, 53 and 11.
- `isNaN` [P] (1541): true of `NaN`; false of `1.0f`; false of `Infinity`, which the sentence sets
  apart ("infinite or Not-a-Number").
- `--Float` [P]: "`--Float 0.0` is negative zero" (1554); the negation of `1.0f` is `-1.0f` (1552).
- `-Float` [P]: "`0.0 -Float 0.0` is positive zero" (1553); 3 - 1 = 2.
- `+Float`: [P] 1 + 2 = 3 (1559). [A] 1569, a tie: 1 + 2^-24 is halfway between 1 and 1 + 2^-23, the
  next datum of binary32, and the one with the even significand is 1; (1 + 2^-23) + 2^-24 is halfway
  between 1 + 2^-23 (significand field 1, odd) and 1 + 2^-22 (2, even): the latter.
- `*Float` [P]: 2 × 3 = 6 (1556). `/Float`: [P] 3 / 2 = 1.5; [S] division by zero, 1 / 0 = +∞; [S] invalid
  operation, 0 / 0 is a NaN.
- `%Float`: [P] (1557-1558) 5 / 3 = 1.66…, the nearest integer is 2, and 5 - 3 × 2 = -1. [A] 1567 and
  [S] remainder: 5 / 2 = 2.5 is halfway between 2 and 3, the even one is 2, and 5 - 2 × 2 = 1 (finding 5).
- `absFloat`: [P] (1578) of `-1.0f` it is `1.0f`; [S] abs, of `-0.0f` it is `0.0f`.
- `floorFloat` [P] (1583-1584): the next lowest integer from 2.5 is 2, from -2.5 it is -3.
  `ceilFloat` [P] (1585-1586): 3 and -2. `truncFloat` [P] (1587-1588, "in the direction of zero"): 2
  and -2. [S] a zero result has the operand's sign: `floorFloat(0.5f)` is `0.0f`,
  `ceilFloat(-0.5f)` is `-0.0f` (finding 3).
- `roundFloat` [P] (1579-1580): 1.5 of `p53x11` to precision 24 and exponent bits 8 is `1.5f`, which
  `p24x8` holds exactly.
- `Int2Float` [P] (1653-1654): 3 at 24, 8 is `3.0f`; -2 at 53, 11 is `-2.0`.
- `maxValueFloat`, `minValueFloat` (1601-1604): [P] the largest finite and the smallest positive
  datum of the format; [S] which data those are in binary32 (`max32`, `min32`).
- The comparisons. [P] "`0.0 ==Float -0.0` is also true" (1638); "`NaN` compares unequal to all
  values, including itself" (1637), so `NaN ==Float NaN` is false; 1 < 2, not 2 < 1; 1 ≤ 1, not 2 ≤ 1;
  2 > 1, not 1 > 1; 1 ≥ 1, not 1 ≥ 2 (1631-1632). [S] comparison: a NaN is unordered with every datum, so
  `NaN <Float 1.0f` and `NaN >=Float 1.0f` are false; `-0.0 <=Float 0.0` is true and
  `-0.0 <Float 0.0` false (the zeros are equal). -/
def vals : List Pt :=
  [⟨floatPrecision, [one], int 24⟩, ⟨floatPrecision, [one64], int 53⟩,
   ⟨floatExponentBits, [one], int 8⟩, ⟨floatExponentBits, [one64], int 11⟩,
   ⟨floatIsNaN, [nan], bool true⟩, ⟨floatIsNaN, [one], bool false⟩, ⟨floatIsNaN, [inf], bool false⟩,
   ⟨floatNeg, [z64], nz64⟩, ⟨floatNeg, [one], mone⟩,
   ⟨floatSub, [z64, z64], z64⟩, ⟨floatSub, [three, one], two⟩,
   ⟨floatAdd, [one, two], three⟩, ⟨floatAdd, [one, tiny], one⟩, ⟨floatAdd, [onePlus, tiny], onePlus2⟩,
   ⟨floatMul, [two, three], six⟩,
   ⟨floatDiv, [three, two], oneHalf⟩, ⟨floatDiv, [one, z], inf⟩, ⟨floatDiv, [z, z], nan⟩,
   ⟨floatRem, [five, three], mone⟩, ⟨floatRem, [five, two], one⟩,
   ⟨floatAbs, [mone], one⟩, ⟨floatAbs, [nz], z⟩,
   ⟨floatFloor, [twoHalf], two⟩, ⟨floatFloor, [mtwoHalf], mthree⟩, ⟨floatFloor, [half], z⟩,
   ⟨floatCeil, [twoHalf], three⟩, ⟨floatCeil, [mtwoHalf], mtwo⟩, ⟨floatCeil, [mhalf], nz⟩,
   ⟨floatTrunc, [twoHalf], two⟩, ⟨floatTrunc, [mtwoHalf], mtwo⟩,
   ⟨floatRound, [oneHalf64, int 24, int 8], oneHalf⟩,
   ⟨int2Float, [int 3, int 24, int 8], three⟩, ⟨int2Float, [int (-2), int 53, int 11], mtwo64⟩,
   ⟨floatMaxValue, [int 24, int 8], max32⟩, ⟨floatMinValue, [int 24, int 8], min32⟩,
   ⟨floatEq, [z64, nz64], bool true⟩, ⟨floatEq, [nan, nan], bool false⟩, ⟨floatEq, [one, one], bool true⟩,
   ⟨floatLt, [one, two], bool true⟩, ⟨floatLt, [two, one], bool false⟩,
   ⟨floatLe, [one, one], bool true⟩, ⟨floatLe, [two, one], bool false⟩,
   ⟨floatGt, [two, one], bool true⟩, ⟨floatGt, [one, one], bool false⟩,
   ⟨floatGe, [one, one], bool true⟩, ⟨floatGe, [one, two], bool false⟩,
   ⟨floatLt, [nan, one], bool false⟩, ⟨floatGe, [nan, one], bool false⟩,
   ⟨floatLe, [nz, z], bool true⟩, ⟨floatLt, [nz, z], bool false⟩]

/-- Every row has a point, and every point is of a row. -/
theorem vals_rows : (rows.all (fun r => vals.any fun p => p.f == r.1) &&
    vals.all (fun p => rows.any (·.1 == p.f))) = true := by
  decide +kernel

/-- **`hook`'s value at each point is the one derived by hand**, the arguments of the signature's
sorts. -/
theorem vals_ok : vals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- **(1) At each point the result is that value and Γ states it, under every interpretation.** -/
theorem vals_gamma : ∀ p ∈ vals, ∀ H : HookParams,
    (c.withHooks H).hookRes p.f p.vs = some (some p.v) ∧
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp vals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  refine ⟨Semantics.hookRes_of_value hh, ?_⟩
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-! ## Findings 2, 3, 4: values `hook` gives that no sentence of the prose gives -/

/-- 2^24 = 1.0 × 2^24 in binary32: exponent field 151 = 1001 0111, 0 10010111 000… = 0x4B800000. -/
def big24 : GroundTerm := f32 0x4B800000

/-- Not derived from the prose (the findings say what each is against): `Int2Float(2^24 + 1, 24, 8)`,
halfway between 2^24 and 2^24 + 2, is 2^24 (the even significand; finding 2); `floorFloat` of
`Infinityf` and of `NaNf` is the operand (finding 3); `1.0 ==Float 1.0f` is true and
`1.0f <Float 1.5` is true, across two formats (finding 4). -/
def beyond : List Pt :=
  [⟨int2Float, [int 16777217, int 24, int 8], big24⟩,
   ⟨floatFloor, [inf], inf⟩, ⟨floatFloor, [nan], nan⟩,
   ⟨floatEq, [one64, one], bool true⟩, ⟨floatLt, [one, oneHalf64], bool true⟩]

theorem beyond_ok : beyond.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- Γ states a value at each, under every interpretation: none is a silent point. -/
theorem beyond_gamma : ∀ p ∈ beyond, ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp beyond_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-! ## Statement 2: a point of each row of the two unstated parts -/

/-- The five arithmetic operations at `1.0` (`p53x11`) and `1.0f` (`p24x8`): two formats.
`roundFloat(1.0, 0, 8)` and `(1.0, 24, -1)`, `Int2Float(1, 24, 0)`, `maxValueFloat(0, 8)`,
`minValueFloat(53, 0)`: no format (DOM 1475, "positive"). The value `v` has the result sort. -/
def pts : List Pt :=
  [⟨floatAdd, [one64, one], z64⟩, ⟨floatSub, [one64, one], z64⟩, ⟨floatMul, [one64, one], z64⟩,
   ⟨floatDiv, [one64, one], z64⟩, ⟨floatRem, [one64, one], z64⟩,
   ⟨floatRound, [one64, int 0, int 8], z64⟩, ⟨floatRound, [one64, int 24, int (-1)], z64⟩,
   ⟨int2Float, [int 1, int 24, int 0], z64⟩,
   ⟨floatMaxValue, [int 0, int 8], z64⟩, ⟨floatMinValue, [int 53, int 0], z64⟩]

/-- Every row of the two parts has a point, and every point is of a key. -/
theorem pts_keys : ((arith ++ [floatRound, int2Float] ++ ats).all (fun f => pts.any (·.f == f)) &&
    pts.all (fun p => keys.contains p.f)) = true := by
  decide +kernel

theorem pts_ok : pts.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- Γ determines no point of `ps` whose facts are decided as in `pts_ok`. -/
theorem undetermined_of {ps : List Pt}
    (hok : ps.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
      c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
      c.sortOf p.v == some (sig p.f).result) = true) : ∀ p ∈ ps,
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) := by
  intro p hp
  have h := List.all_eq_true.mp hok p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hks, hvs⟩, hh⟩, hs⟩, hv⟩ := h
  have hname : (sig p.f).name = p.f := (lookupSig_spec hks).2
  exact undetermined c coreOK (by decide +kernel) (by rw [hname]; exact hks) hvs (by rw [hname]; exact hh)
    (by rw [hname]; exact hs) hv (fnHyp _) (fnHyp _)

/-- **(2) Γ determines none of the points**: over all interpretations it entails neither that the
application has no value nor that it is the point's `v`. -/
theorem pts_undetermined : ∀ p ∈ pts,
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) :=
  undetermined_of pts_ok

/-! ## Finding 1: the thin formats -/

/-- A value of the thin format `p1x8`: sign 0, exponent field 127, no significand field (under
reading (A) of finding 1, the datum 1.0 × 2^0 of that format). -/
def t18 : GroundTerm := fv 1 8 127

/-- A point of each of the twenty keys at a thin format: an operand of `p1x8`, or a precision or
exponent bits of 1. -/
def thin : List Pt :=
  [⟨floatNeg, [t18], z64⟩, ⟨floatAbs, [t18], z64⟩, ⟨floatFloor, [t18], z64⟩, ⟨floatCeil, [t18], z64⟩,
   ⟨floatTrunc, [t18], z64⟩, ⟨floatIsNaN, [t18], bool false⟩,
   ⟨floatLe, [t18, t18], bool true⟩, ⟨floatLt, [t18, one], bool true⟩, ⟨floatGe, [one, t18], bool true⟩,
   ⟨floatGt, [t18, t18], bool true⟩, ⟨floatEq, [t18, t18], bool false⟩,
   ⟨floatAdd, [t18, t18], z64⟩, ⟨floatSub, [t18, t18], z64⟩, ⟨floatMul, [t18, t18], z64⟩,
   ⟨floatDiv, [t18, t18], z64⟩, ⟨floatRem, [t18, t18], z64⟩,
   ⟨floatRound, [t18, int 24, int 8], z64⟩, ⟨floatRound, [one64, int 1, int 8], z64⟩,
   ⟨int2Float, [int 1, int 24, int 1], z64⟩,
   ⟨floatMaxValue, [int 1, int 8], z64⟩, ⟨floatMinValue, [int 53, int 1], z64⟩]

theorem thin_keys : (keys.all (fun f => thin.any (·.f == f)) && thin.all (fun p => keys.contains p.f)) = true := by
  decide +kernel

theorem thin_ok : thin.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **At a thin format Γ determines none of the twenty operations** (a fact about Γ; under reading
(A) of finding 1 the prose states a value at each of these points). -/
theorem thin_undetermined : ∀ p ∈ thin,
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (appP (c.withHooks H) (sig p.f) p.vs ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v)) :=
  undetermined_of thin_ok

/-- `precisionFloat` and `exponentBitsFloat` have their values at a thin format. -/
theorem thin_fmt : hook floatPrecision [t18] = some (some (int 1)) ∧
    hook floatExponentBits [t18] = some (some (int 8)) := by
  decide +kernel

#print axioms rows_registry
#print axioms groups
#print axioms keys_silent
#print axioms fmts_not_silent
#print axioms unary_none
#print axioms isNaN_none
#print axioms cmp_none
#print axioms arith_none
#print axioms round_none
#print axioms int2Float_none
#print axioms at_none
#print axioms float_value
#print axioms float_only
#print axioms covered_fmt
#print axioms covered_ff
#print axioms round_format
#print axioms int2Float_format
#print axioms at_format
#print axioms lits_read
#print axioms vals_gamma
#print axioms beyond_gamma
#print axioms pts_undetermined
#print axioms thin_undetermined
#print axioms thin_fmt

end KCore.HooksFloatTest
