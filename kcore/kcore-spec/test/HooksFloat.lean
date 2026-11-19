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
  - **[R]** the representation the prose names: "represented like an IEEE754 floating-point type"
    (1481-1483), binary32 and binary64 for `f` and `d` (1484-1490): which data a format holds and
    their encoding. This file was made without a copy of the standard: what is marked [R] is the
    encoding as recalled, to confirm against it.
  The prose's general reference ("based on a generalization of the IEEE 754 standard", 1464-1466)
  names no operation and is taken to state no value; a value it alone would give is unstated.
  FLOAT's prose writes no `#False` and no `#Bottom`: no row has a point where it states that there
  is no value. "Unstated" is DOM 14-16.

  Not rows here: `isInfinite`, `sqrtFloat` and `=/=Float` have no `hook` attribute (DOM 1545, 1624,
  1646; an equation each, 1673, 1671, 1648); `^Float`, `rootFloat`, `expFloat`, `logFloat`, the
  trigonometric ones, `maxFloat`, `minFloat`, `exponentFloat`, `signFloat`, `Float2Int` are
  parameter rows.

  The rows, by the region where `hook` gives no value (the `*_none` theorems, at every argument list
  of literals; under `floatShapeOK`, which `coreOK` gives, every value of sort Float is a literal of
  a format `(p, e)`, `float_only`). A format has a model here when `p ≥ 2` and `e ≥ 2`; a *thin*
  format has `p = 1` or `e = 1`, both positive. At a thin format (`thinAt`) `hook` computes by the
  same formulas over the rounding to the nearest datum of that format (`thinHooks`). "No format"
  below is a precision or exponent bits of 0 or below.

  | rows | prose | where `hook` gives no value |
  |---|---|---|
  | `FLOAT.precision`, `FLOAT.exponentBits` | DOM 1508, 1516; `total` 1511, 1519 | nowhere at a Float value (`covered_fmt`) |
  | `FLOAT.neg`, `abs` | DOM 1552-1554, 1578; `total` 1562, 1608 | the NaN (`negAbs_none`) |
  | `FLOAT.floor`, `ceil`, `trunc` | DOM 1583-1588; `total` 1610-1612 | an infinity or NaN; a zero result of a nonzero operand; an integer the format does not hold (`roundings_none`, `convert_special`) |
  | `FLOAT.isNaN` | DOM 1541; `total` 1544 | nowhere at a Float literal (`isNaN_none`) |
  | `FLOAT.le`, `lt`, `ge`, `gt`, `eq` | DOM 1631-1638; 1641-1645, no `total` | nowhere at two Float literals (`cmp_none`) |
  | `FLOAT.add`, `sub`, `mul`, `div`, `rem` | DOM 1556-1559; 1565-1570, no `total` | two formats; an infinite or NaN operand; a zero divisor; a zero result, but `0.0 -Float 0.0`; an exact result above the largest finite datum, or one rounding to zero; for `%Float` a quotient halfway between two integers; at precision 1 an exact result halfway between two data (`arith_none`, `arith_special`, `div_rem_zero`, `exact_zero_none`, `above_max_none`) |
  | `FLOAT.round` | DOM 1579-1582; 1609, no `total` | no format; a value the target does not hold, an infinity, NaN (`round_none`, `convert_special`, `held_exact`) |
  | `FLOAT.int2float` | DOM 1653-1654; 1661, no `total` | no format; an Int the target does not hold (`int2Float_none`) |
  | `FLOAT.maxValue`, `FLOAT.minValue` | DOM 1601-1604; 1625, 1626, no `total` | no format; the format `(1, 1)`, whose finite data are the two zeros (`at_none`) |

  `precisionFloat` and `exponentBitsFloat` are no key of `silentTable`. The other twenty are keys
  whose predicate is true at every argument list (`keys_silent`), so the silent points of each are
  exactly the argument lists of the third column. Against the prose that region has four parts:
  - **two formats** (`+Float`, `-Float`, `*Float`, `/Float`, `%Float`): the prose computes "the sum …
    of two floats" (1556-1559) and nowhere says which format the result has when the two differ:
    unstated. Points: `pts`.
  - **no format** (`roundFloat`, `Int2Float`, `maxValueFloat`, `minValueFloat` at a precision or
    exponentBits ≤ 0): `pNxM` names a format for positive N and M only (1475): unstated. Points:
    `pts`.
  - **what the prose does not describe at a format with a model**: findings 2, 3 and 5. Points: `pts`.
  - **a thin format**: the regions above at a thin format, at precision 1 an exact result halfway
    between two data, and `maxValueFloat(1, 1)`, `minValueFloat(1, 1)`: finding 1. Points: `thin`.

  Statements:
  - **(1)** `vals`: points with the value derived as marked; `hook` gives it (`vals_ok`), it is the
    result under every interpretation and Γ states it (`vals_gamma`), in the semantics of
    `f2-examples/strbytes.kompile.kore` (`coreOK`, no function; a Float literal is a value of Float
    in every semantics, `float_value`). The prose's "The resulting `Float` will yield the specified
    values when calling `precisionFloat` and `exponentBitsFloat`" (1580-1582) at every value of
    `roundFloat` (`round_format`), and the same of `Int2Float`, `maxValueFloat`, `minValueFloat`
    ("with the specified precision and exponent range", 1653-1654, 1601-1604: `int2Float_format`,
    `at_format`).
  - **(2)** `pts`: a point of each row of the unstated parts; Γ over all interpretations entails
    neither ⊥ nor a value there (`pts_undetermined`). The same at a point of each key in the thin
    part (`thin_undetermined`), which is a fact about Γ and, by finding 1, not a reading of the prose.
  - **(3)** `groups`, `keys_silent`, the `*_none` theorems, `covered_fmt`.

  The sort row `FLOAT.Float` (DOM 1464-1490, 1494-1497): a value is a datum of a format `(p, e)`, the
  precision and the exponent bits of the literal's suffix (1483-1487), `p24x8` for `f` and `p53x11`
  for `d` or no suffix (1484-1490; `lits_read`: the reader takes each literal of `lits` to the
  encoding written there by hand, and refuses those of `litsRefused`, `lits_refused`). Every such literal is a value
  of sort Float in every semantics (`float_value`), two encodings are two values (`float_inj`: `0.0`
  and `-0.0` are two, 1553-1554), and nothing else is one (`float_only`); a sort has no argument
  list. The encoding (the format's sign, biased exponent and significand fields) is KCore's
  representation of the datum [R]; of a NaN the syntax (1497) writes neither sign nor payload, and
  KCore has one per format (`KFloat.ok`), which no statement here depends on.

  Findings (prose against `hook` and `silentTable`), none of which makes a statement here
  unprovable:
  1. Thin formats (`p1xM`, `pNx1`). DOM 1475 names `pNxM` for "positive integers" N and M, and
     1481-1483 gives the value of such a literal in a type "represented like an IEEE754
     floating-point type, with the number of bits of precision and exponent specified by the
     suffix"; no sentence of an operation distinguishes a format. So an operation at a thin format
     has the status it has at any format: `1.0p1x8` is a datum, `isNaN(1.0p1x8)` is false, `--Float
     1.0p1x8` is `-1.0p1x8`, `maxValueFloat(1, 8)` is 2^127 (unstated at a thin format, beyond the
     regions of a format with a model: a tie at p = 1, `maxValueFloat(1, 1)`, `minValueFloat(1, 1)`).
     KCore's carrier holds values of thin formats (`KFloat.thinOK`), and at every one `hook`
     computes every operation on their data by the formulas of a format with a model over the
     rounding to the nearest datum of the format (`thinHooks`; `thinVals`, `thinVals_gamma`; the data
     are R read at p = 1, ±0, ±2^x, ±∞, the NaN, and at one exponent bit, ±0, ±f·2^(2-p) for
     0 < f < 2^(p-1), ±∞, the NaN: the encoding rule read at one exponent bit, rulings section 7 R1,
     not confirmed against the standard), a tie at p = 1 giving no value; Γ determines none of the
     points of `thin`, each in an unstated region. The comparisons and `isNaN` have a value at every
     Float literal (`cmp_none`, `isNaN_none`). The reader takes no literal of a thin format
     (test/FloatLib.lean). `precisionFloat` and `exponentBitsFloat` have their values there
     (`covered_fmt`).
  2. Rounding. The prose gives a direction only for literals ("rounded to the nearest possible
     value", 1481-1482, naming no rule for a tie and not saying whether an infinity or which zero is
     a possible value for a finite number) and, as attributes, for the five arithmetic operations
     ([A]: the rounding to nearest, a tie to the even significand). `roundFloat` ("Round a
     floating-point number to a specified precision", 1579) and `Int2Float` ("convert an integer to
     a floating-point number", 1653) at a value the format does not hold have no direction in the
     text: unstated, and `hook` gives none (`held_exact`). The reader refuses a literal halfway
     between two data, above the largest finite datum, or nonzero and nearer to zero than to every
     nonzero datum (`litsRefused`, `lits_refused`).
  3. Special data. The sentences for `floorFloat`, `ceilFloat`, `truncFloat` ("the next lowest
     floating-point value which is an integer", 1583-1588) describe no value at an infinity or a
     NaN and no sign for a zero result; `/Float` and `%Float` at a zero divisor, the five
     arithmetic operations at a NaN or an infinity, `--Float` and `absFloat` at a NaN, and the sign
     of a zero result other than `0.0 -Float 0.0` (1553) are not mentioned, and FLOAT writes no
     `#False`: unstated, and `hook` gives none (`pts`). Above the largest finite datum the prose does
     not say whether an infinity is a value to round to: unstated.
  4. Comparisons of two formats. The prose compares "a float … to another float" (1631-1632): the two
     data have values whatever their formats and the result is a Bool, so the comparison is stated;
     `hook` compares the exact values (`vals`: `1.0 ==Float 1.0f` is true). The arithmetic of two
     formats is unstated: its result needs a format and none is named.
  5. `%Float`: "computed based on rounding the quotient of the two floats to the nearest integer"
     (1557-1558) gives no rule for a quotient halfway between two integers, and the attribute's
     mode (1567) is that of the operation's result, which is exact: `5.0f %Float 2.0f` is unstated
     (`pts`).
  Readings, marked: "the next lowest / next highest floating-point value which is an integer" is
  the integer itself at an integer (so `floorFloat(2.0f)` is `2.0f`; no point of `vals` is at an
  integer); "the smallest positive finite value" (1603-1604) counts subnormal data [R].
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

theorem hk_add (vs : List GroundTerm) : hook floatAdd vs =
    some (flOr (fl2 KFloat.sum?) (tfl2 fun p e => KFloat.sumBy (KFloat.tnNearest? p e)) vs) :=
  hook_at rfl vs
theorem hk_sub (vs : List GroundTerm) : hook floatSub vs =
    some (flOr (fl2 KFloat.diff?) (tfl2 fun p e => KFloat.diffBy (KFloat.tnNearest? p e)) vs) :=
  hook_at rfl vs
theorem hk_mul (vs : List GroundTerm) : hook floatMul vs =
    some (flOr (fl2 KFloat.prod?) (tfl2 fun p e => KFloat.prodBy (KFloat.tnNearest? p e)) vs) :=
  hook_at rfl vs
theorem hk_div (vs : List GroundTerm) : hook floatDiv vs =
    some (flOr (fl2 KFloat.quot?) (tfl2 KFloat.tnQuot?) vs) :=
  hook_at rfl vs
theorem hk_rem (vs : List GroundTerm) : hook floatRem vs =
    some (flOr (fl2 KFloat.remainder) (tfl2 fun p e => KFloat.remainderBy (KFloat.tnHeld? p e)) vs) :=
  hook_at rfl vs
theorem hk_neg (vs : List GroundTerm) :
    hook floatNeg vs = some (flOr (fl1 fun _ => KFloat.neg?) (tfl1 fun _ _ => KFloat.neg?) vs) := hook_at rfl vs
theorem hk_abs (vs : List GroundTerm) :
    hook floatAbs vs = some (flOr (fl1 fun _ => KFloat.abs?) (tfl1 fun _ _ => KFloat.abs?) vs) := hook_at rfl vs
theorem hk_floor (vs : List GroundTerm) :
    hook floatFloor vs = some (flOr (fl1 fun s => KFloat.roundToIntegral s .down)
      (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .down) vs) := hook_at rfl vs
theorem hk_ceil (vs : List GroundTerm) :
    hook floatCeil vs = some (flOr (fl1 fun s => KFloat.roundToIntegral s .up)
      (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .up) vs) := hook_at rfl vs
theorem hk_trunc (vs : List GroundTerm) :
    hook floatTrunc vs = some (flOr (fl1 fun s => KFloat.roundToIntegral s .zero)
      (tfl1 fun p e => KFloat.roundToIntegralBy (KFloat.tnHeld? p e) .zero) vs) := hook_at rfl vs
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
theorem hk_round (vs : List GroundTerm) : hook floatRound vs = some (flOr (flTo KFloat.convertFormat) tflTo vs) :=
  hook_at rfl vs
theorem hk_ofInt (vs : List GroundTerm) : hook int2Float vs = some (flOr flOfInt tflOfInt vs) := hook_at rfl vs
theorem hk_max (vs : List GroundTerm) : hook floatMaxValue vs =
    some (flOr (flAt KFloat.maxValue) (tflAt KFloat.tnMax?) vs) :=
  hook_at rfl vs
theorem hk_min (vs : List GroundTerm) : hook floatMinValue vs =
    some (flOr (flAt KFloat.minValue) (tflAt KFloat.tnMin?) vs) :=
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

theorem fl1_none (op : Float.Model.Format → Float.Model.UnpackedFloat → Option Float.Model.UnpackedFloat)
    (p e b : Nat) : fl1 op [fv p e b] = none ↔
      ∀ sp, KFloat.spec? p e = some sp → op sp (KFloat.unpackBits sp b) = none := by
  simp only [fl1, asFloat_fv]
  cases KFloat.spec? p e <;> simp

/-- **A Float literal has a datum (`asDatum`) at every format**: none exactly at a precision or
exponent bits of 0, which names no format (`KFloat.ok` holds at none of its encodings). -/
theorem asDatum_none (p e b : Nat) : asDatum (fv p e b) = none ↔ (p = 0 ∨ e = 0) := by
  have h0 : asDatum (fv p e b) = (match KFloat.spec? p e with
      | some sp => some (KFloat.unpackBits sp b)
      | none => if KFloat.tnFormat p e = true then some (KFloat.tnUnpack p e b) else none) := rfl
  rw [h0]
  split
  · rename_i sp hs
    have := spec_pos hs
    exact ⟨fun hx => (by cases hx), fun hx => (by omega)⟩
  · rename_i hs
    have hs' := (spec_none p e).mp hs
    by_cases h : KFloat.tnFormat p e = true
    · rw [if_pos h]
      simp only [KFloat.tnFormat, decide_eq_true_eq] at h
      exact ⟨fun hx => (by cases hx), fun hx => (by omega)⟩
    · rw [if_neg h]
      simp only [KFloat.tnFormat, decide_eq_true_eq] at h
      exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem flTest_none (t : Float.Model.UnpackedFloat → Bool) (p e b : Nat) :
    flTest t [fv p e b] = none ↔ asDatum (fv p e b) = none := by
  simp only [flTest]
  cases asDatum (fv p e b) <;> simp

theorem fl2_none
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Option Float.Model.UnpackedFloat)
    (p e b p' e' b' : Nat) : fl2 op [fv p e b, fv p' e' b'] = none ↔
      (KFloat.spec? p e = none ∨ KFloat.spec? p' e' = none ∨ ¬(p = p' ∧ e = e') ∨
        ∀ sp, KFloat.spec? p e = some sp → op sp (KFloat.unpackBits sp b) (KFloat.unpackBits sp b') = none) := by
  simp only [fl2, asFloat_fv]
  cases hs : KFloat.spec? p e with
  | none => simp
  | some sp =>
    cases hs' : KFloat.spec? p' e' with
    | none => simp
    | some sp' =>
      simp only [Option.map_some, Option.bind_some]
      by_cases hpe : p = p' ∧ e = e'
      · obtain ⟨rfl, rfl⟩ := hpe
        rw [hs] at hs'; cases hs'
        simp
      · simp [hpe]

theorem flCmp_none (t : Option Ordering → Bool) (p e b p' e' b' : Nat) :
    flCmp t [fv p e b, fv p' e' b'] = none ↔ (asDatum (fv p e b) = none ∨ asDatum (fv p' e' b') = none) := by
  simp only [flCmp]
  cases asDatum (fv p e b) <;> cases asDatum (fv p' e' b') <;> simp

theorem flAt_none (op : Float.Model.Format → Float.Model.UnpackedFloat) (x y : Int) :
    flAt op [int x, int y] = none ↔ KFloat.spec? x.toNat y.toNat = none := by
  simp only [flAt, asInt_int, Option.bind_some]
  cases KFloat.spec? x.toNat y.toNat <;> simp

theorem flTo_none (op : Float.Model.Format → Float.Model.UnpackedFloat → Option Float.Model.UnpackedFloat)
    (p e b : Nat) (x y : Int) : flTo op [fv p e b, int x, int y] = none ↔
      (KFloat.spec? p e = none ∨ KFloat.spec? x.toNat y.toNat = none ∨
        ∀ sp sq, KFloat.spec? p e = some sp → KFloat.spec? x.toNat y.toNat = some sq →
          op sq (KFloat.unpackBits sp b) = none) := by
  simp only [flTo, asFloat_fv, asInt_int, Option.bind_some]
  cases KFloat.spec? p e <;> cases KFloat.spec? x.toNat y.toNat <;> simp

theorem flOfInt_none (n x y : Int) :
    flOfInt [int n, int x, int y] = none ↔
      (KFloat.spec? x.toNat y.toNat = none ∨
        ∀ sq, KFloat.spec? x.toNat y.toNat = some sq → KFloat.ofInt? sq n = none) := by
  simp only [flOfInt, asInt_int, Option.bind_some]
  cases KFloat.spec? x.toNat y.toNat <;> simp

/-! ### At the formats `thinAt` names (`thinHooks`) -/

theorem flOr_none {f g : List GroundTerm → Option GroundTerm} {vs : List GroundTerm} :
    flOr f g vs = none ↔ (f vs = none ∧ g vs = none) := by
  unfold flOr; split <;> simp_all

theorem flOr_some {f g : List GroundTerm → Option GroundTerm} {vs : List GroundTerm} {v : GroundTerm}
    (h : flOr f g vs = some v) : f vs = some v ∨ g vs = some v := by
  unfold flOr at h; split at h
  · rename_i w hw; cases h; exact Or.inl hw
  · exact Or.inr h

/-- `thinAt` at a format given by two Ints: precision 1 or one exponent bit, both positive. -/
theorem thinAt_toNat (x y : Int) : thinAt x.toNat y.toNat = true ↔ (1 ≤ x ∧ 1 ≤ y ∧ (x = 1 ∨ y = 1)) := by
  simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq]; omega

theorem asThin_fv (p e b : Nat) :
    asThin (fv p e b) = if thinAt p e = true then some (p, e, KFloat.tnUnpack p e b) else none := by
  simp [asThin, fv]

theorem tfl1_none (op : Nat → Nat → Float.Model.UnpackedFloat → Option Float.Model.UnpackedFloat)
    (p e b : Nat) : tfl1 op [fv p e b] = none ↔ (thinAt p e = true → op p e (KFloat.tnUnpack p e b) = none) := by
  simp only [tfl1, asThin_fv]
  cases thinAt p e <;> simp

theorem tfl2_none
    (op : Nat → Nat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Option Float.Model.UnpackedFloat)
    (p e b p' e' b' : Nat) : tfl2 op [fv p e b, fv p' e' b'] = none ↔
      (thinAt p e = true → thinAt p' e' = true → p = p' ∧ e = e' →
        op p e (KFloat.tnUnpack p e b) (KFloat.tnUnpack p' e' b') = none) := by
  simp only [tfl2, asThin_fv]
  cases thinAt p e <;> cases thinAt p' e' <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, false_implies,
      true_implies]
  by_cases hpe : p = p' ∧ e = e'
  · simp only [hpe, and_self, ↓reduceIte, Option.map_eq_none_iff, true_implies]
  · simp only [hpe, ↓reduceIte, false_implies]

theorem tflAt_none (op : Nat → Nat → Option Float.Model.UnpackedFloat) (x y : Int) :
    tflAt op [int x, int y] = none ↔ (thinAt x.toNat y.toNat = true → op x.toNat y.toNat = none) := by
  simp only [tflAt, asInt_int, Option.bind_some]
  cases thinAt x.toNat y.toNat <;> simp

theorem tflTo_none (p e b : Nat) (x y : Int) : tflTo [fv p e b, int x, int y] = none ↔
    ∀ u, asDatum (fv p e b) = some u →
      (∀ sq, KFloat.spec? x.toNat y.toNat = some sq → KFloat.convertFormat sq u = none) ∧
      (thinAt x.toNat y.toNat = true → KFloat.convertBy (KFloat.tnHeld? x.toNat y.toNat) u = none) := by
  simp only [tflTo, asInt_int, Option.bind_some]
  cases asDatum (fv p e b) with
  | none => simp
  | some u =>
    simp only [Option.bind_some, Option.some.injEq, forall_eq']
    cases hs : KFloat.spec? x.toNat y.toNat with
    | some sq =>
      have ht : thinAt x.toNat y.toNat = false := by
        cases h : thinAt x.toNat y.toNat
        · rfl
        · rw [thinAt_spec_none h] at hs; cases hs
      simp [ht]
    | none => cases thinAt x.toNat y.toNat <;> simp

theorem tflOfInt_none (n x y : Int) : tflOfInt [int n, int x, int y] = none ↔
    (thinAt x.toNat y.toNat = true → KFloat.ofIntBy (KFloat.tnHeld? x.toNat y.toNat) n = none) := by
  simp only [tflOfInt, asInt_int, Option.bind_some]
  cases thinAt x.toNat y.toNat <;> simp

/-- At a format `thinAt` names other than `(1, 1)`, `maxValueFloat` and `minValueFloat` have a
datum; at `(1, 1)` neither has (`KFloat.tnMax?_one_one`, `KFloat.tnMin?_one_one`). -/
theorem tnMax_thin {p e : Nat} (ht : thinAt p e = true) (h11 : ¬(p = 1 ∧ e = 1)) :
    ∃ m, KFloat.tnMax? p e = some m := by
  simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq] at ht
  by_cases he : 2 ≤ e
  · obtain ⟨_, hm⟩ := KFloat.tnMax?_normal (p := p) (e := e) ht.1 he
    exact ⟨_, hm⟩
  · obtain rfl : e = 1 := by omega
    obtain ⟨_, hm⟩ := KFloat.tnMax?_subnormal (p := p) (by omega)
    exact ⟨_, hm⟩

theorem tnMin_thin {p e : Nat} (ht : thinAt p e = true) (h11 : ¬(p = 1 ∧ e = 1)) :
    ∃ m, KFloat.tnMin? p e = some m := by
  simp only [thinAt, KFloat.tnFormat, decide_eq_true_eq] at ht
  exact ⟨_, KFloat.tnMin?_eq ht.1 ht.2.1 (by omega)⟩

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

open Float.Model in
theorem neg?_none (u : UnpackedFloat) : KFloat.neg? u = none ↔ u = .notANumber := by
  cases u <;> simp [KFloat.neg?]

open Float.Model in
theorem abs?_none (u : UnpackedFloat) : KFloat.abs? u = none ↔ u = .notANumber := by
  cases u <;> simp [KFloat.abs?]

/-- A condition at every model of the format `(p, e)` against the same with "the format has no
model" as an alternative. -/
theorem spec_all_iff {p e : Nat} {P Q : Float.Model.Format → Prop} (h : ∀ sp, P sp ↔ Q sp) :
    (∀ sp, KFloat.spec? p e = some sp → P sp) ↔
      ((p < 2 ∨ e < 2) ∨ ∀ sp, KFloat.spec? p e = some sp → Q sp) := by
  cases hs : KFloat.spec? p e with
  | none => simp only [reduceCtorEq, false_implies, implies_true, true_iff]; exact Or.inl ((spec_none p e).mp hs)
  | some sp =>
    have := spec_pos hs
    simp only [Option.some.injEq, forall_eq', h]
    constructor
    · exact Or.inr
    · rintro (h' | h') <;> first | omega | exact h'

/-- `--Float`, `absFloat`: no value exactly at the NaN, of which the text says nothing (1552-1554,
1578), and at an operand of a format without a model that `thinAt` does not name (the first
conjunct: of a format with a model; the second: of a format `thinAt` names). -/
theorem negAbs_none : ∀ f ∈ [floatNeg, floatAbs], ∀ p e b : Nat, hook f [fv p e b] = some none ↔
    ((p < 2 ∨ e < 2) ∨ ∀ sp, KFloat.spec? p e = some sp → KFloat.unpackBits sp b = .notANumber) ∧
    (thinAt p e = true → KFloat.tnUnpack p e b = .notANumber) := by
  intro f hf p e b
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [hk_neg, Option.some.injEq, flOr_none, fl1_none, tfl1_none]
    exact and_congr (spec_all_iff fun _ => neg?_none _) (imp_congr_right fun _ => neg?_none _)
  · rw [hk_abs, Option.some.injEq, flOr_none, fl1_none, tfl1_none]
    exact and_congr (spec_all_iff fun _ => abs?_none _) (imp_congr_right fun _ => abs?_none _)

/-- The direction of each of the three roundings to an integer. -/
def dirOf (f : Sym) : KFloat.Dir := if f == floatFloor then .down else if f == floatCeil then .up else .zero

/-- `floorFloat`, `ceilFloat`, `truncFloat`: no value exactly at an operand of a format without a model
that `thinAt` does not name and where the rounding to an integer gives none (`KFloat.roundToIntegral`
at a format with a model, `KFloat.roundToIntegralBy` at one `thinAt` names): an infinity or NaN
(`roundToIntegral_special`), a zero result of a nonzero operand, an integer the format does not hold
(points in `pts`). -/
theorem roundings_none : ∀ f ∈ [floatFloor, floatCeil, floatTrunc], ∀ p e b : Nat,
    hook f [fv p e b] = some none ↔ ((p < 2 ∨ e < 2) ∨
      ∀ sp, KFloat.spec? p e = some sp → KFloat.roundToIntegral sp (dirOf f) (KFloat.unpackBits sp b) = none) ∧
      (thinAt p e = true →
        KFloat.roundToIntegralBy (KFloat.tnHeld? p e) (dirOf f) (KFloat.tnUnpack p e b) = none) := by
  intro f hf p e b
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · rw [hk_floor, Option.some.injEq, flOr_none, fl1_none, tfl1_none]
    exact and_congr (spec_all_iff fun _ => Iff.rfl) Iff.rfl
  · rw [hk_ceil, Option.some.injEq, flOr_none, fl1_none, tfl1_none]
    exact and_congr (spec_all_iff fun _ => Iff.rfl) Iff.rfl
  · rw [hk_trunc, Option.some.injEq, flOr_none, fl1_none, tfl1_none]
    exact and_congr (spec_all_iff fun _ => Iff.rfl) Iff.rfl

/-- `isNaN`: a value at every Float literal; none exactly at a precision or exponent bits of 0,
which names no format (`asDatum`). -/
theorem isNaN_none (p e b : Nat) :
    hook floatIsNaN [fv p e b] = some none ↔ (p = 0 ∨ e = 0) := by
  rw [hk_isNaN, Option.some.injEq, flTest_none, asDatum_none]

/-- The five comparisons: a value at two Float literals of any formats; none exactly where an
operand's precision or exponent bits are 0. -/
theorem cmp_none : ∀ f ∈ cmps, ∀ p e b p' e' b' : Nat,
    hook f [fv p e b, fv p' e' b'] = some none ↔ ((p = 0 ∨ e = 0) ∨ (p' = 0 ∨ e' = 0)) := by
  intro f hf p e b p' e' b'
  simp only [cmps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · rw [hk_le, Option.some.injEq, flCmp_none, asDatum_none, asDatum_none]
  · rw [hk_lt, Option.some.injEq, flCmp_none, asDatum_none, asDatum_none]
  · rw [hk_ge, Option.some.injEq, flCmp_none, asDatum_none, asDatum_none]
  · rw [hk_gt, Option.some.injEq, flCmp_none, asDatum_none, asDatum_none]
  · rw [hk_eq, Option.some.injEq, flCmp_none, asDatum_none, asDatum_none]

/-- The datum operation of each arithmetic row. -/
def arithOp (f : Sym) : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
    Option Float.Model.UnpackedFloat :=
  if f == floatAdd then KFloat.sum? else if f == floatSub then KFloat.diff?
  else if f == floatMul then KFloat.prod? else if f == floatDiv then KFloat.quot? else KFloat.remainder

/-- The datum operation of each arithmetic row at a format `thinAt` names (`thinHooks`). -/
def thinArithOp (f : Sym) : Nat → Nat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat →
    Option Float.Model.UnpackedFloat :=
  if f == floatAdd then fun p e => KFloat.sumBy (KFloat.tnNearest? p e)
  else if f == floatSub then fun p e => KFloat.diffBy (KFloat.tnNearest? p e)
  else if f == floatMul then fun p e => KFloat.prodBy (KFloat.tnNearest? p e)
  else if f == floatDiv then KFloat.tnQuot? else fun p e => KFloat.remainderBy (KFloat.tnHeld? p e)

/-- The five arithmetic operations: no value exactly where an operand is of a format without a
model that `thinAt` does not name, the two operands are of two formats, or the datum operation gives
none (the regions of `arith_special`, `div_rem_zero`, `exact_zero_none`, `above_max_none`, and the
points of `pts`; at a format `thinAt` names also an exact result halfway between two data, `thin`). -/
theorem arith_none : ∀ f ∈ arith, ∀ p e b p' e' b' : Nat,
    hook f [fv p e b, fv p' e' b'] = some none ↔
      ((p < 2 ∨ e < 2) ∨ (p' < 2 ∨ e' < 2) ∨ ¬(p = p' ∧ e = e') ∨
        ∀ sp, KFloat.spec? p e = some sp → arithOp f sp (KFloat.unpackBits sp b) (KFloat.unpackBits sp b') = none) ∧
      (thinAt p e = true → thinAt p' e' = true → p = p' ∧ e = e' →
        thinArithOp f p e (KFloat.tnUnpack p e b) (KFloat.tnUnpack p' e' b') = none) := by
  intro f hf p e b p' e' b'
  simp only [arith, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · rw [hk_add, Option.some.injEq, flOr_none, fl2_none, tfl2_none, spec_none, spec_none]; rfl
  · rw [hk_sub, Option.some.injEq, flOr_none, fl2_none, tfl2_none, spec_none, spec_none]; rfl
  · rw [hk_mul, Option.some.injEq, flOr_none, fl2_none, tfl2_none, spec_none, spec_none]; rfl
  · rw [hk_div, Option.some.injEq, flOr_none, fl2_none, tfl2_none, spec_none, spec_none]; rfl
  · rw [hk_rem, Option.some.injEq, flOr_none, fl2_none, tfl2_none, spec_none, spec_none]; rfl

/-- `roundFloat`: no value exactly where the operand has no datum (`asDatum`), the format asked for
has no model and is not one `thinAt` names, or the target format does not hold the operand's value
(`KFloat.convertFormat` at a format with a model, `KFloat.convertBy` at one `thinAt` names: also at an
infinity and NaN, `convert_special`). The first conjunct is Lean core's model on both sides; the
second reads the operand's datum at every format that has one. -/
theorem round_none (p e b : Nat) (x y : Int) : hook floatRound [fv p e b, int x, int y] = some none ↔
    ((p < 2 ∨ e < 2) ∨ (x < 2 ∨ y < 2) ∨
      ∀ sp sq, KFloat.spec? p e = some sp → KFloat.spec? x.toNat y.toNat = some sq →
        KFloat.convertFormat sq (KFloat.unpackBits sp b) = none) ∧
    (∀ u, asDatum (fv p e b) = some u →
      (∀ sq, KFloat.spec? x.toNat y.toNat = some sq → KFloat.convertFormat sq u = none) ∧
      (thinAt x.toNat y.toNat = true → KFloat.convertBy (KFloat.tnHeld? x.toNat y.toNat) u = none)) := by
  rw [hk_round, Option.some.injEq, flOr_none, flTo_none, tflTo_none, spec_none, spec_none]
  have : (x.toNat < 2 ∨ y.toNat < 2) ↔ (x < 2 ∨ y < 2) := by omega
  rw [this]

/-- `Int2Float`: no value exactly at a precision or exponent bits below 2 that `thinAt` does not
name and at an Int the format does not hold (`KFloat.ofInt?`, `KFloat.ofIntBy`). -/
theorem int2Float_none (n x y : Int) : hook int2Float [int n, int x, int y] = some none ↔
    ((x < 2 ∨ y < 2) ∨ ∀ sq, KFloat.spec? x.toNat y.toNat = some sq → KFloat.ofInt? sq n = none) ∧
    (thinAt x.toNat y.toNat = true → KFloat.ofIntBy (KFloat.tnHeld? x.toNat y.toNat) n = none) := by
  rw [hk_ofInt, Option.some.injEq, flOr_none, flOfInt_none, tflOfInt_none, spec_none]
  have : (x.toNat < 2 ∨ y.toNat < 2) ↔ (x < 2 ∨ y < 2) := by omega
  rw [this]

/-! ### The unstated regions, on the data -/

open Float.Model in
theorem exact_none (u : UnpackedFloat) : KFloat.exact u = none ↔ (u = .notANumber ∨ ∃ sg, u = .infinity sg) := by
  cases u <;> simp [KFloat.exact]

open Float.Model in
/-- **An infinite or NaN operand**: none of the five arithmetic operations gives a value (the text
gives none, 1556-1559). -/
theorem arith_special : ∀ f ∈ arith, ∀ (s : Format) (u v : UnpackedFloat),
    (KFloat.exact u = none ∨ KFloat.exact v = none) → arithOp f s u v = none := by
  intro f hf s u v h
  simp only [arith, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · show KFloat.sum? s u v = none
    unfold KFloat.sum?; rcases h with h | h <;> rw [h] <;> simp
  · show KFloat.diff? s u v = none
    unfold KFloat.diff?; rcases h with h | h <;> split <;> simp_all [KFloat.exact]
  · show KFloat.prod? s u v = none
    unfold KFloat.prod?; rcases h with h | h <;> rw [h] <;> simp
  · show KFloat.quot? s u v = none
    unfold KFloat.quot?; rcases h with h | h <;> rw [h] <;> simp
  · show KFloat.remainder s u v = none
    unfold KFloat.remainder; split
    · simp [KFloat.exact] at h
    · rfl

open Float.Model in
/-- **A zero divisor**: `/Float` and `%Float` give no value (the text gives none). -/
theorem div_rem_zero (s : Format) (u : UnpackedFloat) (sg : UnpackedFloat.Sign) :
    KFloat.quot? s u (.zero sg) = none ∧ KFloat.remainder s u (.zero sg) = none := by
  refine ⟨?_, by cases u <;> rfl⟩
  unfold KFloat.quot?
  have h0 : KFloat.exact (.zero sg) = some (0, 0) := rfl
  rw [h0]
  generalize KFloat.exact u = x; generalize KFloat.exact (KFloat.maxValue s) = y
  rcases x with _ | ⟨a, qa⟩ <;> rcases y with _ | ⟨M, Q⟩ <;> simp

open Float.Model in
/-- **A zero exact result** (`+Float`, `-Float`, `*Float`: `KFloat.nearest?` at the value `0·2^q`):
no value; the text gives a zero result no sign but at `0.0 -Float 0.0` (1553). -/
theorem exact_zero_none (s : Format) (q : Int) : KFloat.nearest? s 0 q = none := by
  unfold KFloat.nearest?; split <;> simp

open Float.Model in
/-- **An exact result above the format's largest finite value**: no value (the text does not say
whether an infinity is a value to round to). -/
theorem above_max_none (s : Format) (a q M Q : Int) (hM : KFloat.exact (KFloat.maxValue s) = some (M, Q))
    (h : KFloat.cmpScaled a.natAbs q M Q = .gt) : KFloat.nearest? s a q = none := by
  unfold KFloat.nearest?; rw [hM]; simp [h]

open Float.Model in
/-- `roundFloat`, `floorFloat`, `ceilFloat`, `truncFloat` at an infinity or NaN: no value. -/
theorem convert_special (s : Format) (d : KFloat.Dir) (u : UnpackedFloat) (h : KFloat.exact u = none) :
    KFloat.convertFormat s u = none ∧ KFloat.roundToIntegral s d u = none := by
  rw [exact_none] at h; rcases h with rfl | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩

open Float.Model in
/-- **`roundFloat`, `Int2Float`, the roundings to an integer and `%Float` give only the value the
text describes**: where `KFloat.held?` gives a datum, its value is `a·2^q` itself, never a rounding
of it. -/
theorem held_exact (s : Format) (a q : Int) (r : UnpackedFloat) (h : KFloat.held? s a q = some r) :
    ∃ b e, KFloat.exact r = some (b, e) ∧ KFloat.cmpScaled a q b e = .eq := by
  unfold KFloat.held? at h
  cases hn : KFloat.nearest? s a q with
  | none => rw [hn] at h; cases h
  | some r' =>
    rw [hn] at h
    cases he : KFloat.exact r' with
    | none => simp [Option.filter, he] at h
    | some be =>
      obtain ⟨b, e⟩ := be
      by_cases hc : KFloat.cmpScaled a q b e = .eq
      · simp [Option.filter, he, hc] at h; subst h; exact ⟨b, e, he, hc⟩
      · simp [Option.filter, he, hc] at h

/-- `maxValueFloat`, `minValueFloat`: no value exactly at a precision or exponent bits of 0 or below,
which names no format, and at `(1, 1)`, whose finite data are the two zeros (`thinAt`, where
`KFloat.tnMax?` and `KFloat.tnMin?` have a datum at every other format). -/
theorem at_none : ∀ f ∈ ats, ∀ x y : Int, hook f [int x, int y] = some none ↔
    (x < 1 ∨ y < 1 ∨ (x = 1 ∧ y = 1)) := by
  intro f hf x y
  simp only [ats, List.mem_cons, List.not_mem_nil, or_false] at hf
  have h11 : (x = 1 ∧ y = 1) → x.toNat = 1 ∧ y.toNat = 1 := fun h => by omega
  rcases hf with rfl | rfl
  · rw [hk_max, Option.some.injEq, flOr_none, flAt_none, tflAt_none, spec_none]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : x < 1 ∨ y < 1
      · exact Or.elim hc Or.inl (fun h => Or.inr (Or.inl h))
      · refine Or.inr (Or.inr ?_)
        have ht := (thinAt_toNat x y).mpr (by omega)
        by_cases hn : x = 1 ∧ y = 1
        · exact hn
        · obtain ⟨m, hm⟩ := tnMax_thin ht (by omega)
          rw [h2 ht] at hm; cases hm
    · intro h
      refine ⟨by omega, fun ht => ?_⟩
      have := (thinAt_toNat x y).mp ht
      obtain ⟨hx, hy⟩ := h11 (by omega)
      rw [hx, hy]; exact KFloat.tnMax?_one_one
  · rw [hk_min, Option.some.injEq, flOr_none, flAt_none, tflAt_none, spec_none]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : x < 1 ∨ y < 1
      · exact Or.elim hc Or.inl (fun h => Or.inr (Or.inl h))
      · refine Or.inr (Or.inr ?_)
        have ht := (thinAt_toNat x y).mpr (by omega)
        by_cases hn : x = 1 ∧ y = 1
        · exact hn
        · obtain ⟨m, hm⟩ := tnMin_thin ht (by omega)
          rw [h2 ht] at hm; cases hm
    · intro h
      refine ⟨by omega, fun ht => ?_⟩
      have := (thinAt_toNat x y).mp ht
      obtain ⟨hx, hy⟩ := h11 (by omega)
      rw [hx, hy]; exact KFloat.tnMin?_one_one

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

/-- A literal of the format `thinAt` names given by two Ints has that precision and those exponent
bits. -/
theorem fmt_thin (x y : Int) (ht : thinAt x.toNat y.toNat = true) (w : Float.Model.UnpackedFloat) :
    hook floatPrecision [tnFloatV x.toNat y.toNat w] = some (some (int x)) ∧
      hook floatExponentBits [tnFloatV x.toNat y.toNat w] = some (some (int y)) := by
  obtain ⟨hx, hy, -⟩ := (thinAt_toNat x y).mp ht
  have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
  have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
  have := fmt_at x.toNat y.toNat (KFloat.tnPack x.toNat y.toNat w) (by omega) (by omega)
  rw [hx', hy'] at this
  exact this

/-- **"The resulting `Float` will yield the specified values when calling `precisionFloat` and
`exponentBitsFloat`"** (DOM 1580-1582), at every value of `roundFloat`. -/
theorem round_format (p e b : Nat) (x y : Int) {v : GroundTerm}
    (h : hook floatRound [fv p e b, int x, int y] = some (some v)) :
    hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
  rw [hk_round, Option.some.injEq] at h
  rcases (flOr_some h).symm with h | h
  · simp only [tflTo, asInt_int, Option.bind_some] at h
    obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i sq h2
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hx, hy⟩ := spec_pos h2
      have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
      have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
      have := fmt_floatV x.toNat y.toNat sq w (by omega) (by omega)
      rw [hx', hy'] at this
      exact this
    · split at h
      · rename_i ht
        obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact fmt_thin x y ht w
      · cases h
  simp only [flTo, asFloat_fv, asInt_int, Option.bind_some] at h
  cases h1 : KFloat.spec? p e with
  | none => rw [h1] at h; simp at h
  | some sp =>
    cases h2 : KFloat.spec? x.toNat y.toNat with
    | none => rw [h1, h2] at h; simp at h
    | some sq =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.bind_some] at h
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hx, hy⟩ := spec_pos h2
      have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
      have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
      have := fmt_floatV x.toNat y.toNat sq w (by omega) (by omega)
      rw [hx', hy'] at this
      exact this

/-- The same of `Int2Float` ("with the specified precision and exponent range", DOM 1653-1654). -/
theorem int2Float_format (n x y : Int) {v : GroundTerm}
    (h : hook int2Float [int n, int x, int y] = some (some v)) :
    hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
  rw [hk_ofInt, Option.some.injEq] at h
  rcases (flOr_some h).symm with h | h
  · simp only [tflOfInt, asInt_int, Option.bind_some] at h
    split at h
    · rename_i ht
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact fmt_thin x y ht w
    · cases h
  simp only [flOfInt, asInt_int, Option.bind_some] at h
  cases h2 : KFloat.spec? x.toNat y.toNat with
  | none => rw [h2] at h; simp at h
  | some sq =>
    rw [h2] at h
    simp only [Option.bind_some] at h
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hx, hy⟩ := spec_pos h2
    have hx' : (x.toNat : Int) = x := Int.toNat_of_nonneg (by omega)
    have hy' : (y.toNat : Int) = y := Int.toNat_of_nonneg (by omega)
    have := fmt_floatV x.toNat y.toNat sq w (by omega) (by omega)
    rw [hx', hy'] at this
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
  have keyT : ∀ (op : Nat → Nat → Option Float.Model.UnpackedFloat) (x y : Int) {v : GroundTerm},
      tflAt op [int x, int y] = some v →
      hook floatPrecision [v] = some (some (int x)) ∧ hook floatExponentBits [v] = some (some (int y)) := by
    intro op x y v h
    simp only [tflAt, asInt_int, Option.bind_some] at h
    split at h
    · rename_i ht
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact fmt_thin x y ht w
    · cases h
  intro f hf x y v h
  simp only [ats, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rw [hk_max, Option.some.injEq] at h
    rcases flOr_some h with h | h
    · exact key _ x y h
    · exact keyT _ x y h
  · rw [hk_min, Option.some.injEq] at h
    rcases flOr_some h with h | h
    · exact key _ x y h
    · exact keyT _ x y h

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
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

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

[R] The encoding of a datum of `p24x8`, IEEE 754 binary32 (DOM 1488-1489; the interchange
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

/-- Literals whose datum the prose does not state (finding 2): `16777217.0f`, 2^24 + 1, halfway
between 2^24 and 2^24 + 2, the data of binary32 there; `1e39f`, above its largest finite datum
(about 3.4 × 10^38); `1e-46f`, nonzero and nearer to zero than to its smallest positive datum
2^-149 (about 1.4 × 10^-45). -/
def litsRefused : List String := ["16777217.0f", "1e39f", "1e-46f", "-1e39f"]

/-- **The reader refuses each.** -/
theorem lits_refused : litsRefused.all (fun l => (Parse.floatLit? l).isNone) = true := by
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
- `*Float` [P]: 2 × 3 = 6 (1556). `/Float` [P]: 3 / 2 = 1.5.
- `%Float` [P] (1557-1558): 5 / 3 = 1.66…, the nearest integer is 2, and 5 - 3 × 2 = -1.
- `absFloat`: [P] (1578) of `-1.0f` it is `1.0f`; [P] of `-0.0f` it is `0.0f` (reading: the prose
  calls the two zeros positive and negative, 1553-1554, and the absolute value of a negative datum
  is the positive one of its magnitude).
- `floorFloat` [P] (1583-1584): the next lowest integer from 2.5 is 2, from -2.5 it is -3.
  `ceilFloat` [P] (1585-1586): 3 and -2. `truncFloat` [P] (1587-1588, "in the direction of zero"): 2
  and -2.
- `roundFloat` [P] (1579-1580): 1.5 of `p53x11` to precision 24 and exponent bits 8 is `1.5f`, which
  `p24x8` holds exactly.
- `Int2Float` [P] (1653-1654): 3 at 24, 8 is `3.0f`; -2 at 53, 11 is `-2.0`.
- `maxValueFloat`, `minValueFloat` (1601-1604): [P] the largest finite and the smallest positive
  datum of the format; [R] which data those are in binary32 (`max32`, `min32`).
- The comparisons. [P] "`0.0 ==Float -0.0` is also true" (1638); "`NaN` compares unequal to all
  values, including itself" (1637), so `NaN ==Float NaN` is false; 1 < 2, not 2 < 1; 1 ≤ 1, not 2 ≤ 1;
  2 > 1, not 1 > 1; 1 ≥ 1, not 1 ≥ 2 (1631-1632). [P] a NaN, which is no number (1541), stands in no
  order, so `NaN <Float 1.0f` and `NaN >=Float 1.0f` are false (1673, an equation of the module,
  reads both orders as false at a NaN); `-0.0 <=Float 0.0` is true and `-0.0 <Float 0.0` false (the
  zeros are equal, 1638). [P] two formats (1631-1632: a float against another float, a Bool
  result): `1.0 ==Float 1.0f` and `1.0f <Float 1.5` are true. -/
def vals : List Pt :=
  [⟨floatPrecision, [one], int 24⟩, ⟨floatPrecision, [one64], int 53⟩,
   ⟨floatExponentBits, [one], int 8⟩, ⟨floatExponentBits, [one64], int 11⟩,
   ⟨floatIsNaN, [nan], bool true⟩, ⟨floatIsNaN, [one], bool false⟩, ⟨floatIsNaN, [inf], bool false⟩,
   ⟨floatNeg, [z64], nz64⟩, ⟨floatNeg, [one], mone⟩,
   ⟨floatSub, [z64, z64], z64⟩, ⟨floatSub, [three, one], two⟩,
   ⟨floatAdd, [one, two], three⟩, ⟨floatAdd, [one, tiny], one⟩, ⟨floatAdd, [onePlus, tiny], onePlus2⟩,
   ⟨floatMul, [two, three], six⟩,
   ⟨floatDiv, [three, two], oneHalf⟩,
   ⟨floatRem, [five, three], mone⟩,
   ⟨floatAbs, [mone], one⟩, ⟨floatAbs, [nz], z⟩,
   ⟨floatFloor, [twoHalf], two⟩, ⟨floatFloor, [mtwoHalf], mthree⟩,
   ⟨floatCeil, [twoHalf], three⟩, ⟨floatCeil, [mtwoHalf], mtwo⟩,
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
   ⟨floatLe, [nz, z], bool true⟩, ⟨floatLt, [nz, z], bool false⟩,
   ⟨floatEq, [one64, one], bool true⟩, ⟨floatLt, [one, oneHalf64], bool true⟩]

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

/-! ## Statement 2: a point of each row of the unstated parts -/

/-- **Two formats**: the five arithmetic operations at `1.0` (`p53x11`) and `1.0f` (`p24x8`).
**No format** (DOM 1475, "positive"): `roundFloat(1.0, 0, 8)` and `(1.0, 24, -1)`,
`Int2Float(1, 24, 0)`, `maxValueFloat(0, 8)`, `minValueFloat(53, 0)`.
**Where the text states no value at a format with a model** (findings 2, 3, 5): `--Float` and
`absFloat` at `NaNf`; `1.0f /Float 0.0f`, `0.0f /Float 0.0f`, `1.0f %Float 0.0f` (a zero divisor);
`Infinityf +Float 1.0f`, `NaNf *Float 1.0f`, `Infinityf -Float 1.0f`, `Infinityf %Float 1.0f` (an
infinite or NaN operand); `1.0f +Float -1.0f`, `0.0f *Float 3.0f`, `-0.0f -Float -0.0f` (a zero
result whose sign the text does not give); `max32 +Float max32`, `max32 *Float 2.0f` (above the
largest finite datum); `5.0f %Float 2.0f` (2.5 is halfway between two integers);
`floorFloat(0.5f)`, `ceilFloat(-0.5f)`, `truncFloat(0.5f)` (a zero result of a nonzero operand);
`floorFloat`, `ceilFloat`, `truncFloat` at `Infinityf` and `NaNf`; `roundFloat(onePlus, 2, 8)` (an
inexact value) and `roundFloat(Infinityf, 53, 11)`; `Int2Float(2^24 + 1, 24, 8)` (an Int the format
does not hold). The value `v` has the result sort. -/
def pts : List Pt :=
  [⟨floatAdd, [one64, one], z64⟩, ⟨floatSub, [one64, one], z64⟩, ⟨floatMul, [one64, one], z64⟩,
   ⟨floatDiv, [one64, one], z64⟩, ⟨floatRem, [one64, one], z64⟩,
   ⟨floatRound, [one64, int 0, int 8], z64⟩, ⟨floatRound, [one64, int 24, int (-1)], z64⟩,
   ⟨int2Float, [int 1, int 24, int 0], z64⟩,
   ⟨floatMaxValue, [int 0, int 8], z64⟩, ⟨floatMinValue, [int 53, int 0], z64⟩,
   ⟨floatNeg, [nan], z64⟩, ⟨floatAbs, [nan], z64⟩,
   ⟨floatDiv, [one, z], z64⟩, ⟨floatDiv, [z, z], z64⟩, ⟨floatRem, [one, z], z64⟩,
   ⟨floatAdd, [inf, one], z64⟩, ⟨floatMul, [nan, one], z64⟩, ⟨floatSub, [inf, one], z64⟩,
   ⟨floatRem, [inf, one], z64⟩,
   ⟨floatAdd, [one, mone], z64⟩, ⟨floatMul, [z, three], z64⟩, ⟨floatSub, [nz, nz], z64⟩,
   ⟨floatAdd, [max32, max32], z64⟩, ⟨floatMul, [max32, two], z64⟩,
   ⟨floatRem, [five, two], z64⟩,
   ⟨floatFloor, [half], z64⟩, ⟨floatCeil, [mhalf], z64⟩, ⟨floatTrunc, [half], z64⟩,
   ⟨floatFloor, [inf], z64⟩, ⟨floatCeil, [nan], z64⟩, ⟨floatTrunc, [minf], z64⟩,
   ⟨floatRound, [onePlus, int 2, int 8], z64⟩, ⟨floatRound, [inf, int 53, int 11], z64⟩,
   ⟨int2Float, [int 16777217, int 24, int 8], z64⟩]

/-- Every row with an unstated region has a point, and every point is of a key. -/
theorem pts_keys : ((arith ++ unary ++ [floatRound, int2Float] ++ ats).all (fun f => pts.any (·.f == f)) &&
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

/-- Values of the thin format `p1x8` [R]: sign bit 8, exponent field the 8 bits below it (bias 127),
no significand field, so a datum is ±2^x, ±0 or ±∞. `1.0p1x8` (field 127, 2^0), `-1.0p1x8`, `2.0p1x8`
(field 128), `4.0p1x8` (field 129), `0.5p1x8` (field 126), `Infinityp1x8` (field 255), the largest
finite datum 2^127 (field 254) and the smallest positive one 2^-126 (field 1: with no significand
field there is no subnormal datum), and its NaN, the code 2^9 (`KFloat.thinOK`). Of `p2x1` (one
exponent bit, precision 2: sign bit 2, the exponent bit, one significand bit; bias 0, so its
subnormal data are f·2^0): `1.0p2x1` (the significand field 1, the largest and the smallest positive
datum), `-1.0p2x1`, `0.0p2x1`, `Infinityp2x1` (the exponent bit set). Of `p1x1` (no finite datum but
the zeros): `0.0p1x1` (code 0), `Infinityp1x1` (code 1), `NaNp1x1` (code 4). -/
def t18 : GroundTerm := fv 1 8 127
def mt18 : GroundTerm := fv 1 8 (256 + 127)
def two18 : GroundTerm := fv 1 8 128
def four18 : GroundTerm := fv 1 8 129
def half18 : GroundTerm := fv 1 8 126
def inf18 : GroundTerm := fv 1 8 255
def max18 : GroundTerm := fv 1 8 254
def min18 : GroundTerm := fv 1 8 1
def nan18 : GroundTerm := fv 1 8 512
def t21 : GroundTerm := fv 2 1 1
def mt21 : GroundTerm := fv 2 1 5
def z21 : GroundTerm := fv 2 1 0
def inf21 : GroundTerm := fv 2 1 2
def z11 : GroundTerm := fv 1 1 0
def inf11 : GroundTerm := fv 1 1 1
def nan11 : GroundTerm := fv 1 1 4
def z18 : GroundTerm := fv 1 8 0

/-- **At a thin format the operations have the values the prose states**
(finding 1; [P] and [A] as in `vals`, the data [R]): `isNaN(1.0p1x8)` false, `isNaN(NaNp1x8)` true,
`isNaN(Infinityp1x8)` false; `1.0p1x8 ==Float 1.0` true, `2.0p1x8 ==Float 2.0f` true,
`-1.0p1x8 <Float 1.0p1x8` true, `1.0p1x8 <=Float 1.0f` true, `2.0p1x8 >Float 1.5` true,
`Infinityp1x8 >=Float max32` true, `NaNp1x8 ==Float NaNp1x8` false, `NaNp1x8 <Float 1.0p1x8` false;
`--Float 1.0p1x8` is `-1.0p1x8`, `absFloat(-1.0p1x8)` is `1.0p1x8`; 1 + 1 = 2, 2 - 1 = 1, 2 × 2 = 4,
1 / 2 = 0.5, all data of `p1x8`; `1.0p1x8 %Float 4.0p1x8`: 1 / 4 = 0.25, the nearest integer is 0, and
1 - 4 × 0 = 1; `floorFloat(1.0p1x8)` is itself, `ceilFloat(0.5p1x8)` is 1, `truncFloat(2.0p1x8)` is
itself; `roundFloat(1.0, 1, 8)` is `1.0p1x8` and `roundFloat(1.0p1x8, 24, 8)` is `1.0f`, values the
target holds; `Int2Float(2, 1, 8)` is `2.0p1x8`; `maxValueFloat(1, 8)` and `minValueFloat(1, 8)` are
the largest finite and the smallest positive datum. **At one exponent bit too** (the data R read at
one exponent bit, rulings section 7 R1): `isNaN(1.0p2x1)` false, `1.0p2x1 ==Float 1.0` true,
`Infinityp2x1 >Float 1.0p2x1` true, `NaNp1x1 ==Float NaNp1x1` false, `0.0p1x1 ==Float -0.0`
true; `--Float 1.0p2x1` is `-1.0p2x1`, `absFloat(-1.0p2x1)` is `1.0p2x1`; 1 × 1 = 1, 1 / 1 = 1;
`floorFloat(1.0p2x1)` is itself; `roundFloat(1.0, 2, 1)` is `1.0p2x1`, `roundFloat(1.0p2x1, 24, 8)`
is `1.0f`; `Int2Float(1, 2, 1)` is `1.0p2x1` and `Int2Float(0, 1, 1)` is `0.0p1x1`;
`maxValueFloat(2, 1)` and `minValueFloat(2, 1)` are both `1.0p2x1`, the one positive finite datum. -/
def thinVals : List Pt :=
  [⟨floatIsNaN, [t18], bool false⟩, ⟨floatIsNaN, [nan18], bool true⟩, ⟨floatIsNaN, [inf18], bool false⟩,
   ⟨floatEq, [t18, one64], bool true⟩, ⟨floatEq, [two18, two], bool true⟩, ⟨floatLt, [mt18, t18], bool true⟩,
   ⟨floatLe, [t18, one], bool true⟩, ⟨floatGt, [two18, oneHalf64], bool true⟩,
   ⟨floatGe, [inf18, max32], bool true⟩, ⟨floatEq, [nan18, nan18], bool false⟩,
   ⟨floatLt, [nan18, t18], bool false⟩,
   ⟨floatNeg, [t18], mt18⟩, ⟨floatAbs, [mt18], t18⟩,
   ⟨floatAdd, [t18, t18], two18⟩, ⟨floatSub, [two18, t18], t18⟩, ⟨floatMul, [two18, two18], four18⟩,
   ⟨floatDiv, [t18, two18], half18⟩, ⟨floatRem, [t18, four18], t18⟩,
   ⟨floatFloor, [t18], t18⟩, ⟨floatCeil, [half18], t18⟩, ⟨floatTrunc, [two18], two18⟩,
   ⟨floatRound, [one64, int 1, int 8], t18⟩, ⟨floatRound, [t18, int 24, int 8], one⟩,
   ⟨int2Float, [int 2, int 1, int 8], two18⟩,
   ⟨floatMaxValue, [int 1, int 8], max18⟩, ⟨floatMinValue, [int 1, int 8], min18⟩,
   ⟨floatIsNaN, [t21], bool false⟩, ⟨floatEq, [t21, one64], bool true⟩, ⟨floatGt, [inf21, t21], bool true⟩,
   ⟨floatEq, [nan11, nan11], bool false⟩, ⟨floatEq, [z11, nz64], bool true⟩,
   ⟨floatNeg, [t21], mt21⟩, ⟨floatAbs, [mt21], t21⟩,
   ⟨floatMul, [t21, t21], t21⟩, ⟨floatDiv, [t21, t21], t21⟩, ⟨floatFloor, [t21], t21⟩,
   ⟨floatRound, [one64, int 2, int 1], t21⟩, ⟨floatRound, [t21, int 24, int 8], one⟩,
   ⟨int2Float, [int 1, int 2, int 1], t21⟩, ⟨int2Float, [int 0, int 1, int 1], z11⟩,
   ⟨floatMaxValue, [int 2, int 1], t21⟩, ⟨floatMinValue, [int 2, int 1], t21⟩]

theorem thinVals_ok : thinVals.all (fun p => decide (sig p.f ∈ hookSigs) && (sig p.f).name == p.f &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some (some p.v)) = true := by
  decide +kernel

/-- Γ states each, under every interpretation. -/
theorem thinVals_gamma : ∀ p ∈ thinVals, ∀ H : HookParams,
    Γ (c.withHooks H) (appP (c.withHooks H) (sig p.f) p.vs ≡ den (c.withHooks H) p.v) := by
  intro p hp H
  have h := List.all_eq_true.mp thinVals_ok p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hname⟩, hvs⟩, hh⟩ := h
  exact gamma_val (c.withHooks H) hk (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)
    (by rw [hname]; exact hh)

/-- The keys with a silent point at a Float literal: all but the five comparisons and `isNaN`, which
have a value at every one (`cmp_none`, `isNaN_none`). -/
def thinKeys : List Sym := unary ++ arith ++ [floatRound, int2Float] ++ ats

/-- A point of each of `thinKeys` at a thin format where `hook` gives no value, the region of a format
with a model or one particular to a field of 1: `--Float`, `absFloat`, `ceilFloat` at `NaNp1x1`,
`floorFloat` at `Infinityp1x1`, `truncFloat` at `Infinityp1x8`; `1.0p1x8 +Float 2.0p1x8`, exactly 3,
halfway between the data 2 and 4 (finding 1: a tie at precision 1); `1.0p2x1 -Float -1.0p2x1`, 2,
above the largest finite datum 1; `max18 *Float 2.0p1x8`, above it; `1.0p2x1 /Float 0.0p2x1` and
`1.0p1x8 %Float 0.0p1x8`, a zero divisor; `roundFloat(1.0, 1, 1)` and `roundFloat(1.5, 2, 1)`,
`Int2Float(3, 1, 8)` and `Int2Float(1, 1, 1)`, values the format does not hold;
`maxValueFloat(1, 1)` and `minValueFloat(1, 1)`, at a format whose finite data are the two zeros. -/
def thin : List Pt :=
  [⟨floatNeg, [nan11], z64⟩, ⟨floatAbs, [nan11], z64⟩, ⟨floatFloor, [inf11], z64⟩, ⟨floatCeil, [nan11], z64⟩,
   ⟨floatTrunc, [inf18], z64⟩,
   ⟨floatAdd, [t18, two18], z64⟩, ⟨floatSub, [t21, mt21], z64⟩, ⟨floatMul, [max18, two18], z64⟩,
   ⟨floatDiv, [t21, z21], z64⟩, ⟨floatRem, [t18, z18], z64⟩,
   ⟨floatRound, [one64, int 1, int 1], z64⟩, ⟨floatRound, [oneHalf64, int 2, int 1], z64⟩,
   ⟨int2Float, [int 3, int 1, int 8], z64⟩, ⟨int2Float, [int 1, int 1, int 1], z64⟩,
   ⟨floatMaxValue, [int 1, int 1], z64⟩, ⟨floatMinValue, [int 1, int 1], z64⟩]

theorem thin_keys : (thinKeys.all (fun f => thin.any (·.f == f)) && thin.all (fun p => thinKeys.contains p.f)) = true := by
  decide +kernel

theorem thin_ok : thin.all (fun p => lookupSig hookSigs p.f == some (sig p.f) &&
    c.sortsOf p.vs == some (sig p.f).args && hook p.f p.vs == some none && silent p.f p.vs &&
    c.sortOf p.v == some (sig p.f).result) = true := by
  decide +kernel

/-- **At a thin format where `hook` gives no value Γ determines none of the operations of
`thinKeys`** (a fact about Γ: the text states no value at these points, as at the same region of a
format with a model). -/
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
#print axioms negAbs_none
#print axioms roundings_none
#print axioms arith_special
#print axioms div_rem_zero
#print axioms exact_zero_none
#print axioms above_max_none
#print axioms convert_special
#print axioms held_exact
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
#print axioms lits_refused
#print axioms vals_gamma
#print axioms pts_undetermined
#print axioms thin_undetermined
#print axioms thinVals_gamma
#print axioms thin_fmt

end KCore.HooksFloatTest
