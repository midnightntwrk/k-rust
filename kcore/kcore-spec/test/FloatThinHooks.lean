/-
  The combinators of the formats with a field of 1 (KcoreSpec/Hooks.lean, `thinHooks`), at the
  formats `thinAt` names (here `p1x3`), each value decided by the kernel.
  These are the values of `thinHooks`' entries; `floatHooks` pairs each with its entry of a format
  with a model by `flOr`, so they are `hook`'s values at these formats.

  `p1x3` (bias 3): the encoding `8·s + x`, the field `x` from 1 to 6 is `±2^(x − 3)` (0.25, 0.5, 1,
  2, 4, 8), 0 a zero, 7 an infinity, 16 the NaN. At precision 1 a significand is the one digit 1, so
  a value halfway between two powers of two (a tie) has no rounding.
-/
import KcoreSpec.SubjectReduction
import KcoreSpec.Collections

open KCore Float.Model

namespace KCore.FloatThinHooksTest

/-- A Float literal. -/
def fv (p e b : Nat) : GroundTerm := .dv Srt.float (.float p e b)
/-- A literal of `p1x3`. -/
abbrev t (b : Nat) : GroundTerm := fv 1 3 b
/-- A literal of `p53x11` (binary64). -/
abbrev d (b : Nat) : GroundTerm := fv 53 11 b

/-- `thinHooks`' entry for `f`, applied to `vs`: `none` where `f` has no entry. -/
def th (f : Sym) (vs : List GroundTerm) : Option (Option GroundTerm) :=
  (thinHooks.find? (·.1 == f)).map (·.2 vs)

/-! ## Arithmetic: the exact result rounded to the nearest datum -/

/-- 2 + 2 = 4; 4 − 2 = 2; 2 · 4 = 8; 1 / 4 = 0.25; the remainder of 1 by 4 is 1. -/
example : [th floatAdd [t 4, t 4], th floatSub [t 5, t 4], th floatMul [t 4, t 5], th floatDiv [t 3, t 5],
    th floatRem [t 3, t 5]] = [some (some (t 5)), some (some (t 4)), some (some (t 6)), some (some (t 1)),
    some (some (t 3))] := by decide +kernel

/-- No value: 1 + 2 = 3 is a tie between 2 and 4; 4 · 4 = 16 is above the largest finite datum 8;
1 / 0; two formats. -/
example : [th floatAdd [t 3, t 4], th floatMul [t 5, t 5], th floatDiv [t 3, t 0],
    th floatAdd [t 4, fv 1 4 4]] = [some none, some none, some none, some none] := by decide +kernel

/-! ## One operand -/

/-- `--Float 2` is −2; `absFloat −8` is 8; `ceilFloat 0.5` is 1; `truncFloat −1` is −1;
`sqrtFloat 4` is 2. -/
example : [th floatNeg [t 4], th floatAbs [t 14], th floatCeil [t 2], th floatTrunc [t 11],
    th floatSqrt [t 5]] = [some (some (t 12)), some (some (t 6)), some (some (t 3)), some (some (t 11)),
    some (some (t 4))] := by decide +kernel

/-- No value: `--Float` of the NaN; `floorFloat 0.5`, a zero result of a nonzero operand;
`sqrtFloat 2`, which no datum is. -/
example : [th floatNeg [t 16], th floatFloor [t 2], th floatSqrt [t 4]] = [some none, some none, some none] := by
  decide +kernel

/-! ## `isInfinite`, the formats' extreme data, conversions -/

/-- `isInfinite` of +∞ and of 8. -/
example : th floatIsInfinite [t 7] = some (some (bool true)) ∧ th floatIsInfinite [t 6] = some (some (bool false)) := by
  decide +kernel

/-- `maxValueFloat(1, 3)` is 8 and `minValueFloat(1, 3)` 0.25; `maxValueFloat(1, 8)` is `2^127`
(exponent field 254); `maxValueFloat(1, 1)` has none (the format's finite data are its zeros). -/
example : [th floatMaxValue [int 1, int 3], th floatMinValue [int 1, int 3], th floatMaxValue [int 1, int 8],
    th floatMaxValue [int 1, int 1]] = [some (some (t 6)), some (some (t 1)), some (some (fv 1 8 254)), some none] := by
  decide +kernel

/-- `Int2Float(4, 1, 3)` is 4 and `Int2Float(0, 1, 3)` the positive zero; `Int2Float(3, 1, 3)` has
none (a tie). -/
example : [th int2Float [int 4, int 1, int 3], th int2Float [int 0, int 1, int 3], th int2Float [int 3, int 1, int 3]] =
    [some (some (t 5)), some (some (t 0)), some none] := by decide +kernel

/-- `roundFloat` of the binary64 2.0 to `p1x3` is 2, and of the `p1x3` 4 to binary64 is 4.0. -/
example : th floatRound [d 4611686018427387904, int 1, int 3] = some (some (t 4)) ∧
    th floatRound [t 5, int 53, int 11] = some (some (d 4616189618054758400)) := by decide +kernel

/-! ## At a format with a model the combinators of one format have no value (`asThin_none_of_asFloat`) -/

example : asThin (d 4611686018427387904) = none :=
  asThin_none_of_asFloat (by decide +kernel)
example : th floatAdd [d 4611686018427387904, d 4611686018427387904] = some none ∧
    th floatNeg [d 4611686018427387904] = some none := by decide +kernel

/-! ## `flOr`: an operation at a format with a model, then at a format with a field of 1 -/

/-- At binary64 `fl2 KFloat.sum?` gives 2.0 + 2.0 = 4.0 (`flOr_of_some`); at `p1x3` it has none
and the thin entry gives 4 (`flOr_of_none`). -/
example : flOr (fl2 KFloat.sum?) (tfl2 fun p e => KFloat.sumBy (KFloat.tnNearest? p e))
    [d 4611686018427387904, d 4611686018427387904] = some (d 4616189618054758400) :=
  flOr_of_some (by decide +kernel)
example : flOr (fl2 KFloat.sum?) (tfl2 fun p e => KFloat.sumBy (KFloat.tnNearest? p e)) [t 4, t 4] = some (t 5) := by
  rw [flOr_of_none (by decide +kernel)]; decide +kernel

/-- The pairing has the sort of its result (`flOr_sorted`, `fl2_sorted`, `tfl2_sorted`). -/
example (c : Semantics) (ws : List GroundTerm) (v : GroundTerm)
    (h : flOr (fl2 KFloat.sum?) (tfl2 fun p e => KFloat.sumBy (KFloat.tnNearest? p e)) ws = some v) :
    c.sortOf v = some Srt.float :=
  flOr_sorted (fun _ h => fl2_sorted h)
    (fun _ h => tfl2_sorted (fun p e _ _ _ _ _ _ h => KFloat.sumBy_datum (KFloat.tnNearest?_datum' p e) h) h) h

/-- A format `thinAt` names is one with a field of 1 (`thinAt_tnFormat`) and has no model
(`thinAt_spec_none`). -/
example : KFloat.tnFormat 1 3 = true ∧ KFloat.spec? 1 3 = none :=
  ⟨thinAt_tnFormat (by decide), thinAt_spec_none (by decide)⟩

end KCore.FloatThinHooksTest
