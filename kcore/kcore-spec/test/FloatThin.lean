/-
  The model of the formats with a field of 1 (KcoreSpec/FloatThin.lean) at small formats, each
  value decided by the kernel and written as the datum's encoding (`tnPack`).

  `p1x3` (bias 3): sign bit and three exponent bits; the field `x` from 1 to 6 is `2^(x − 3)`, so
  0.25, 0.5, 1, 2, 4, 8; field 7 an infinity; 16 the NaN.
  `p3x1`: sign bit, one exponent bit, two significand bits; the field `f` from 1 to 3 at exponent
  bit 0 is `f·2^(−1)`, so 0.5, 1, 1.5; 4 is +∞; 16 the NaN.
  `p1x1`: 0 and 2 the zeros, 1 and 3 the infinities, 4 the NaN.
-/
import KcoreSpec.FloatThinRound

open KCore.KFloat Float.Model

namespace KCore.FloatThinTest

/-- The encoding of a result in the format `(p, e)`. -/
def enc (p e : Nat) (r : Option UnpackedFloat) : Option Nat := r.map (tnPack p e)

/-- The datum of the encoding `b` of `p1x3`. -/
abbrev a (b : Nat) : UnpackedFloat := tnUnpack 1 3 b
/-- The datum of the encoding `b` of `p3x1`. -/
abbrev s (b : Nat) : UnpackedFloat := tnUnpack 3 1 b

/-! ## Encodings: every encoding of the three formats is read and written back -/

example : (List.range 17).all (fun b => !thinOK 1 3 b || tnPack 1 3 (a b) == b) = true := by decide +kernel
example : (List.range 17).all (fun b => !thinOK 3 1 b || tnPack 3 1 (s b) == b) = true := by decide +kernel
example : (List.range 5).all (fun b => tnPack 1 1 (tnUnpack 1 1 b) == b) = true := by decide +kernel
/-- The exponent field of all ones with a nonzero significand field is no literal (`thinOK`) and
reads as the NaN. -/
example : [5, 6, 7].map (fun b => (thinOK 3 1 b, tnPack 3 1 (s b))) = [(false, 16), (false, 16), (false, 16)] := by
  decide +kernel

/-! ## The largest finite and the smallest positive datum -/

example : enc 1 3 (tnMax? 1 3) = some 6 ∧ enc 1 3 (tnMin? 1 3) = some 1 := by decide +kernel
example : enc 3 1 (tnMax? 3 1) = some 3 ∧ enc 3 1 (tnMin? 3 1) = some 1 := by decide +kernel
example : tnMax? 1 1 = none ∧ tnMin? 1 1 = none := by decide +kernel
/-- `maxValueFloat(1, 8)` is `2^127`: exponent field 254. -/
example : enc 1 8 (tnMax? 1 8) = some 254 := by decide +kernel

/-! ## The rounding at `p1x3` -/

/-- 5 is nearer 4 than 8; 7 is nearer 8; −1.25 is nearer −1; 3/16 is nearer 0.25 than 0. -/
example : [enc 1 3 (tnNearest? 1 3 5 0), enc 1 3 (tnNearest? 1 3 7 0), enc 1 3 (tnNearest? 1 3 (-5) (-2)),
    enc 1 3 (tnNearest? 1 3 3 (-4))] = [some 5, some 6, some 11, some 1] := by decide +kernel
/-- No value: 3 is halfway between 2 and 4, and 1/8 halfway between 0 and 0.25 (a tie at precision
1); 9 is above the largest finite datum; 1/16 rounds to zero; a zero result. -/
example : [tnNearest? 1 3 3 0, tnNearest? 1 3 1 (-3), tnNearest? 1 3 9 0, tnNearest? 1 3 1 (-4),
    tnNearest? 1 3 0 0].map (enc 1 3) = [none, none, none, none, none] := by decide +kernel

/-! ## The rounding at `p3x1` -/

/-- 3/4 is halfway between 0.5 (`f = 1`) and 1 (`f = 2`), and 5/4 between 1 and 1.5 (`f = 3`):
each goes to the even significand, 1. 5/8 is nearer 0.5; 3/2 is held. -/
example : [enc 3 1 (tnNearest? 3 1 3 (-2)), enc 3 1 (tnNearest? 3 1 5 (-2)), enc 3 1 (tnNearest? 3 1 5 (-3)),
    enc 3 1 (tnNearest? 3 1 3 (-1))] = [some 2, some 2, some 1, some 3] := by decide +kernel
/-- No value: 1/4 is halfway between 0 and 0.5 and goes to the even significand 0, a rounding to
zero; 7/4 is above the largest finite datum. -/
example : [enc 3 1 (tnNearest? 3 1 1 (-2)), enc 3 1 (tnNearest? 3 1 7 (-2))] = [none, none] := by decide +kernel

/-! ## No arithmetic result at `p1x1` -/

example : [tnNearest? 1 1 1 0, tnNearest? 1 1 1 (-1), tnHeld? 1 1 1 0].map (enc 1 1) = [none, none, none] := by
  decide +kernel
/-- The operations whose own words give a zero its sign have their value at `(1, 1)` too. -/
example : enc 1 1 (diffBy (tnNearest? 1 1) (tnUnpack 1 1 0) (tnUnpack 1 1 0)) = some 0 ∧
    enc 1 1 (ofIntBy (tnHeld? 1 1) 0) = some 0 ∧
    enc 1 1 (roundToIntegralBy (tnHeld? 1 1) .down (tnUnpack 1 1 2)) = some 2 ∧
    enc 1 1 (convertBy (tnHeld? 1 1) (a 8)) = some 2 := by decide +kernel

/-! ## The operations at `p1x3` and `p3x1` -/

/-- 1 + 1 = 2; 2 · 4 = 8; 1 / 0.5 = 2; 1.5 / 1 = 1.5; 0.5 / 1.5 = 1/3, nearer 0.5 than 0. -/
example : enc 1 3 (sumBy (tnNearest? 1 3) (a 3) (a 3)) = some 4 ∧
    enc 1 3 (prodBy (tnNearest? 1 3) (a 4) (a 5)) = some 6 ∧
    enc 1 3 (tnQuot? 1 3 (a 3) (a 2)) = some 4 ∧
    enc 3 1 (tnQuot? 3 1 (s 3) (s 2)) = some 3 ∧
    enc 3 1 (tnQuot? 3 1 (s 1) (s 3)) = some 1 := by decide +kernel
/-- No value: 4 · 4 is above the largest finite datum; 1 − 1 is a zero the text gives no sign;
1 + 2 = 3 is a tie at precision 1; a division by a zero; an infinite operand. -/
example : [prodBy (tnNearest? 1 3) (a 5) (a 5), diffBy (tnNearest? 1 3) (a 3) (a 3),
    sumBy (tnNearest? 1 3) (a 3) (a 4), tnQuot? 1 3 (a 3) (a 0), sumBy (tnNearest? 1 3) (a 7) (a 3)].map (enc 1 3) =
    [none, none, none, none, none] := by decide +kernel
/-- `0.0 -Float 0.0` is positive zero. -/
example : enc 1 3 (diffBy (tnNearest? 1 3) (a 0) (a 0)) = some 0 := by decide +kernel
/-- `1 %Float 4` is 1 (the quotient 1/4 is nearest 0); `4 %Float 1` is a zero, of no given sign. -/
example : enc 1 3 (remainderBy (tnHeld? 1 3) (a 3) (a 5)) = some 3 ∧
    remainderBy (tnHeld? 1 3) (a 5) (a 3) = none := by decide +kernel
/-- The ceiling of 0.5 is 1, at both formats; the floor of 1.5 is 1; the floor of 0.5 is a zero of
no given sign; the ceiling of 1.5 is 2, which `p3x1` does not hold; a zero is its own rounding. -/
example : enc 1 3 (roundToIntegralBy (tnHeld? 1 3) .up (a 2)) = some 3 ∧
    enc 3 1 (roundToIntegralBy (tnHeld? 3 1) .up (s 1)) = some 2 ∧
    enc 3 1 (roundToIntegralBy (tnHeld? 3 1) .down (s 3)) = some 2 ∧
    roundToIntegralBy (tnHeld? 1 3) .down (a 2) = none ∧
    roundToIntegralBy (tnHeld? 3 1) .up (s 3) = none ∧
    enc 1 3 (roundToIntegralBy (tnHeld? 1 3) .zero (a 8)) = some 8 := by decide +kernel
/-- `roundFloat` between the two formats: 1 is held by both; 1.5 is not a datum of `p1x3`, and 4
none of `p3x1`. -/
example : enc 1 3 (convertBy (tnHeld? 1 3) (s 2)) = some 3 ∧ enc 3 1 (convertBy (tnHeld? 3 1) (a 3)) = some 2 ∧
    convertBy (tnHeld? 1 3) (s 3) = none ∧ convertBy (tnHeld? 3 1) (a 5) = none := by decide +kernel
/-- `Int2Float`: 4 and −8 are data of `p1x3`, 3 is none; 0 is positive zero. -/
example : enc 1 3 (ofIntBy (tnHeld? 1 3) 4) = some 5 ∧ enc 1 3 (ofIntBy (tnHeld? 1 3) (-8)) = some 14 ∧
    ofIntBy (tnHeld? 1 3) 3 = none ∧ enc 1 3 (ofIntBy (tnHeld? 1 3) 0) = some 0 := by decide +kernel
/-- The square root of 4 is 2; 2 has no root among the data. -/
example : enc 1 3 (tnSqrt? 1 3 (a 5)) = some 4 ∧ tnSqrt? 1 3 (a 4) = none := by decide +kernel

/-! ## Infinite exactly when beyond the largest finite datum (`tnIsInf_datum`), at every encoding -/

example : (List.range 17).all (fun b =>
    isInf (a b) == (cmpExact (a b) (a 6) == some .gt || cmpExact (a b) (a 14) == some .lt)) = true := by
  decide +kernel
example : (List.range 17).all (fun b =>
    isInf (s b) == (cmpExact (s b) (s 3) == some .gt || cmpExact (s b) (s 11) == some .lt)) = true := by
  decide +kernel

/-! ## The rounding has a value on the stated region and is to the nearest datum (`tnRound_isSome`, `tnRound_nearest`)

Magnitudes are in units of `2^(−shift)`: at `p1x3` (`shift` 3) the largest finite datum 8 is 64
units; at `p3x1` (`shift` 2) the largest finite datum 1.5 is 6 units. -/

/-- At `p1x3`, `N / D` is not halfway between two powers of two. -/
theorem p1x3_off_tie {N D : Nat} (h : ∀ X, 1 ≤ X → 2 * (N * 2 ^ shift 1 3) ≠ 3 * 2 ^ X * D) :
    (1 : Nat) = 1 → ∀ X, 1 ≤ X → 2 * (N * 2 ^ shift 1 3) ≠ 3 * 2 ^ X * D := fun _ => h

/-- The region's three hypotheses at `p1x3`: the largest finite datum itself (8); 3/16, between half
the smallest positive datum and that datum; 7, which rounds into the next binade. -/
example : (tnRound 1 3 .positive 8 1).isSome = true :=
  tnRound_isSome (W := 64) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (p1x3_off_tie fun X _ => by simp only [show shift 1 3 = 3 by decide]; omega)
example : (tnRound 1 3 .negative 3 16).isSome = true :=
  tnRound_isSome (W := 64) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (p1x3_off_tie fun X hX => by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hX
      simp only [show shift 1 3 = 3 by decide]; omega)
example : (tnRound 1 3 .positive 7 1).isSome = true :=
  tnRound_isSome (W := 64) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (p1x3_off_tie fun X _ => by simp only [show shift 1 3 = 3 by decide]; omega)

/-- At `p3x1`: the two ties 3/4 and 5/4, and the largest finite datum 3/2. A tie has a value where
the precision is not 1. -/
example : (tnRound 3 1 .positive 3 4).isSome = true ∧ (tnRound 3 1 .positive 5 4).isSome = true ∧
    (tnRound 3 1 .negative 3 2).isSome = true :=
  ⟨tnRound_isSome (W := 6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
      (fun h => absurd h (by decide)),
   tnRound_isSome (W := 6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
      (fun h => absurd h (by decide)),
   tnRound_isSome (W := 6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
      (fun h => absurd h (by decide))⟩

/-- The two statements together at the tie 3/4 of `p3x1` and at 7 of `p1x3`: the rounding has a
value, no datum is nearer, and a datum of another value as near leaves an even significand. -/
example : ∃ m q hm, tnRound 3 1 .positive 3 4 = some (.finite .positive m q hm) ∧
    ∀ d w, tnIsDatum 3 1 d = true → tnMag 3 1 d = some w →
      tnGap (3 * 2 ^ shift 3 1) (m * 2 ^ (q + (shift 3 1 : Int)).toNat * 4) ≤ tnGap (3 * 2 ^ shift 3 1) (w * 4) ∧
        (tnGap (3 * 2 ^ shift 3 1) (m * 2 ^ (q + (shift 3 1 : Int)).toNat * 4) = tnGap (3 * 2 ^ shift 3 1) (w * 4) →
          w ≠ m * 2 ^ (q + (shift 3 1 : Int)).toNat → m % 2 = 0) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (tnRound_isSome (p := 3) (e := 1) (sg := .positive) (N := 3) (D := 4)
    (W := 6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (fun h => absurd h (by decide)))
  obtain ⟨m, q, hm, rfl, h⟩ := tnRound_nearest (by decide) (by decide) (by decide) hu
  exact ⟨m, q, hm, hu, h⟩

example : ∃ m q hm, tnRound 1 3 .positive 7 1 = some (.finite .positive m q hm) ∧
    ∀ d w, tnIsDatum 1 3 d = true → tnMag 1 3 d = some w →
      tnGap (7 * 2 ^ shift 1 3) (m * 2 ^ (q + (shift 1 3 : Int)).toNat * 1) ≤ tnGap (7 * 2 ^ shift 1 3) (w * 1) ∧
        (tnGap (7 * 2 ^ shift 1 3) (m * 2 ^ (q + (shift 1 3 : Int)).toNat * 1) = tnGap (7 * 2 ^ shift 1 3) (w * 1) →
          w ≠ m * 2 ^ (q + (shift 1 3 : Int)).toNat → m % 2 = 0) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (tnRound_isSome (p := 1) (e := 3) (sg := .positive) (N := 7) (D := 1)
    (W := 64) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (p1x3_off_tie fun X _ => by simp only [show shift 1 3 = 3 by decide]; omega))
  obtain ⟨m, q, hm, rfl, h⟩ := tnRound_nearest (by decide) (by decide) (by decide) hu
  exact ⟨m, q, hm, hu, h⟩

/-- `N / D` is in the region of `tnRound_isSome` at the format `(p, e)` whose largest finite datum
is `W` units; the halfway points up to `2^8` units. -/
def inRegion (p e W N D : Nat) : Bool :=
  decide (N * 2 ^ shift p e ≤ W * D) && decide (D < N * 2 ^ shift p e) &&
    (p != 1 || (List.range 8).all fun X => 2 * (N * 2 ^ shift p e) != 3 * 2 ^ (X + 1) * D)

/-- The result `r` of rounding `N / D` is a zero or finite datum, no encoding's datum is nearer, and
an encoding of another value as near leaves `r`'s significand even. -/
def isNearest (p e N D : Nat) (r : UnpackedFloat) : Bool :=
  match tnMag p e r with
  | none => false
  | some x => (List.range (2 ^ (p + e))).all fun b =>
    match tnMag p e (tnUnpack p e b) with
    | none => true
    | some w => decide (tnGap (N * 2 ^ shift p e) (x * D) ≤ tnGap (N * 2 ^ shift p e) (w * D)) &&
      (tnGap (N * 2 ^ shift p e) (x * D) != tnGap (N * 2 ^ shift p e) (w * D) || w == x ||
        (match r with | .finite _ m _ _ => m % 2 == 0 | _ => false))

/-- The fractions `(N + 1) / (D + 1)` for `N < 40`, `D < 12`. -/
def fracs : List (Nat × Nat) := (List.range 40).flatMap fun N => (List.range 12).map fun D => (N + 1, D + 1)

/-- On the grid, at `p1x3` and at `p3x1`: in the region the rounding has a value, and every value
it has is a nearest datum, a tie to the even significand. -/
example : fracs.all (fun (N, D) =>
    (!inRegion 1 3 64 N D || (tnRound 1 3 .positive N D).isSome) &&
      (match tnRound 1 3 .positive N D with | some r => isNearest 1 3 N D r | none => true)) = true := by
  decide +kernel
example : fracs.all (fun (N, D) =>
    (!inRegion 3 1 6 N D || (tnRound 3 1 .positive N D).isSome) &&
      (match tnRound 3 1 .positive N D with | some r => isNearest 3 1 N D r | none => true)) = true := by
  decide +kernel
/-- At `p1x1` no positive finite datum exists, the region is empty (`tnMax?` has no value) and the
rounding has none. -/
example : fracs.all (fun (N, D) => (tnRound 1 1 .positive N D).isNone) = true := by decide +kernel

end KCore.FloatThinTest
