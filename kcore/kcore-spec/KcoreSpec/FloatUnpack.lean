/-
  KCore. Facts of Lean core's binary floating-point model (`Float.Model`) at every format it covers
  (`KFloat.spec?`: a stored significand of `w ≥ 1` bits, so a precision `p = w + 1 ≥ 2`, and an
  exponent width `e ≥ 2`, bias `B = 2^(e−1) − 1`), proved from the definitions of `unpack`, `pack`
  and `round`, symbolically in the format.

  - `datum_unpack`: the datum of any encoding is a `Datum` of the format: a finite datum is a normal
    one, `2^w ≤ m < 2^p` and `1 − B − w ≤ q ≤ B − w`, or a subnormal one, `m < 2^w` and
    `q = 1 − B − w`. So a finite datum's significand is below `2^p` and its exponent at most
    `2^e − 2 − B − w` (`unpack_finite_bounds`), the exponent field being at most `2^e − 2`.
  - `unpack_pack`: `pack` and `unpack` are inverse at a `Datum` (`unpackBits_packBits` on the
    encoding as a number).
  - `round_of_target`: `round` leaves `m·2^q` unchanged where `q` is already the exponent the format
    gives it (`targetExponent`); so `maxValue s` is `(2^p − 1)·2^(B − w)` (`maxValue_eq`, `exact_maxValue`).
  - `isInf_unpack`: a datum of the format is infinite exactly when it is above `maxValue s` or below
    its negation by the exact comparison (`cmpExact`): every finite datum lies within them.
-/
import KcoreSpec.FloatDomain

set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## The format's constants -/

theorem fu_two_pow_exponentBits (s : Format) : 2 ^ s.exponentBits = 2 * (s.exponentBias + 1) := by
  have he := s.he
  unfold Format.exponentBias
  have h1 : 2 ^ s.exponentBits = 2 * 2 ^ (s.exponentBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h2 : 1 ≤ 2 ^ (s.exponentBits - 1) := Nat.one_le_two_pow
  omega

theorem fu_one_le_exponentBias (s : Format) : 1 ≤ s.exponentBias := by
  have he := s.he
  unfold Format.exponentBias
  have : 2 ^ 1 ≤ 2 ^ (s.exponentBits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem fu_mantissaBits (s : Format) : s.mantissaBits = s.mantissaBitsWithoutImplicit + 1 := by
  unfold Format.mantissaBits; omega

theorem fu_minExponent (s : Format) :
    s.minExponent = 1 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
  have he := s.he
  unfold Format.minExponent Format.mantissaBits Format.exponentBias
  have h2 : 1 ≤ 2 ^ (s.exponentBits - 1) := Nat.one_le_two_pow
  have hc : ((2 ^ (s.exponentBits - 1) : Nat) : Int) = (2 : Int) ^ (s.exponentBits - 1) := by
    simp
  omega

/-! ## The data of a format -/

/-- A datum of the format `s` (`w` stored significand bits, bias `B`): NaN, an infinity, a zero, a
normal finite datum `m·2^q` with `2^w ≤ m < 2^(w+1)` and `1 − B − w ≤ q ≤ B − w`, or a subnormal
one with `m < 2^w` and `q = 1 − B − w`. -/
def Datum (s : Format) : UnpackedFloat → Prop
  | .finite _ m q _ =>
    (2 ^ s.mantissaBitsWithoutImplicit ≤ m ∧ m < 2 ^ s.mantissaBits ∧
      1 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit ≤ q ∧
      q ≤ (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit) ∨
    (m < 2 ^ s.mantissaBitsWithoutImplicit ∧
      q = 1 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit)
  | _ => True

theorem fu_finite_congr {sg : Sign} {m m' : Nat} {q q' : Int} {h : 0 < m} {h' : 0 < m'}
    (hm : m' = m) (hq : q' = q) : UnpackedFloat.finite sg m' q' h' = .finite sg m q h := by
  subst hm hq; rfl

theorem fu_toNat_ne_zero {n : Nat} {x : BitVec n} (h : ¬ x = 0#n) : x.toNat ≠ 0 := by
  intro h'; exact h (BitVec.toNat_inj.mp (by simp [h']))

theorem fu_toNat_ne_allOnes {n : Nat} {x : BitVec n} (h : ¬ x = -1#n) : x.toNat ≠ 2 ^ n - 1 := by
  intro h'; apply h; rw [BitVec.neg_one_eq_allOnes]; exact BitVec.toNat_inj.mp (by simp [h'])

theorem fu_toNat_one_append {n : Nat} (v : BitVec n) : (1#1 ++ v).toNat = 2 ^ n + v.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt v.isLt]
  simp [Nat.one_shiftLeft]

/-- **The datum of every encoding is a `Datum` of the format.** -/
theorem datum_unpack (s : Format) (b : BitVec s.numBits) : Datum s (unpack s b) := by
  have hE := fu_two_pow_exponentBits s
  have hx := (unpackExponent b).isLt
  have hmv := (unpackMantissa b).isLt
  unfold UnpackedFloat.unpack
  dsimp only
  split
  · split <;> trivial
  · rename_i hne1
    have h1 := fu_toNat_ne_allOnes hne1
    split
    · rename_i h0
      split
      · trivial
      · right
        refine ⟨hmv, ?_⟩
        rw [h0]; simp; omega
    · rename_i h0
      have h0' := fu_toNat_ne_zero h0
      left
      rw [fu_toNat_one_append, fu_mantissaBits]
      have : 2 ^ (s.mantissaBitsWithoutImplicit + 1) = 2 * 2 ^ s.mantissaBitsWithoutImplicit :=
        Nat.pow_succ'
      refine ⟨by omega, by omega, by omega, by omega⟩

/-- A finite datum of the format: its significand is below `2^p` and its exponent at most
`2^e − 2 − B − (p − 1)`. -/
theorem unpack_finite_bounds {s : Format} {b : BitVec s.numBits} {sg : Sign} {m : Nat} {q : Int}
    {h : 0 < m} (hu : unpack s b = .finite sg m q h) :
    m < 2 ^ s.mantissaBits ∧
      q ≤ (2 ^ s.exponentBits : Nat) - 2 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
  have hd := datum_unpack s b
  rw [hu] at hd
  have hE := fu_two_pow_exponentBits s
  have hB := fu_one_le_exponentBias s
  have hp : 2 ^ s.mantissaBits = 2 * 2 ^ s.mantissaBitsWithoutImplicit := by
    rw [fu_mantissaBits]; exact Nat.pow_succ'
  rcases hd with ⟨-, h2, -, h4⟩ | ⟨h1, h2⟩
  · exact ⟨h2, by omega⟩
  · exact ⟨by omega, by omega⟩

/-! ## `unpack` after `pack` -/

@[simp]
theorem fu_unpackSign_packComponents {spec : Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  obtain rfl : i = 0 := by omega
  simp [unpackSign, packComponents, BitVec.getLsbD_append, BitVec.getElem_append]

@[simp]
theorem fu_ofBitVec_toBitVec (sg : Sign) : Sign.ofBitVec sg.toBitVec = sg := by
  cases sg <;> rfl

theorem fu_zero_ne_negOne (s : Format) : ¬ (0#s.exponentBits : BitVec s.exponentBits) = -1#_ := by
  have hE := fu_two_pow_exponentBits s
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
  simp at this; omega

/-- `unpack` after `pack` is the identity at a datum of the format. -/
theorem unpack_pack (s : Format) (u : UnpackedFloat) (hu : Datum s u) : unpack s (pack s u) = u := by
  have hE := fu_two_pow_exponentBits s
  have hB := fu_one_le_exponentBias s
  have hw := s.hm
  match u, hu with
  | .notANumber, _ =>
    have hne : ¬ (1#s.mantissaBitsWithoutImplicit <<< (s.mantissaBitsWithoutImplicit - 1)) = 0#_ := by
      intro h
      have := congrArg BitVec.toNat h
      have hlt : 2 ^ (s.mantissaBitsWithoutImplicit - 1) < 2 ^ s.mantissaBitsWithoutImplicit :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      have h1 : 1 % 2 ^ s.mantissaBitsWithoutImplicit = 1 :=
        Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      simp [Nat.one_shiftLeft, h1, Nat.mod_eq_of_lt hlt] at this
    simp [UnpackedFloat.pack, packedNaN, UnpackedFloat.unpack, hne]
  | .infinity sg, _ => simp [UnpackedFloat.pack, packedInfinity, UnpackedFloat.unpack]
  | .zero sg, _ => simp [UnpackedFloat.pack, packedZero, UnpackedFloat.unpack, show s.exponentBits ≠ 0 by have := s.he; omega]
  | .finite sg m q hm, hd =>
    have hp : 2 ^ s.mantissaBits = 2 * 2 ^ s.mantissaBitsWithoutImplicit := by
      rw [fu_mantissaBits]; exact Nat.pow_succ'
    have hq : q ≤ (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
      rcases hd with ⟨-, -, -, h⟩ | ⟨-, h⟩ <;> omega
    have hlo : 1 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit ≤ q := by
      rcases hd with ⟨-, -, h, -⟩ | ⟨-, h⟩ <;> omega
    have hov : ¬ 2 ^ s.exponentBits ≤
        (q + s.exponentBias + s.mantissaBitsWithoutImplicit).toNat + 1 := by omega
    by_cases hn : m.log2 + 1 = s.mantissaBits
    · -- normal
      have hm1 : 2 ^ s.mantissaBitsWithoutImplicit ≤ m ∧ m < 2 ^ s.mantissaBits := by
        have := (Nat.log2_eq_iff (Nat.pos_iff_ne_zero.mp hm)).mp (show m.log2 = s.mantissaBitsWithoutImplicit by
          rw [fu_mantissaBits] at hn; omega)
        rw [fu_mantissaBits]; exact this
      have hpos : 1 ≤ (q + s.exponentBias + s.mantissaBitsWithoutImplicit).toNat := by
        rcases hd with ⟨-, -, h, -⟩ | ⟨h, -⟩
        · omega
        · omega
      have hlt : (q + s.exponentBias + s.mantissaBitsWithoutImplicit).toNat < 2 ^ s.exponentBits := by
        omega
      have hne1 : ¬ BitVec.ofNat s.exponentBits (q + s.exponentBias + s.mantissaBitsWithoutImplicit).toNat
          = -1#_ := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlt] at this
        omega
      have hne0 : ¬ BitVec.ofNat s.exponentBits (q + s.exponentBias + s.mantissaBitsWithoutImplicit).toNat
          = 0#_ := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        simp at this; omega
      simp only [UnpackedFloat.pack, hov, ite_false, hn, ite_true]
      unfold UnpackedFloat.unpack
      simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
        fu_unpackSign_packComponents, fu_ofBitVec_toBitVec, hne1, hne0, ite_false]
      apply fu_finite_congr
      · rw [fu_toNat_one_append, BitVec.toNat_ofNat]
        rw [fu_mantissaBits] at hm1
        have : 2 ^ (s.mantissaBitsWithoutImplicit + 1) = 2 * 2 ^ s.mantissaBitsWithoutImplicit :=
          Nat.pow_succ'
        rw [Nat.mod_eq_sub_mod hm1.1, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega
    · -- subnormal
      have hsub : m < 2 ^ s.mantissaBitsWithoutImplicit ∧
          q = 1 - (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
        rcases hd with ⟨h1, h2, -, -⟩ | h
        · exfalso; apply hn
          have := (Nat.log2_eq_iff (k := s.mantissaBitsWithoutImplicit) (Nat.pos_iff_ne_zero.mp hm)).mpr
            ⟨h1, by rw [fu_mantissaBits] at h2; exact h2⟩
          rw [this, fu_mantissaBits]
        · exact h
      have hne0 : ¬ BitVec.ofNat s.mantissaBitsWithoutImplicit m = 0#_ := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub.1] at this
        simp at this; omega
      simp only [UnpackedFloat.pack, hov, ite_false, hn]
      unfold UnpackedFloat.unpack
      simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
        fu_unpackSign_packComponents, fu_ofBitVec_toBitVec, fu_zero_ne_negOne, ite_true, ite_false,
        hne0, dite_false]
      apply fu_finite_congr
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub.1]
      · simp; omega

/-- `unpack_pack` on the encoding as a number (`unpackBits`, `packBits`). -/
theorem unpackBits_packBits (s : Format) (u : UnpackedFloat) (hu : Datum s u) :
    unpackBits s (packBits s u) = u := by
  unfold unpackBits packBits
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact unpack_pack s u hu

theorem datum_neg {s : Format} {u : UnpackedFloat} (hu : Datum s u) : Datum s u.neg := by
  cases u <;> exact hu

/-! ## `round` at a value the format holds -/

theorem fu_shr_zero (em : ExtendedMantissa) : em >>> (0 : Nat) = em := rfl

/-- At an exponent that is already the target, `shiftToTargetExponent` shifts nothing. -/
theorem fu_shiftToTargetExponent_of_target (s : Format) {m : Nat} {q : Int}
    (ht : s.targetExponent (totalExponent m q) = q) :
    shiftToTargetExponent s m q .exact = (⟨m, false, false⟩, q) := by
  unfold shiftToTargetExponent shiftToExponent
  simp only [ht, Int.sub_self, Int.toNat_zero, fu_shr_zero, Int.natCast_zero, Int.add_zero]
  rfl

/-- **`round` leaves `m·2^q` unchanged where `q` is the exponent the format gives it**
(`targetExponent` of its total exponent): no bit is shifted out, so the mantissa is exact and
rounding to nearest keeps it. -/
theorem round_of_target (s : Format) (sg : Sign) {m : Nat} {q : Int} (hm : 0 < m)
    (ht : s.targetExponent (totalExponent m q) = q) : round s sg m q = .finite sg m q hm := by
  unfold round decreaseExponent
  simp only [ht, Int.sub_self, Int.toNat_zero, Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero]
  unfold roundWithAccuracy
  rw [fu_shiftToTargetExponent_of_target s ht]
  dsimp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
    Accuracy.roundToNearestEven]
  rw [fu_shiftToTargetExponent_of_target s ht]
  dsimp only
  simp [Nat.pos_iff_ne_zero.mp hm]

/-- The total exponent of `2^p − 1` at `B − w` is `B + 1`, and the format's target exponent for
it is `B − w`. -/
theorem fu_target_maxValue (s : Format) :
    s.targetExponent (totalExponent (2 ^ s.mantissaBits - 1)
      ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit)) =
      (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
  have hB := fu_one_le_exponentBias s
  have hp : 2 ^ s.mantissaBits = 2 * 2 ^ s.mantissaBitsWithoutImplicit := by
    rw [fu_mantissaBits]; exact Nat.pow_succ'
  have h1 : 1 ≤ 2 ^ s.mantissaBitsWithoutImplicit := Nat.one_le_two_pow
  have hl : (2 ^ s.mantissaBits - 1).log2 = s.mantissaBitsWithoutImplicit :=
    (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by rw [Nat.pow_succ]; omega⟩
  unfold Format.targetExponent totalExponent
  rw [hl, fu_minExponent, fu_mantissaBits]
  omega

theorem fu_maxValue_pos (s : Format) : 0 < 2 ^ s.mantissaBits - 1 := by
  have : 2 ^ 1 ≤ 2 ^ s.mantissaBits :=
    Nat.pow_le_pow_right (by decide) (by rw [fu_mantissaBits]; omega)
  omega

/-- The format's largest finite value is the datum `(2^p − 1)·2^(B − (p − 1))`: `round`
leaves it unchanged. -/
theorem maxValue_eq (s : Format) :
    maxValue s = .finite .positive (2 ^ s.mantissaBits - 1)
      ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit) (fu_maxValue_pos s) :=
  round_of_target s .positive (fu_maxValue_pos s) (fu_target_maxValue s)

/-- `exact (maxValue s) = (2^p − 1, B − (p − 1))`. -/
theorem exact_maxValue (s : Format) :
    exact (maxValue s) =
      some (((2 ^ s.mantissaBits - 1 : Nat) : Int), (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit) := by
  rw [maxValue_eq]; rfl

/-- The largest finite value is a datum of the format. -/
theorem datum_maxValue (s : Format) : Datum s (maxValue s) := by
  rw [maxValue_eq]
  have hp : 2 ^ s.mantissaBits = 2 * 2 ^ s.mantissaBitsWithoutImplicit := by
    rw [fu_mantissaBits]; exact Nat.pow_succ'
  have h1 : 1 ≤ 2 ^ s.mantissaBitsWithoutImplicit := Nat.one_le_two_pow
  have hB := fu_one_le_exponentBias s
  left
  refine ⟨by omega, by omega, by omega, Int.le_refl _⟩

/-! ## The finite data lie within `±maxValue` -/

theorem fu_two_pow_nonneg (n : Nat) : (0 : Int) ≤ 2 ^ n := Int.pow_nonneg (by decide)

theorem fu_one_le_two_pow (n : Nat) : (1 : Int) ≤ 2 ^ n := by
  have : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by simp
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- `a·2^q` with `|a| ≤ M` and `q ≤ Q` is not above `M·2^Q` and not below `−M·2^Q`. -/
theorem fu_cmpScaled_within {a q : Int} {M : Nat} {Q : Int} (hq : q ≤ Q) (ha : -(M : Int) ≤ a ∧ a ≤ M) :
    cmpScaled a q M Q ≠ .gt ∧ cmpScaled a q (-(M : Int)) Q ≠ .lt := by
  unfold cmpScaled
  dsimp only
  rw [Int.min_eq_left hq, Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one]
  have hX := fu_one_le_two_pow (Q - q).toNat
  generalize (2 : Int) ^ (Q - q).toNat = X at hX ⊢
  have hM : (M : Int) * 1 ≤ M * X := Int.mul_le_mul_of_nonneg_left hX (by omega)
  rw [Int.neg_mul]
  constructor
  · intro h; rw [Int.compare_eq_gt] at h; omega
  · intro h; rw [Int.compare_eq_lt] at h; omega

/-- A zero is not above `M·2^Q` and not below `−M·2^Q`. -/
theorem fu_cmpScaled_zero (M : Nat) (Q : Int) :
    cmpScaled 0 0 M Q ≠ .gt ∧ cmpScaled 0 0 (-(M : Int)) Q ≠ .lt := by
  unfold cmpScaled
  dsimp only
  rw [Int.zero_mul]
  have hX := fu_two_pow_nonneg (Q - min 0 Q).toNat
  generalize (2 : Int) ^ (Q - min 0 Q).toNat = X at hX ⊢
  have hM : 0 ≤ (M : Int) * X := Int.mul_nonneg (by omega) hX
  rw [Int.neg_mul]
  constructor
  · intro h; rw [Int.compare_eq_gt] at h; omega
  · intro h; rw [Int.compare_eq_lt] at h; omega

theorem fu_within_false {X Y : Ordering} (h1 : X ≠ .gt) (h2 : Y ≠ .lt) :
    false = (some X == some .gt || some Y == some .lt) := by
  cases X <;> cases Y <;> simp_all

/-- **Every datum of the format is infinite exactly when it is above `maxValue s` or below its
negation** (`cmpExact`): an infinity is above or below every finite value, NaN is in no order, and
a zero or a finite datum `m·2^q` has `m ≤ 2^p − 1` and `q ≤ B − w` (`Datum`), so it lies within. -/
theorem isInf_datum (s : Format) (u : UnpackedFloat) (hd : Datum s u) :
    isInf u = (cmpExact u (maxValue s) == some .gt || cmpExact u (maxValue s).neg == some .lt) := by
  have hB := fu_one_le_exponentBias s
  rw [maxValue_eq]
  match u, hd with
  | .notANumber, _ => rfl
  | .infinity .positive, _ => rfl
  | .infinity .negative, _ => rfl
  | .zero sg, _ =>
    obtain ⟨h1, h2⟩ := fu_cmpScaled_zero (2 ^ s.mantissaBits - 1)
      ((s.exponentBias : Int) - s.mantissaBitsWithoutImplicit)
    exact fu_within_false h1 h2
  | .finite sg m q hm, hd =>
    have hm1 : m ≤ 2 ^ s.mantissaBits - 1 := by
      have hp : 2 ^ s.mantissaBits = 2 * 2 ^ s.mantissaBitsWithoutImplicit := by
        rw [fu_mantissaBits]; exact Nat.pow_succ'
      rcases hd with ⟨-, h, -, -⟩ | ⟨h, -⟩ <;> omega
    have hq : q ≤ (s.exponentBias : Int) - s.mantissaBitsWithoutImplicit := by
      rcases hd with ⟨-, -, -, h⟩ | ⟨-, h⟩ <;> omega
    have ha : -((2 ^ s.mantissaBits - 1 : Nat) : Int) ≤ sg.apply m ∧
        sg.apply m ≤ ((2 ^ s.mantissaBits - 1 : Nat) : Int) := by
      cases sg <;> simp only [Sign.apply] <;> omega
    obtain ⟨h1, h2⟩ := fu_cmpScaled_within hq ha
    exact fu_within_false h1 h2

/-- `isInf_datum` at the datum of an encoding (`datum_unpack`). -/
theorem isInf_unpack (s : Format) (b : BitVec s.numBits) :
    isInf (UnpackedFloat.unpack s b) =
      (cmpExact (UnpackedFloat.unpack s b) (maxValue s) == some .gt ||
        cmpExact (UnpackedFloat.unpack s b) (maxValue s).neg == some .lt) :=
  isInf_datum s _ (datum_unpack s b)

end KCore.KFloat
