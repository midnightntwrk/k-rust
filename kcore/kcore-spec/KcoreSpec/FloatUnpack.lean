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

/-- **(a)** A finite datum of the format: its significand is below `2^p` and its exponent at most
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

/-- **(c)** `unpack` after `pack` is the identity at a datum of the format. -/
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

end KCore.KFloat
