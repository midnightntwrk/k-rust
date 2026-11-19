/-
  KCore. Facts of the model of the formats with a field of 1 (FloatThin.lean), symbolically in the
  format `(p, e)`, `p` and `e` positive.

  - `tnIsDatum_unpack`: the datum of any encoding is a datum of the format.
  - `tnUnpack_pack`: `tnUnpack` after `tnPack` is the identity at a datum; `thinOK_tnPack`: the
    encoding of a datum is a Float literal's (`thinOK`).
  - `tnMax?_normal`, `tnMax?_subnormal`, `tnMax?_one_one`, `tnMin?_eq`, `tnMin?_one_one`: the
    largest finite and the smallest positive datum, and none of either at `(1, 1)`.
  - `tnRound_datum` … `tnSqrt?_datum`, `sumBy_datum` … `ofIntBy_datum`: every operation's result is
    a datum of the format; `ok_tnPack`: its encoding is a Float literal's data.
  - `tnIsInf_datum`: a datum is infinite exactly when it is above the largest finite datum or below
    its negation by the exact comparison.
  - `sum?_eq_sumBy` …: the operations of FloatDomain.lean are the formulas `sumBy` … at Lean core's
    rounding.
-/
import KcoreSpec.FloatThin
import KcoreSpec.FloatUnpack

set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## Encodings -/

theorem tn_bits_eq (p e s x f : Nat) : tnBits p e s x f = (s * 2 ^ e + x) * 2 ^ (p - 1) + f := by
  unfold tnBits
  rw [Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ e)]

theorem tn_bits_div {p e s x f : Nat} (hf : f < 2 ^ (p - 1)) :
    tnBits p e s x f / 2 ^ (p - 1) = s * 2 ^ e + x := by
  rw [tn_bits_eq, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hf, Nat.add_zero]

theorem tn_bits_sign {p e s x f : Nat} (hx : x < 2 ^ e) (hf : f < 2 ^ (p - 1)) :
    tnBits p e s x f / 2 ^ (p - 1 + e) = s := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, tn_bits_div hf, Nat.mul_comm,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, Nat.add_zero]

theorem tn_bits_expo {p e s x f : Nat} (hx : x < 2 ^ e) (hf : f < 2 ^ (p - 1)) :
    tnBits p e s x f / 2 ^ (p - 1) % 2 ^ e = x := by
  rw [tn_bits_div hf, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]

theorem tn_bits_frac {p e s x f : Nat} (hf : f < 2 ^ (p - 1)) :
    tnBits p e s x f % 2 ^ (p - 1) = f := by
  rw [tn_bits_eq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]

theorem tn_pow_split {p : Nat} (e : Nat) (hp : 1 ≤ p) : 2 ^ (p + e) = 2 * 2 ^ e * 2 ^ (p - 1) := by
  have : p + e = (p - 1) + (e + 1) := by omega
  rw [this, Nat.pow_add, Nat.pow_succ]
  rw [Nat.mul_comm (2 ^ (p - 1)), Nat.mul_comm (2 ^ e) 2]

theorem tn_bits_lt {p e s x f : Nat} (hp : 1 ≤ p) (hs : s ≤ 1) (hx : x < 2 ^ e) (hf : f < 2 ^ (p - 1)) :
    tnBits p e s x f < 2 ^ (p + e) := by
  rw [tn_bits_eq, tn_pow_split e hp]
  have h1 : s * 2 ^ e + x + 1 ≤ 2 * 2 ^ e := by
    have : s * 2 ^ e ≤ 1 * 2 ^ e := Nat.mul_le_mul_right _ hs
    omega
  have h2 := Nat.mul_le_mul_right (2 ^ (p - 1)) h1
  rw [Nat.succ_mul] at h2
  omega

theorem tn_signBit_le (sg : Sign) : tnSignBit sg ≤ 1 := by cases sg <;> decide

theorem tn_sign_of_bit (sg : Sign) :
    (if tnSignBit sg = 0 then Sign.positive else Sign.negative) = sg := by cases sg <;> rfl

/-- The datum of the encoding with sign bit of `sg`, exponent field `x` and significand field `f`. -/
theorem tnUnpack_bits {p e x f : Nat} (sg : Sign) (hp : 1 ≤ p) (hx : x < 2 ^ e) (hf : f < 2 ^ (p - 1)) :
    tnUnpack p e (tnBits p e (tnSignBit sg) x f) =
      if x = 2 ^ e - 1 then (if f = 0 then .infinity sg else .notANumber)
      else if h : sig p x f = 0 then .zero sg
      else .finite sg (sig p x f) ((expo x : Int) - (shift p e : Int)) (Nat.pos_of_ne_zero h) := by
  unfold tnUnpack
  simp only [Nat.not_le.mpr (tn_bits_lt hp (tn_signBit_le sg) hx hf), ↓reduceIte]
  simp only [tn_bits_sign hx hf, tn_bits_expo hx hf, tn_bits_frac hf, tn_sign_of_bit]

theorem tn_two_le_pow {e : Nat} (he : 1 ≤ e) : 2 ≤ 2 ^ e := by
  have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
  omega

theorem tn_pow_pred {p : Nat} (hp : 1 ≤ p) : 2 ^ p = 2 * 2 ^ (p - 1) := by
  have : p = (p - 1) + 1 := by omega
  rw [this, Nat.pow_succ']; simp

/-- **`tnUnpack` after `tnPack` is the identity at a datum of the format.** -/
theorem tnUnpack_pack {p e : Nat} (hp : 1 ≤ p) (he : 1 ≤ e) (u : UnpackedFloat)
    (hu : tnIsDatum p e u = true) : tnUnpack p e (tnPack p e u) = u := by
  have h2 := tn_two_le_pow he
  have hA : 0 < 2 ^ (p - 1) := Nat.two_pow_pos _
  match u, hu with
  | .notANumber, _ => simp [tnPack, tnUnpack]
  | .infinity sg, _ =>
    rw [tnPack, tnUnpack_bits sg hp (by omega) hA]; simp
  | .zero sg, _ =>
    rw [tnPack, tnUnpack_bits sg hp (by omega) hA]
    have : ¬ (0 = 2 ^ e - 1) := by omega
    simp [this, sig]
  | .finite sg m q hm, hu =>
    simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq] at hu
    rcases hu with ⟨h1, h2'⟩ | ⟨h1, h2', h3, h4⟩
    · simp only [tnPack, h1, ↓reduceIte]
      rw [tnUnpack_bits sg hp (by omega) h1]
      have h0 : ¬ (0 = 2 ^ e - 1) := by omega
      have hs : sig p 0 m = m := by simp [sig]
      simp only [h0, ↓reduceIte, hs, Nat.ne_of_gt hm, ↓reduceDIte]
      exact fu_finite_congr rfl (by simp [expo]; omega)
    · have hpp := tn_pow_pred hp
      have hx : (q + (shift p e : Int)).toNat < 2 ^ e := by omega
      have hn : ¬ m < 2 ^ (p - 1) := by omega
      simp only [tnPack, hn, ↓reduceIte]
      rw [tnUnpack_bits sg hp hx (by omega)]
      have hx1 : ¬ ((q + (shift p e : Int)).toNat = 2 ^ e - 1) := by omega
      have hx0 : ¬ ((q + (shift p e : Int)).toNat = 0) := by omega
      have hs : sig p (q + (shift p e : Int)).toNat (m - 2 ^ (p - 1)) = m := by
        simp only [sig, hx0, ↓reduceIte]; omega
      simp only [hx1, ↓reduceIte, hs, Nat.ne_of_gt hm, ↓reduceDIte]
      exact fu_finite_congr rfl (by simp only [expo, hx0, ↓reduceIte]; omega)

/-- **The encoding of a datum of a format with a field of 1 is a Float literal's** (`thinOK`). -/
theorem thinOK_tnPack {p e : Nat} (hf : tnFormat p e = true) (u : UnpackedFloat)
    (hu : tnIsDatum p e u = true) : thinOK p e (tnPack p e u) = true := by
  have hf' := hf
  simp only [tnFormat, decide_eq_true_eq] at hf'
  obtain ⟨hp, he, -⟩ := hf'
  have h2 := tn_two_le_pow he
  have hA : 0 < 2 ^ (p - 1) := Nat.two_pow_pos _
  have key : ∀ (sg : Sign) (x f : Nat), x < 2 ^ e → f < 2 ^ (p - 1) → (x ≠ 2 ^ e - 1 ∨ f = 0) →
      thinOK p e (tnBits p e (tnSignBit sg) x f) = true := by
    intro sg x f hx hff hor
    unfold thinOK
    simp only [tnFormat] at hf
    rw [hf, Bool.true_and, tn_bits_expo hx hff, tn_bits_frac hff,
      decide_eq_true (tn_bits_lt hp (tn_signBit_le sg) hx hff)]
    rcases hor with h | h <;> simp [h]
  match u, hu with
  | .notANumber, _ =>
    unfold thinOK tnPack
    simp only [tnFormat] at hf
    simp [hf]
  | .infinity sg, _ => exact key sg _ _ (by omega) hA (Or.inr rfl)
  | .zero sg, _ => exact key sg _ _ (by omega) hA (Or.inr rfl)
  | .finite sg m q hm, hu =>
    simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq] at hu
    rcases hu with ⟨h1, -⟩ | ⟨h1, h2', h3, h4⟩
    · simp only [tnPack, h1, ↓reduceIte]; exact key sg _ _ (by omega) h1 (Or.inl (by omega))
    · have hpp := tn_pow_pred hp
      have hn : ¬ m < 2 ^ (p - 1) := by omega
      simp only [tnPack, hn, ↓reduceIte]
      exact key sg _ _ (by omega) (by omega) (Or.inl (by omega))

/-- **The datum of any encoding is a datum of the format.** -/
theorem tnIsDatum_unpack {p e : Nat} (hp : 1 ≤ p) (b : Nat) : tnIsDatum p e (tnUnpack p e b) = true := by
  have hpp := tn_pow_pred hp
  have hx : b / 2 ^ (p - 1) % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hf : b % 2 ^ (p - 1) < 2 ^ (p - 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold tnUnpack
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rename_i hx1
      split
      · rfl
      · rename_i hs
        simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
        by_cases hx0 : b / 2 ^ (p - 1) % 2 ^ e = 0
        · left; simp only [sig, expo, hx0, ↓reduceIte]; omega
        · right; simp only [sig, expo, hx0, ↓reduceIte]; omega

/-! ## The largest and the smallest datum -/

theorem tnMk?_datum {p e : Nat} {sg : Sign} {m : Nat} {q : Int} {u : UnpackedFloat}
    (h : tnMk? p e sg m q = some u) : tnIsDatum p e u = true := by
  unfold tnMk? at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem tnMk?_of {p e : Nat} (sg : Sign) {m : Nat} {q : Int} (hm : 0 < m)
    (hd : tnIsDatum p e (.finite sg m q hm) = true) : tnMk? p e sg m q = some (.finite sg m q hm) := by
  unfold tnMk?
  simp only [hm, ↓reduceDIte, hd, ↓reduceIte]

theorem tn_max_pos (p : Nat) : 0 < 2 ^ p - 1 ∨ p = 0 := by
  rcases Nat.eq_zero_or_pos p with h | h
  · exact Or.inr h
  · have := tn_two_le_pow h; omega

/-- The largest finite datum of a format with normal data: `(2^p − 1)·2^(2^e − 2 − shift)`. -/
theorem tnMax?_normal {p e : Nat} (hp : 1 ≤ p) (he : 2 ≤ e) :
    ∃ h, tnMax? p e = some (.finite .positive (2 ^ p - 1) (((2 ^ e - 2 : Nat) : Int) - (shift p e : Int)) h) := by
  have h2 := tn_two_le_pow hp
  have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
  have hpp := tn_pow_pred hp
  refine ⟨by omega, ?_⟩
  unfold tnMax?
  simp only [he, ↓reduceIte]
  apply tnMk?_of
  simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
  right; omega

/-- The largest finite datum of a format of one exponent bit: `(2^(p−1) − 1)·2^(1 − shift)`. -/
theorem tnMax?_subnormal {p : Nat} (hp : 2 ≤ p) :
    ∃ h, tnMax? p 1 = some (.finite .positive (2 ^ (p - 1) - 1) (1 - (shift p 1 : Int)) h) := by
  have h2 := tn_two_le_pow (show 1 ≤ p - 1 by omega)
  refine ⟨by omega, ?_⟩
  unfold tnMax?
  simp only [show ¬ (2 ≤ 1) by decide, ↓reduceIte]
  apply tnMk?_of
  simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨by omega, trivial⟩

theorem tnMax?_one_one : tnMax? 1 1 = none := by decide

theorem tnMin?_one_one : tnMin? 1 1 = none := by decide

/-- The smallest positive datum of a format other than `(1, 1)`: `2^(1 − shift)`. -/
theorem tnMin?_eq {p e : Nat} (hp : 1 ≤ p) (he : 1 ≤ e) (h : 2 ≤ p ∨ 2 ≤ e) :
    tnMin? p e = some (.finite .positive 1 (1 - (shift p e : Int)) Nat.one_pos) := by
  unfold tnMin?
  apply tnMk?_of
  simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · have hp1 : p = 1 := by omega
    have he2 : 2 ≤ e := by omega
    have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he2
    subst hp1
    right; simp; omega
  · have h2 := tn_two_le_pow (show 1 ≤ p - 1 by omega)
    exact Or.inl ⟨by omega, trivial⟩

/-! ## Every result is a datum -/

theorem tnRound_datum {p e : Nat} {sg : Sign} {N D : Nat} {u : UnpackedFloat}
    (h : tnRound p e sg N D = some u) : tnIsDatum p e u = true := by
  unfold tnRound at h
  dsimp only at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨n, -, h⟩ := h
  split at h <;> exact tnMk?_datum h

theorem tnNearest?_datum {p e : Nat} {a q : Int} {u : UnpackedFloat}
    (h : tnNearest? p e a q = some u) : tnIsDatum p e u = true := by
  unfold tnNearest? at h
  split at h
  · split at h
    · exact tnRound_datum h
    · cases h
  · cases h

theorem tnHeld?_datum {p e : Nat} {a q : Int} {u : UnpackedFloat}
    (h : tnHeld? p e a q = some u) : tnIsDatum p e u = true := by
  unfold tnHeld? heldBy at h
  rw [Option.filter_eq_some_iff] at h
  exact tnNearest?_datum h.1

theorem tnQuot?_datum {p e : Nat} {u v r : UnpackedFloat}
    (h : tnQuot? p e u v = some r) : tnIsDatum p e r = true := by
  unfold tnQuot? at h
  split at h
  · split at h
    · exact tnRound_datum h
    · cases h
  · cases h

theorem tnSqrt?_datum {p e : Nat} {u r : UnpackedFloat}
    (h : tnSqrt? p e u = some r) : tnIsDatum p e r = true := by
  unfold tnSqrt? at h
  split at h
  · dsimp only at h
    rw [Option.ite_none_right_eq_some] at h
    exact tnHeld?_datum h.2
  · cases h

theorem tnIsDatum_neg {p e : Nat} {u : UnpackedFloat} (h : tnIsDatum p e u = true) :
    tnIsDatum p e u.neg = true := by
  cases u <;> first | rfl | exact h

theorem tnIsDatum_abs {p e : Nat} {u : UnpackedFloat} (h : tnIsDatum p e u = true) :
    tnIsDatum p e u.abs = true := by
  cases u <;> first | rfl | exact h

/-! ## The formulas give data where the rounding does -/

section By

variable {p e : Nat} {nr : Int → Int → Option UnpackedFloat}

theorem heldBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {a q : Int}
    {r : UnpackedFloat} (h : heldBy nr a q = some r) : tnIsDatum p e r = true := by
  unfold heldBy at h
  rw [Option.filter_eq_some_iff] at h
  exact hn _ _ _ h.1

theorem sumBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {u v r : UnpackedFloat}
    (h : sumBy nr u v = some r) : tnIsDatum p e r = true := by
  unfold sumBy at h
  split at h
  · exact hn _ _ _ h
  · cases h

theorem diffBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {u v r : UnpackedFloat}
    (h : diffBy nr u v = some r) : tnIsDatum p e r = true := by
  unfold diffBy at h
  split at h
  · cases h; rfl
  · split at h
    · exact hn _ _ _ h
    · cases h

theorem prodBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {u v r : UnpackedFloat}
    (h : prodBy nr u v = some r) : tnIsDatum p e r = true := by
  unfold prodBy at h
  split at h
  · exact hn _ _ _ h
  · cases h

theorem remainderBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {u v r : UnpackedFloat}
    (h : remainderBy nr u v = some r) : tnIsDatum p e r = true := by
  unfold remainderBy at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · exact hn _ _ _ h
  · cases h

/-- A rounding to an integer of a datum of the format is one: the operand itself, or `nr`'s. -/
theorem roundToIntegralBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {d : Dir}
    {u r : UnpackedFloat} (hu : tnIsDatum p e u = true) (h : roundToIntegralBy nr d u = some r) :
    tnIsDatum p e r = true := by
  unfold roundToIntegralBy at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; exact hu
    · exact hn _ _ _ h
  · cases h

theorem convertBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {u r : UnpackedFloat}
    (h : convertBy nr u = some r) : tnIsDatum p e r = true := by
  unfold convertBy at h
  split at h
  · cases h; rfl
  · exact hn _ _ _ h
  · cases h

theorem ofIntBy_datum (hn : ∀ a q u, nr a q = some u → tnIsDatum p e u = true) {n : Int}
    {r : UnpackedFloat} (h : ofIntBy nr n = some r) : tnIsDatum p e r = true := by
  unfold ofIntBy at h
  split at h
  · cases h; rfl
  · exact hn _ _ _ h

end By

theorem tnNearest?_datum' (p e : Nat) : ∀ a q u, tnNearest? p e a q = some u → tnIsDatum p e u = true :=
  fun _ _ _ h => tnNearest?_datum h

theorem tnHeld?_datum' (p e : Nat) : ∀ a q u, tnHeld? p e a q = some u → tnIsDatum p e u = true :=
  fun _ _ _ h => tnHeld?_datum h

theorem tnMax?_datum {p e : Nat} {u : UnpackedFloat} (h : tnMax? p e = some u) : tnIsDatum p e u = true := by
  unfold tnMax? at h
  split at h <;> exact tnMk?_datum h

theorem tnMin?_datum {p e : Nat} {u : UnpackedFloat} (h : tnMin? p e = some u) : tnIsDatum p e u = true :=
  tnMk?_datum h

/-- A format with a field of 1 has no model in Lean core (`spec?`), so a Float literal of it is one
by `thinOK`. -/
theorem spec?_of_tnFormat {p e : Nat} (h : tnFormat p e = true) : spec? p e = none := by
  simp only [tnFormat, decide_eq_true_eq] at h
  unfold spec?
  simp only [show ¬ (2 ≤ p ∧ 2 ≤ e) by omega, ↓reduceDIte]

/-- **The encoding of a datum of a format with a field of 1 is a Float literal's data** (`ok`). -/
theorem ok_tnPack {p e : Nat} (hf : tnFormat p e = true) (u : UnpackedFloat)
    (hu : tnIsDatum p e u = true) : ok p e (tnPack p e u) = true := by
  unfold ok
  rw [spec?_of_tnFormat hf]
  exact thinOK_tnPack hf u hu

/-! ## Infinite exactly when beyond the largest finite datum -/

/-- **A datum of a format with a largest finite datum is infinite exactly when it is above that
datum or below its negation** (`cmpExact`): a finite datum `m·2^q` has its significand and its
exponent at most the largest one's. -/
theorem tnIsInf_datum {p e : Nat} (hp : 1 ≤ p) (he : 1 ≤ e) {u mx : UnpackedFloat}
    (hd : tnIsDatum p e u = true) (hmx : tnMax? p e = some mx) :
    isInf u = (cmpExact u mx == some .gt || cmpExact u mx.neg == some .lt) := by
  have hpp := tn_pow_pred hp
  have hA : 0 < 2 ^ (p - 1) := Nat.two_pow_pos _
  -- the largest datum `M·2^Q` bounds every finite datum's significand and exponent
  obtain ⟨M, Q, hM, rfl, hb⟩ : ∃ (M : Nat) (Q : Int) (hM : 0 < M), mx = .finite .positive M Q hM ∧
      ∀ (sg : Sign) (m : Nat) (q : Int) (hm : 0 < m), tnIsDatum p e (.finite sg m q hm) = true →
        m ≤ M ∧ q ≤ Q := by
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · have he1 : e = 1 := by omega
      subst he1
      rcases Nat.lt_or_ge p 2 with hp1 | hp2
      · have hp1 : p = 1 := by omega
        subst hp1; rw [tnMax?_one_one] at hmx; cases hmx
      · obtain ⟨h, hx⟩ := tnMax?_subnormal hp2
        rw [hx] at hmx; cases hmx
        refine ⟨_, _, h, rfl, ?_⟩
        intro sg m q hm hdm
        simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq] at hdm
        rcases hdm with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
        · omega
        · simp at h4; omega
    · obtain ⟨h, hx⟩ := tnMax?_normal hp he2
      rw [hx] at hmx; cases hmx
      have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he2
      refine ⟨_, _, h, rfl, ?_⟩
      intro sg m q hm hdm
      simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq] at hdm
      rcases hdm with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
  match u, hd with
  | .notANumber, _ => rfl
  | .infinity .positive, _ => rfl
  | .infinity .negative, _ => rfl
  | .zero sg, _ =>
    obtain ⟨h1, h2⟩ := fu_cmpScaled_zero M Q
    exact fu_within_false h1 h2
  | .finite sg m q hm, hd =>
    obtain ⟨hm1, hq⟩ := hb sg m q hm hd
    have ha : -(M : Int) ≤ sg.apply m ∧ sg.apply m ≤ (M : Int) := by
      cases sg <;> simp only [Sign.apply] <;> omega
    obtain ⟨h1, h2⟩ := fu_cmpScaled_within hq ha
    exact fu_within_false h1 h2

/-! ## The operations of FloatDomain.lean are the formulas at Lean core's rounding -/

theorem held?_eq_heldBy (s : Format) : held? s = heldBy (nearest? s) := rfl
theorem sum?_eq_sumBy (s : Format) : sum? s = sumBy (nearest? s) := rfl
theorem diff?_eq_diffBy (s : Format) : diff? s = diffBy (nearest? s) := rfl
theorem prod?_eq_prodBy (s : Format) : prod? s = prodBy (nearest? s) := rfl
theorem remainder_eq_remainderBy (s : Format) : remainder s = remainderBy (held? s) := rfl
theorem roundToIntegral_eq_By (s : Format) (d : Dir) : roundToIntegral s d = roundToIntegralBy (held? s) d := rfl
theorem convertFormat_eq_convertBy (s : Format) : convertFormat s = convertBy (held? s) := rfl
theorem ofInt?_eq_ofIntBy (s : Format) : ofInt? s = ofIntBy (held? s) := rfl

end KCore.KFloat
