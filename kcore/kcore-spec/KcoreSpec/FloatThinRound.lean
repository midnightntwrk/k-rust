/-
  KCore. The rounding of the formats with a field of 1 (`tnRound`, FloatThin.lean) is the rounding
  to the nearest datum, a tie to the even significand, and has a value on the whole region where the
  text states one. Symbolically in the format `(p, e)`, `p` and `e` positive (a field of 1 is not
  used), from the arithmetic of the data alone.

  A magnitude is counted in units of `2^(−shift)` (`tnMag`): every finite datum `m·2^q` of the
  format has `q + shift ≥ 1` (`tnIsDatum`), so its magnitude is the natural number
  `m·2^(q + shift)`. The distance of the rational `N / D` from a magnitude of `w` units is then
  `|N·2^shift − w·D|`, in units of `2^(−shift) / D` (`tnGap`).

  - `tnRound_nearest`: a result of `tnRound p e sg N D` is a finite datum of the sign `sg`, no datum
    of the format, zero included, is nearer `N / D`, and where a datum of another value is as near,
    the result's significand is even.
  - `tnRound_isSome`: `tnRound p e sg N D` has a value where `N / D` is at most the largest finite
    datum, above half the smallest positive datum (at half of it or below, the nearest datum is zero,
    or at `p = 1` there is a tie) and, at `p = 1`, not halfway between two powers of two.
-/
import KcoreSpec.FloatThinLaws

set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## Magnitudes and distances -/

/-- The magnitude of a zero or finite datum of the format `(p, e)`, in units of `2^(−shift)`:
`m·2^(q + shift)` for `m·2^q`. For a datum of the format `q + shift ≥ 1` (`tnIsDatum`), so the
exponent is not truncated. -/
def tnMag (p e : Nat) : UnpackedFloat → Option Nat
  | .zero _ => some 0
  | .finite _ m q _ => some (m * 2 ^ (q + (shift p e : Int)).toNat)
  | _ => none

/-- `|a − b|`. -/
def tnGap (a b : Nat) : Nat := ((a : Int) - (b : Int)).natAbs

/-! ## Powers of two -/

/-- `N / D < 2^(y − x)` and `y − x ≤ z − t` give `N / D < 2^(z − t)`. -/
theorem tn_scale_lt {N D x y t z : Nat} (h : N * 2 ^ x < D * 2 ^ y) (hz : y + t ≤ z + x) :
    N * 2 ^ t < D * 2 ^ z := by
  apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ x)
  calc N * 2 ^ t * 2 ^ x = N * 2 ^ x * 2 ^ t := Nat.mul_right_comm ..
    _ < D * 2 ^ y * 2 ^ t := (Nat.mul_lt_mul_right (Nat.two_pow_pos t)).2 h
    _ = D * 2 ^ (y + t) := by rw [Nat.mul_assoc, ← Nat.pow_add]
    _ ≤ D * 2 ^ (z + x) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hz)
    _ = D * 2 ^ z * 2 ^ x := by rw [Nat.pow_add, Nat.mul_assoc]

/-- `2^(y − x) ≤ N / D` and `z − t ≤ y − x` give `2^(z − t) ≤ N / D`. -/
theorem tn_scale_le {N D x y t z : Nat} (h : D * 2 ^ y ≤ N * 2 ^ x) (hz : z + x ≤ y + t) :
    D * 2 ^ z ≤ N * 2 ^ t := by
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ x) _ (Nat.two_pow_pos x)
  calc D * 2 ^ z * 2 ^ x = D * 2 ^ (z + x) := by rw [Nat.mul_assoc, ← Nat.pow_add]
    _ ≤ D * 2 ^ (y + t) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hz)
    _ = D * 2 ^ y * 2 ^ t := by rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ N * 2 ^ x * 2 ^ t := Nat.mul_le_mul_right _ h
    _ = N * 2 ^ t * 2 ^ x := Nat.mul_right_comm ..

/-- `tnLog N D` is the `k` with `2^k ≤ N / D < 2^(k+1)`. -/
theorem tnLog_spec {N D : Nat} (hN : 0 < N) (hD : 0 < D) :
    D * 2 ^ (tnLog N D).toNat ≤ N * 2 ^ (-(tnLog N D)).toNat ∧
      N * 2 ^ (-(tnLog N D + 1)).toNat < D * 2 ^ (tnLog N D + 1).toNat := by
  unfold tnLog
  dsimp only
  have a1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hN)
  have a2 := Nat.lt_log2_self (n := N)
  have b1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hD)
  have b2 := Nat.lt_log2_self (n := D)
  generalize Nat.log2 N = a at a1 a2 ⊢
  generalize Nat.log2 D = b at b1 b2 ⊢
  -- `N / D < 2^(a + 1 − b)` and `2^(a − b − 1) < N / D`
  have hub : N * 2 ^ b < D * 2 ^ (a + 1) :=
    Nat.lt_of_lt_of_le ((Nat.mul_lt_mul_right (Nat.two_pow_pos b)).2 a2)
      (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ b1)
  have hlb : D * 2 ^ a ≤ N * 2 ^ (b + 1) :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le ((Nat.mul_lt_mul_right (Nat.two_pow_pos a)).2 b2)
      (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ a1))
  split
  · rename_i h
    exact ⟨h, tn_scale_lt hub (by omega)⟩
  · rename_i h
    refine ⟨tn_scale_le hlb (by omega), ?_⟩
    rw [Int.sub_add_cancel]
    exact Nat.lt_of_not_ge h

/-! ## The nearest integer -/

/-- The integer nearest `A / B` is the one nearest `(A·c) / (B·c)`. -/
theorem tnNearInt_scale (ev : Bool) (A B : Nat) {c : Nat} (hc : 0 < c) :
    tnNearInt ev (A * c) (B * c) = tnNearInt ev A B := by
  unfold tnNearInt
  rw [Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right]
  have h1 : 2 * (A % B * c) < B * c ↔ 2 * (A % B) < B := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  have h2 : B * c < 2 * (A % B * c) ↔ B < 2 * (A % B) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_right hc
  simp only [h1, h2]

/-- A result `n` of `tnNearInt` is within a half of `A / B`, and where it is a half away, `even` is
set and `n` is even. -/
theorem tnNearInt_spec {ev : Bool} {A B n : Nat} (hB : 0 < B) (h : tnNearInt ev A B = some n) :
    2 * (n * B) ≤ 2 * A + B ∧ 2 * A ≤ 2 * (n * B) + B ∧
      ((2 * (n * B) = 2 * A + B ∨ 2 * A = 2 * (n * B) + B) → ev = true ∧ n % 2 = 0) := by
  have hdm := Nat.div_add_mod A B
  have hlt := Nat.mod_lt A hB
  unfold tnNearInt at h
  generalize A / B = t at h hdm
  generalize A % B = r at h hdm hlt
  have e0 : t * B = B * t := Nat.mul_comm ..
  have e1 : (t + 1) * B = B * t + B := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
  split at h
  · cases h; rw [e0]
    exact ⟨by omega, by omega, fun hh => by exfalso; omega⟩
  · split at h
    · cases h; rw [e1]
      exact ⟨by omega, by omega, fun hh => by exfalso; omega⟩
    · split at h
      · rename_i hev
        have hn : (n = t ∧ t % 2 = 0) ∨ (n = t + 1 ∧ t % 2 = 1) := by
          simp only [Option.some.injEq] at h
          split at h <;> omega
        rcases hn with ⟨hn, ht⟩ | ⟨hn, ht⟩
        · rw [hn, e0]; exact ⟨by omega, by omega, fun _ => ⟨hev, by omega⟩⟩
        · rw [hn, e1]; exact ⟨by omega, by omega, fun _ => ⟨hev, by omega⟩⟩
      · cases h

/-- `tnNearInt` has a value where `even` is set or `A / B` is not halfway between two integers. -/
theorem tnNearInt_isSome {ev : Bool} {A B : Nat} (h : ev = true ∨ 2 * (A % B) ≠ B) :
    (tnNearInt ev A B).isSome = true := by
  unfold tnNearInt
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i h1 h2 h3
        rcases h with h | h
        · exact absurd h h3
        · omega

/-- An integer `n` within a half of `U / V` is at least as near it as any integer `j`, and where
another integer is as near, `U / V` is a half away from `n`. -/
theorem tn_near_mul {U V n : Nat} (h1 : 2 * (n * V) ≤ 2 * U + V) (h2 : 2 * U ≤ 2 * (n * V) + V)
    (j : Nat) :
    tnGap U (n * V) ≤ tnGap U (j * V) ∧
      (tnGap U (n * V) = tnGap U (j * V) → j ≠ n →
        2 * (n * V) = 2 * U + V ∨ 2 * U = 2 * (n * V) + V) := by
  unfold tnGap
  rcases Nat.lt_trichotomy j n with h | h | h
  · have hm : (j + 1) * V ≤ n * V := Nat.mul_le_mul_right V h
    rw [Nat.add_mul, Nat.one_mul] at hm
    generalize n * V = X at *
    generalize j * V = Y at *
    omega
  · subst h
    exact ⟨Nat.le_refl _, fun _ hne => absurd rfl hne⟩
  · have hm : (n + 1) * V ≤ j * V := Nat.mul_le_mul_right V h
    rw [Nat.add_mul, Nat.one_mul] at hm
    generalize n * V = X at *
    generalize j * V = Y at *
    omega

/-! ## The rounding, in units of `2^(−shift)` -/

theorem tnMk?_eq_some {p e : Nat} {sg : Sign} {m : Nat} {q : Int} {u : UnpackedFloat}
    (h : tnMk? p e sg m q = some u) :
    ∃ hm, u = .finite sg m q hm ∧ tnIsDatum p e (.finite sg m q hm) = true := by
  unfold tnMk? at h
  split at h
  · rename_i hm
    split at h
    · rename_i hd
      cases h
      exact ⟨hm, rfl, hd⟩
    · cases h
  · cases h

/-- `tnRound` with the exponent `q` of its last digit named, `q + shift = QS ≥ 1`: the significand
is the integer nearest `N / D` counted in the `2^QS` units of that digit; `N / D` is below
`2^p` of them, and at least `2^(p−1)` of them where `q` is above the format's smallest exponent. -/
theorem tnRound_units {p e : Nat} (sg : Sign) {N D : Nat} (hp : 1 ≤ p) (hN : 0 < N) (hD : 0 < D) :
    ∃ (q : Int) (QS : Nat), (QS : Int) = q + (shift p e : Int) ∧ 1 ≤ QS ∧
      tnRound p e sg N D =
        ((tnNearInt (decide (2 ≤ p)) (N * 2 ^ shift p e) (2 ^ QS * D)).bind fun n =>
          if n = 2 ^ p then tnMk? p e sg (2 ^ (p - 1)) (q + 1) else tnMk? p e sg n q) ∧
      N * 2 ^ shift p e < 2 ^ p * (2 ^ QS * D) ∧
      (2 ≤ QS → 2 ^ (p - 1) * (2 ^ QS * D) ≤ N * 2 ^ shift p e) := by
  obtain ⟨hl1, hl2⟩ := tnLog_spec hN hD
  unfold tnRound
  dsimp only
  generalize shift p e = S
  generalize tnLog N D = k at hl1 hl2
  have hq1 : 1 - (S : Int) ≤ max (k - ((p - 1 : Nat) : Int)) (1 - (S : Int)) := Int.le_max_right ..
  have hq2 : k - ((p - 1 : Nat) : Int) ≤ max (k - ((p - 1 : Nat) : Int)) (1 - (S : Int)) :=
    Int.le_max_left ..
  have hq3 : 1 - (S : Int) < max (k - ((p - 1 : Nat) : Int)) (1 - (S : Int)) →
      max (k - ((p - 1 : Nat) : Int)) (1 - (S : Int)) = k - ((p - 1 : Nat) : Int) := by omega
  generalize max (k - ((p - 1 : Nat) : Int)) (1 - (S : Int)) = q at hq1 hq2 hq3
  refine ⟨q, (q + (S : Int)).toNat, by omega, by omega, ?_, ?_, ?_⟩
  · have ea : (-q).toNat + (S - (-q).toNat) = S := by omega
    have eb : q.toNat + (S - (-q).toNat) = (q + (S : Int)).toNat := by omega
    have hA : N * 2 ^ S = N * 2 ^ (-q).toNat * 2 ^ (S - (-q).toNat) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, ea]
    have hB : 2 ^ (q + (S : Int)).toNat * D = D * 2 ^ q.toNat * 2 ^ (S - (-q).toNat) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, eb, Nat.mul_comm]
    rw [hA, hB, tnNearInt_scale _ _ _ (Nat.two_pow_pos _)]
  · have h := tn_scale_lt (t := S) (z := p + (q + (S : Int)).toNat) hl2 (by omega)
    have e : 2 ^ p * (2 ^ (q + (S : Int)).toNat * D) = D * 2 ^ (p + (q + (S : Int)).toNat) := by
      rw [Nat.pow_add]; ac_rfl
    rw [e]; exact h
  · intro h2
    have hq : q = k - ((p - 1 : Nat) : Int) := hq3 (by omega)
    have h := tn_scale_le (t := S) (z := (p - 1) + (q + (S : Int)).toNat) hl1 (by omega)
    have e : 2 ^ (p - 1) * (2 ^ (q + (S : Int)).toNat * D) =
        D * 2 ^ ((p - 1) + (q + (S : Int)).toNat) := by
      rw [Nat.pow_add]; ac_rfl
    rw [e]; exact h

/-! ## The result is a nearest datum, a tie to the even significand -/

/-- A result of `tnRound p e sg N D` is a finite datum `m·2^q` of the sign `sg` such that no zero or
finite datum `d` of the format is nearer `N / D`; and where a datum of another value is as near,
`m` is even. -/
theorem tnRound_nearest {p e : Nat} {sg : Sign} {N D : Nat} {u : UnpackedFloat} (hp : 1 ≤ p)
    (hN : 0 < N) (hD : 0 < D) (h : tnRound p e sg N D = some u) :
    ∃ m q hm, u = .finite sg m q hm ∧ ∀ d w, tnIsDatum p e d = true → tnMag p e d = some w →
      tnGap (N * 2 ^ shift p e) (m * 2 ^ (q + (shift p e : Int)).toNat * D) ≤
          tnGap (N * 2 ^ shift p e) (w * D) ∧
        (tnGap (N * 2 ^ shift p e) (m * 2 ^ (q + (shift p e : Int)).toNat * D) =
            tnGap (N * 2 ^ shift p e) (w * D) →
          w ≠ m * 2 ^ (q + (shift p e : Int)).toNat → m % 2 = 0) := by
  obtain ⟨q, QS, hQS, hQ1, hr, hup, hlo⟩ := tnRound_units (p := p) (e := e) sg hp hN hD
  rw [hr, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, h⟩ := h
  have hV : 0 < 2 ^ QS * D := Nat.mul_pos (Nat.two_pow_pos _) hD
  obtain ⟨s1, s2, s3⟩ := tnNearInt_spec hV hn
  have hpp := tn_pow_pred hp
  -- the result is `n` units of the last digit, and its significand is even where `n` is
  have hres : ∃ m q' hm, u = .finite sg m q' hm ∧
      m * 2 ^ (q' + (shift p e : Int)).toNat = n * 2 ^ QS ∧ (n % 2 = 0 → 2 ≤ p → m % 2 = 0) := by
    split at h
    · rename_i hnp
      obtain ⟨hm, rfl, -⟩ := tnMk?_eq_some h
      refine ⟨_, _, hm, rfl, ?_, fun _ hp2 => ?_⟩
      · have e1 : (q + 1 + (shift p e : Int)).toNat = QS + 1 := by omega
        rw [e1, hnp, Nat.pow_succ, hpp]; ac_rfl
      · have := tn_pow_pred (show 1 ≤ p - 1 by omega)
        omega
    · obtain ⟨hm, rfl, -⟩ := tnMk?_eq_some h
      refine ⟨_, _, hm, rfl, ?_, fun hev _ => hev⟩
      have e1 : (q + (shift p e : Int)).toNat = QS := by omega
      rw [e1]
  obtain ⟨m, q', hm, rfl, hmag, heven⟩ := hres
  refine ⟨m, q', hm, rfl, fun d w hd hw => ?_⟩
  rw [hmag, Nat.mul_assoc]
  generalize hU : N * 2 ^ shift p e = U at *
  generalize hVV : 2 ^ QS * D = V at *
  -- a datum that is `j` units of the last digit
  have hmul : ∀ j, w = j * 2 ^ QS →
      tnGap U (n * V) ≤ tnGap U (w * D) ∧
        (tnGap U (n * V) = tnGap U (w * D) → w ≠ n * 2 ^ QS → m % 2 = 0) := by
    intro j hj
    have hwD : w * D = j * V := by rw [hj, Nat.mul_assoc, hVV]
    rw [hwD]
    obtain ⟨t1, t2⟩ := tn_near_mul s1 s2 j
    refine ⟨t1, fun heq hne => ?_⟩
    have hjn : j ≠ n := fun hjn => hne (by rw [hj, hjn])
    obtain ⟨hev, hn2⟩ := s3 (t2 heq hjn)
    exact heven hn2 (of_decide_eq_true hev)
  cases d with
  | notANumber => simp [tnMag] at hw
  | infinity sg' => simp [tnMag] at hw
  | zero sg' =>
    simp only [tnMag, Option.some.injEq] at hw
    exact hmul 0 (by rw [← hw, Nat.zero_mul])
  | finite sg' m' q'' hm' =>
    simp only [tnMag, Option.some.injEq] at hw
    simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq] at hd
    have hq'' : 1 - (shift p e : Int) ≤ q'' := by omega
    have hm2 : m' < 2 ^ p := by omega
    by_cases hqq : q ≤ q''
    · refine hmul (m' * 2 ^ (q'' - q).toNat) ?_
      have e1 : (q'' + (shift p e : Int)).toNat = (q'' - q).toNat + QS := by omega
      rw [← hw, e1, Nat.pow_add, Nat.mul_assoc]
    · -- a datum of a lower exponent is below `2^(p−1)` units of the last digit, which `N / D` is not
      have hlo' := hlo (by omega)
      obtain ⟨t1, -⟩ := tn_near_mul s1 s2 (2 ^ (p - 1))
      have e1 : QS = (q'' + (shift p e : Int)).toNat + 1 + (QS - ((q'' + (shift p e : Int)).toNat + 1)) := by omega
      have hpw : 2 ^ ((q'' + (shift p e : Int)).toNat + 1) ≤ 2 ^ QS :=
        Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at hpw
      have hwlt : w * D < 2 ^ (p - 1) * V := by
        rw [← hVV, ← Nat.mul_assoc]
        apply (Nat.mul_lt_mul_right hD).2
        rw [← hw]
        calc m' * 2 ^ (q'' + (shift p e : Int)).toNat
            < 2 ^ p * 2 ^ (q'' + (shift p e : Int)).toNat := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hm2
          _ = 2 ^ (p - 1) * (2 ^ (q'' + (shift p e : Int)).toNat * 2) := by rw [hpp]; ac_rfl
          _ ≤ 2 ^ (p - 1) * 2 ^ QS := Nat.mul_le_mul_left _ hpw
      unfold tnGap at t1 ⊢
      generalize 2 ^ (p - 1) * V = HV at *
      generalize n * V = X at *
      generalize w * D = Y at *
      omega

/-! ## The rounding has a value on the stated region -/

/-- `tnRound p e sg N D` has a value on the region where the text states one: `N / D` is at most
the largest finite datum of the format, of `W` units; it is above half the smallest positive datum,
which is 2 units (at half of it or below, the nearest datum is zero, or zero is as near); and at
`p = 1`, where a tie has no even significand to go to, it is not halfway between `2^x` and
`2^(x+1)` for an exponent `x` of the format (`X = x + shift ≥ 1`). -/
theorem tnRound_isSome {p e : Nat} {sg : Sign} {N D W : Nat} (hp : 1 ≤ p) (he : 1 ≤ e) (hD : 0 < D)
    (hW : (tnMax? p e).bind (tnMag p e) = some W)
    (hle : N * 2 ^ shift p e ≤ W * D) (hlo : D < N * 2 ^ shift p e)
    (htie : p = 1 → ∀ X, 1 ≤ X → 2 * (N * 2 ^ shift p e) ≠ 3 * 2 ^ X * D) :
    (tnRound p e sg N D).isSome = true := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; rw [Nat.zero_mul] at hlo; omega
    · exact h
  have hpp := tn_pow_pred hp
  have hH : 0 < 2 ^ (p - 1) := Nat.two_pow_pos _
  -- the largest finite datum, in units
  have hWv : (2 ≤ e ∧ W = (2 ^ p - 1) * 2 ^ (2 ^ e - 2)) ∨ (e = 1 ∧ 2 ≤ p ∧ W = (2 ^ (p - 1) - 1) * 2) := by
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · have he1 : e = 1 := by omega
      subst he1
      rcases Nat.lt_or_ge p 2 with hp1 | hp2
      · have hp1 : p = 1 := by omega
        subst hp1
        rw [tnMax?_one_one] at hW
        cases hW
      · obtain ⟨h0, hm⟩ := tnMax?_subnormal hp2
        have e1 : (1 - (shift p 1 : Int) + (shift p 1 : Int)).toNat = 1 := by omega
        rw [hm] at hW
        simp only [Option.bind_some, tnMag, e1, Option.some.injEq, Nat.pow_one] at hW
        exact Or.inr ⟨rfl, hp2, hW.symm⟩
    · obtain ⟨h0, hm⟩ := tnMax?_normal hp he2
      have e1 : (((2 ^ e - 2 : Nat) : Int) - (shift p e : Int) + (shift p e : Int)).toNat = 2 ^ e - 2 := by
        omega
      rw [hm] at hW
      simp only [Option.bind_some, tnMag, e1, Option.some.injEq] at hW
      exact Or.inl ⟨he2, hW.symm⟩
  obtain ⟨q, QS, hQS, hQ1, hr, hup, hlow⟩ := tnRound_units (p := p) (e := e) sg hp hN hD
  have hG2 : 2 ^ 1 ≤ 2 ^ QS := Nat.pow_le_pow_right (by decide) hQ1
  have hGq : QS = 1 → 2 ^ QS = 2 := fun h => by rw [h]
  have hE : 2 ≤ e → 2 ≤ 2 ^ e - 2 := fun he2 => by
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he2
    omega
  have hEpow : ∀ x, 2 ^ e - 2 + x ≤ QS → 2 ^ (2 ^ e - 2) * 2 ^ x ≤ 2 ^ QS := fun x hx => by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hx
  have hTE : 0 < 2 ^ (2 ^ e - 2) := Nat.two_pow_pos _
  generalize 2 ^ (2 ^ e - 2) = TE at hWv hEpow hTE
  generalize hSdef : shift p e = S at *
  generalize hGdef : 2 ^ QS = G at *
  generalize hU : N * 2 ^ S = U at *
  generalize hHdef : 2 ^ (p - 1) = H at *
  have hV : 0 < G * D := Nat.mul_pos (by omega) hD
  -- the significand's rounding has a value
  have hsome : (tnNearInt (decide (2 ≤ p)) U (G * D)).isSome = true := by
    apply tnNearInt_isSome
    by_cases hp2 : 2 ≤ p
    · exact Or.inl (decide_eq_true hp2)
    · right
      intro htie'
      have hp1 : p = 1 := by omega
      have hdm := Nat.div_add_mod U (G * D)
      have ht : U / (G * D) ≤ 1 := by
        apply Nat.le_of_lt_succ
        apply Nat.lt_of_not_ge
        intro h2
        have := Nat.mul_le_mul_left (G * D) h2
        rw [hp1] at hup
        omega
      rcases Nat.eq_zero_or_pos (U / (G * D)) with h0 | h1
      · rw [h0, Nat.mul_zero] at hdm
        rcases Nat.lt_or_ge QS 2 with hq | hq
        · have hG := hGq (by omega)
          subst hG
          omega
        · have h := hlow hq
          have := Nat.le_mul_of_pos_left (G * D) (show 0 < H by omega)
          omega
      · have h1 : U / (G * D) = 1 := by omega
        rw [h1, Nat.mul_one] at hdm
        refine htie hp1 QS hQ1 ?_
        rw [hGdef, Nat.mul_assoc]
        omega
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨s1, s2, -⟩ := tnNearInt_spec hV hn
  rw [hr, hn]
  simp only [Option.bind_some]
  -- `n ≤ 2^p`
  have hnP : n ≤ 2 ^ p := by
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_not_ge
    intro h2
    have := Nat.mul_le_mul_right (G * D) h2
    rw [Nat.succ_mul] at this
    omega
  -- `1 ≤ n`
  have hn1 : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at s2
    rcases Nat.lt_or_ge QS 2 with hq | hq
    · have hG := hGq (by omega)
      subst hG
      omega
    · have h := hlow hq
      have := Nat.le_mul_of_pos_left (G * D) (show 0 < H by omega)
      omega
  -- `(2n − 1)·G ≤ 2·W`: `N / D` is at least `n − 1/2` units of the last digit and at most `W`
  have K1 : 2 * (n * G) ≤ 2 * W + G := by
    have e1 : 2 * (n * G) * D = 2 * (n * (G * D)) := by simp only [Nat.mul_assoc]
    have e2 : (2 * W + G) * D = 2 * (W * D) + G * D := by rw [Nat.add_mul, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_right (c := D) (by omega) hD
  -- `2^(p−1)·G ≤ W` where the last digit is above the smallest exponent
  have K2 : 2 ≤ QS → H * G ≤ W := fun hq => by
    have h := hlow hq
    rw [← Nat.mul_assoc] at h
    exact Nat.le_of_mul_le_mul_right (c := D) (by omega) hD
  have hPG : (2 ^ p - 1) * G = 2 ^ p * G - G := by rw [Nat.sub_mul, Nat.one_mul]
  have hPT : (2 ^ p - 1) * TE = 2 ^ p * TE - TE := by rw [Nat.sub_mul, Nat.one_mul]
  have hGle : G ≤ 2 ^ p * G := Nat.le_mul_of_pos_left G (by omega)
  have hTle : TE ≤ 2 ^ p * TE := Nat.le_mul_of_pos_left TE (by omega)
  split
  · -- the significand `2^p` is `2^(p−1)` at the next exponent
    rename_i hnp
    rw [hnp] at K1
    have hd : tnIsDatum p e (.finite sg H (q + 1) (by omega)) = true := by
      simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
      right
      rw [hSdef, hHdef]
      refine ⟨Nat.le_refl _, by omega, by omega, ?_⟩
      rcases hWv with ⟨he2, hWe⟩ | ⟨he1, hp2, hWe⟩
      · have hlt : QS < 2 ^ e - 2 := by
          apply Nat.lt_of_not_ge
          intro hge
          have h1 := hEpow 0 (by omega)
          have h2 := Nat.mul_le_mul_left (2 ^ p - 1) h1
          rw [Nat.pow_zero, Nat.mul_one, hPG] at h2
          rw [hWe] at K1
          omega
        omega
      · exfalso
        have h1 := Nat.mul_le_mul_left (2 ^ p) (show 2 ≤ G by omega)
        rw [hWe] at K1
        omega
    rw [tnMk?_of sg hH hd]
    rfl
  · rename_i hnp
    have hd : tnIsDatum p e (.finite sg n q hn1) = true := by
      simp only [tnIsDatum, Bool.or_eq_true, decide_eq_true_eq]
      rw [hSdef, hHdef]
      rcases Nat.lt_or_ge n H with hnH | hnH
      · -- below `2^(p−1)`: the last digit is at the smallest exponent
        left
        refine ⟨hnH, ?_⟩
        have hq : QS < 2 := by
          apply Nat.lt_of_not_ge
          intro hq
          have h := hlow hq
          have := Nat.mul_le_mul_right (G * D) (show n + 1 ≤ H from hnH)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        omega
      · right
        refine ⟨hnH, by omega, by omega, ?_⟩
        have hHn := Nat.mul_le_mul_right G hnH
        rcases hWv with ⟨he2, hWe⟩ | ⟨he1, hp2, hWe⟩
        · have hle' : QS ≤ 2 ^ e - 2 := by
            apply Nat.le_of_not_gt
            intro hgt
            have hE2 := hE he2
            have h := K2 (by omega)
            have h1 := hEpow 1 (by omega)
            have h2 := Nat.mul_le_mul_left H h1
            have e3 : H * (TE * 2 ^ 1) = 2 ^ p * TE := by rw [hpp, Nat.pow_one]; ac_rfl
            rw [e3] at h2
            rw [hWe, hPT] at h
            omega
          omega
        · exfalso
          have h1 := Nat.mul_le_mul_left (2 * H - 1) (show 2 ≤ G by omega)
          have e3 : (2 * H - 1) * G = 2 * (H * G) - G := by rw [Nat.sub_mul, Nat.one_mul, Nat.mul_assoc]
          have hGH : G ≤ H * G := Nat.le_mul_of_pos_left G (by omega)
          rw [e3] at h1
          rw [hWe] at K1
          omega
    rw [tnMk?_of sg hn1 hd]
    rfl

end KCore.KFloat
