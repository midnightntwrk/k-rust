/-
  KCore. A Float literal's text determines it (`KFloat.text_inj`): two literals with data (`ok`)
  and one text are one literal. The text is the format's suffix after the datum's decimal value,
  `Infinity` or `NaN` (FloatDomain.lean); the proof reads the format back from the suffix and the
  encoding from the value: a finite value fixes the exponent field and the significand field, and
  a format has one NaN encoding.
-/
import KcoreSpec.FloatDomain
import KcoreSpec.SubjectReduction

set_option autoImplicit false

namespace KCore.KFloat

open Float.Model Float.Model.UnpackedFloat

/-! ## Lists of characters -/

theorem append_sep_inj {c : Char} : ∀ {a a' r r' : List Char}, c ∉ a → c ∉ a' →
    a ++ c :: r = a' ++ c :: r' → a = a' ∧ r = r'
  | [], [], _, _, _, _, h => by simpa using h
  | [], d :: a', _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | d :: a, [], _, _, h₁, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₁
  | d :: a, d' :: a', _, _, h₁, h', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨h1, h2⟩ := append_sep_inj (fun hm => h₁ (List.mem_cons_of_mem _ hm))
      (fun hm => h' (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [h1], h2⟩

theorem toDigits_inj {n m : Nat} (h : Nat.toDigits 10 n = Nat.toDigits 10 m) : n = m := by
  have := digitsVal_toDigits n
  rw [h, digitsVal_toDigits m] at this
  exact (Option.some.inj this).symm

theorem digit_of_mem {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem repr_toList (n : Nat) : (Nat.repr n).toList = Nat.toDigits 10 n := by
  simp only [Nat.repr_eq_ofList_toDigits, String.toList_ofList]

/-! ## Reading a body back -/

/-- What a literal's text says before its suffix. -/
inductive BV where
  | nan
  | inf (neg : Bool)
  | int (neg : Bool) (n : Nat)
  | dec (neg : Bool) (n k : Nat)
  deriving DecidableEq

def unsignedVal (l : List Char) (ng : Bool) : Option BV :=
  if l = "Infinity".toList then some (.inf ng) else
  match digitsVal (l.takeWhile Char.isDigit) 0, l.dropWhile Char.isDigit with
  | some n, ['.', '0'] => some (.int ng n)
  | some n, 'e' :: '-' :: ks => (digitsVal ks 0).map fun k => .dec ng n k
  | _, _ => none

def bodyVal (l : List Char) : Option BV :=
  if l = "NaN".toList then some .nan else
  match l with
  | '-' :: r => unsignedVal r true
  | r => unsignedVal r false

/-- The body of `text` (before `p`). -/
def body (p e b : Nat) : String :=
  let sign := if (fields p e b).1 = 0 then "" else "-"
  if 2 ^ (p + e) ≤ b then "NaN"
  else if (fields p e b).2.1 = 2 ^ e - 1 then (if (fields p e b).2.2 = 0 then sign ++ "Infinity" else "NaN")
  else sign ++ magText p e (fields p e b).2.1 (fields p e b).2.2

theorem text_eq (p e b : Nat) :
    (text p e b).toList = (body p e b).toList ++ 'p' :: (Nat.toDigits 10 p ++ 'x' :: Nat.toDigits 10 e) := by
  simp only [text, body, String.toList_append, repr_toList, List.append_assoc]
  rfl

/-- The value of a zero or finite datum `magText` writes. -/
def magVal (p e x f : Nat) (ng : Bool) : BV :=
  if sig p x f = 0 then .int ng 0
  else if shift p e ≤ expo x then .int ng (sig p x f * 2 ^ (expo x - shift p e))
  else .dec ng (sig p x f * 5 ^ (shift p e - expo x)) (shift p e - expo x)

/-- The value `body` writes. -/
def bv (p e b : Nat) : BV :=
  if 2 ^ (p + e) ≤ b then .nan
  else if (fields p e b).2.1 = 2 ^ e - 1 then (if (fields p e b).2.2 = 0 then .inf ((fields p e b).1 != 0) else .nan)
  else magVal p e (fields p e b).2.1 (fields p e b).2.2 ((fields p e b).1 != 0)

theorem takeWhile_digits (n : Nat) (c : Char) (r : List Char) (hc : c.isDigit = false) :
    (Nat.toDigits 10 n ++ c :: r).takeWhile Char.isDigit = Nat.toDigits 10 n ∧
    (Nat.toDigits 10 n ++ c :: r).dropWhile Char.isDigit = c :: r := by
  have hall : ∀ a ∈ Nat.toDigits 10 n, a.isDigit = true := fun a h => digit_of_mem h
  constructor
  · rw [List.takeWhile_append_of_pos hall]
    simp [hc]
  · rw [List.dropWhile_append_of_pos hall]
    simp [hc]

theorem digits_head (n : Nat) (r : List Char) : ∃ d r', Nat.toDigits 10 n ++ r = d :: r' ∧ d.isDigit = true := by
  obtain ⟨d, ds, he, -, -⟩ := toDigits_head n
  exact ⟨d, ds ++ r, by rw [he]; rfl, digit_of_mem (he ▸ List.mem_cons_self)⟩

theorem ne_of_head {l l' : List Char} (hl : ∃ d r, l = d :: r ∧ d.isDigit = true)
    (hl' : ∃ d r, l' = d :: r ∧ d.isDigit = false) : l ≠ l' := by
  obtain ⟨d, r, rfl, hd⟩ := hl
  obtain ⟨d', r', rfl, hd'⟩ := hl'
  intro h; simp only [List.cons.injEq] at h; rw [h.1] at hd; rw [hd] at hd'; cases hd'

theorem infinity_head : ∃ d r, "Infinity".toList = d :: r ∧ d.isDigit = false := ⟨'I', _, rfl, by decide⟩

theorem unsignedVal_int (n : Nat) (ng : Bool) :
    unsignedVal (Nat.toDigits 10 n ++ ['.', '0']) ng = some (.int ng n) := by
  unfold unsignedVal
  rw [if_neg (ne_of_head (digits_head n _) infinity_head)]
  obtain ⟨h1, h2⟩ := takeWhile_digits n '.' ['0'] (by decide)
  rw [h1, h2, digitsVal_toDigits]
  rfl

theorem unsignedVal_dec (n k : Nat) (ng : Bool) :
    unsignedVal (Nat.toDigits 10 n ++ 'e' :: '-' :: Nat.toDigits 10 k) ng = some (.dec ng n k) := by
  unfold unsignedVal
  rw [if_neg (ne_of_head (digits_head n _) infinity_head)]
  obtain ⟨h1, h2⟩ := takeWhile_digits n 'e' ('-' :: Nat.toDigits 10 k) (by decide)
  rw [h1, h2, digitsVal_toDigits]
  simp [digitsVal_toDigits]

theorem magText_toList (p e x f : Nat) :
    (magText p e x f).toList =
      if sig p x f = 0 then Nat.toDigits 10 0 ++ ['.', '0']
      else if shift p e ≤ expo x then Nat.toDigits 10 (sig p x f * 2 ^ (expo x - shift p e)) ++ ['.', '0']
      else Nat.toDigits 10 (sig p x f * 5 ^ (shift p e - expo x)) ++ 'e' :: '-' :: Nat.toDigits 10 (shift p e - expo x) := by
  unfold magText
  split
  · simp only [String.toList_append, repr_toList]; rfl
  · split
    · simp only [String.toList_append, repr_toList]; rfl
    · simp only [String.toList_append, repr_toList, List.append_assoc]; rfl

theorem unsignedVal_mag (p e x f : Nat) (ng : Bool) :
    unsignedVal (magText p e x f).toList ng = some (magVal p e x f ng) := by
  rw [magText_toList]
  unfold magVal
  split
  · exact unsignedVal_int 0 ng
  · split
    · exact unsignedVal_int _ ng
    · exact unsignedVal_dec _ _ ng

theorem mag_head (p e x f : Nat) : ∃ d r, (magText p e x f).toList = d :: r ∧ d.isDigit = true := by
  rw [magText_toList]
  split
  · exact digits_head _ _
  · split
    · exact digits_head _ _
    · exact digits_head _ _

theorem bodyVal_neg (r : List Char) : bodyVal ('-' :: r) = unsignedVal r true := by
  unfold bodyVal
  rw [if_neg (by intro h; cases h)]
  rfl

theorem bodyVal_pos {r : List Char} (hd : ∃ d r', r = d :: r' ∧ (d = '-' → False) ∧ (d = 'N' → False)) :
    bodyVal r = unsignedVal r false := by
  obtain ⟨d, r', rfl, h1, h2⟩ := hd
  unfold bodyVal
  rw [if_neg (by intro h; simp only [show "NaN".toList = ['N', 'a', 'N'] from rfl, List.cons.injEq] at h; exact h2 h.1)]
  split
  · rename_i h; simp only [List.cons.injEq] at h; exact (h1 h.1).elim
  · rfl

theorem bodyVal_body (p e b : Nat) : bodyVal (body p e b).toList = some (bv p e b) := by
  unfold body bv
  by_cases hN : 2 ^ (p + e) ≤ b
  · simp only [hN, ↓reduceIte]; simp [bodyVal]
  simp only [hN, ↓reduceIte]
  generalize (fields p e b).1 = sg
  generalize (fields p e b).2.1 = x
  generalize (fields p e b).2.2 = f
  try dsimp only
  by_cases hx : x = 2 ^ e - 1
  · rw [if_pos hx, if_pos hx]
    by_cases hf : f = 0
    · rw [if_pos hf, if_pos hf]
      by_cases hs : sg = 0
      · rw [if_pos hs, String.empty_append, bodyVal_pos (r := "Infinity".toList) ⟨'I', _, rfl, by decide, by decide⟩]
        simp [unsignedVal, hs]
      · rw [if_neg hs, String.toList_append, show "-".toList = ['-'] from rfl, List.singleton_append, bodyVal_neg]
        simp [unsignedVal, hs]
    · rw [if_neg hf, if_neg hf]
      simp [bodyVal]
  · rw [if_neg hx, if_neg hx]
    obtain ⟨d, r, hdr, hd⟩ := mag_head p e x f
    by_cases hs : sg = 0
    · rw [if_pos hs, String.empty_append, bodyVal_pos, unsignedVal_mag]
      · have : (sg != 0) = false := by simp [hs]
        rw [this]
      · refine ⟨d, r, hdr, ?_, ?_⟩ <;> (intro h; rw [h] at hd; exact absurd hd (by decide))
    · rw [if_neg hs, String.toList_append, show "-".toList = ['-'] from rfl, List.singleton_append, bodyVal_neg,
        unsignedVal_mag]
      have : (sg != 0) = true := by simp [hs]
      rw [this]

/-! ## The encoding from its fields -/

theorem fields_eq {p e b : Nat} (_hb : b < 2 ^ (1 + e + (p - 1))) :
    b = (fields p e b).1 * 2 ^ (p - 1 + e) + (fields p e b).2.1 * 2 ^ (p - 1) + (fields p e b).2.2 := by
  simp only [fields]
  have h3 : b / 2 ^ (p - 1 + e) = b / 2 ^ (p - 1) / 2 ^ e := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [h3, Nat.pow_add]
  have h1 := Nat.div_add_mod b (2 ^ (p - 1))
  generalize b / 2 ^ (p - 1) = q at h1 ⊢
  generalize b % 2 ^ (p - 1) = r at h1 ⊢
  have h2 := Nat.div_add_mod q (2 ^ e)
  generalize q / 2 ^ e = A at h2 ⊢
  generalize q % 2 ^ e = B at h2 ⊢
  generalize 2 ^ (p - 1) = P at h1 ⊢
  generalize 2 ^ e = E at h2 ⊢
  subst h2 h1
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]

/-- Two encodings with the same fields are one. -/
theorem eq_of_fields {p e b b' : Nat} (hb : b < 2 ^ (1 + e + (p - 1))) (hb' : b' < 2 ^ (1 + e + (p - 1)))
    (h : fields p e b = fields p e b') : b = b' := by
  rw [fields_eq hb, fields_eq hb', h]

theorem field_bounds (p e b : Nat) (hb : b < 2 ^ (1 + e + (p - 1))) :
    (fields p e b).1 < 2 ∧ (fields p e b).2.1 < 2 ^ e ∧ (fields p e b).2.2 < 2 ^ (p - 1) := by
  refine ⟨?_, Nat.mod_lt _ (Nat.two_pow_pos _), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  simp only [fields]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_succ']
  have : 1 + e + (p - 1) = (p - 1 + e).succ := by omega
  rwa [this] at hb

/-- A significand times a power of two, the significand of `p` bits, fixes both. -/
theorem mul_pow_inj {p M M' j j' : Nat} (hM : 2 ^ (p - 1) ≤ M) (hM2 : M < 2 * 2 ^ (p - 1))
    (hM' : 2 ^ (p - 1) ≤ M') (hM2' : M' < 2 * 2 ^ (p - 1)) (h : M * 2 ^ j = M' * 2 ^ j') :
    j = j' ∧ M = M' := by
  have key : ∀ {M M' j j' : Nat}, 2 ^ (p - 1) ≤ M' → M < 2 * 2 ^ (p - 1) → M * 2 ^ j = M' * 2 ^ j' → ¬ j < j' := by
    intro M M' j j' hM' hM2 h hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hj
    have h' : M * 2 ^ j = (M' * 2 ^ (d + 1)) * 2 ^ j := by
      rw [h, show j + d + 1 = j + (d + 1) by omega, Nat.pow_add, Nat.mul_comm (2 ^ j), Nat.mul_assoc]
    have h2 := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos j) h'
    have : M' * 2 ^ (d + 1) ≥ 2 ^ (p - 1) * 2 := by
      apply Nat.mul_le_mul hM'
      rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left 2 (Nat.two_pow_pos d)
    omega
  have hj : j = j' := by
    rcases Nat.lt_trichotomy j j' with hl | he | hg
    · exact absurd hl (key hM' hM2 h)
    · exact he
    · exact absurd hg (key hM hM2' h.symm)
  subst hj
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos j) h⟩

/-- In a valid encoding of a NaN (exponent field all ones, significand field nonzero), the
encoding is the canonical NaN's. -/
theorem nan_canonical {p e b : Nat} (hp : 2 ≤ p) (he : 2 ≤ e) (s : Format) (hs : spec? p e = some s)
    (hv : validBits s b = true) (hx : (fields p e b).2.1 = 2 ^ e - 1) (hf : (fields p e b).2.2 ≠ 0) :
    b = (packedNaN s).toNat := by
  unfold spec? at hs
  rw [dif_pos ⟨hp, he⟩] at hs
  cases hs
  simp only [validBits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hv
  obtain ⟨hlt, hv⟩ := hv
  have hval : (BitVec.ofNat (1 + e + (p - 1)) b).toNat = b := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  rcases hv with (h1 | h2) | h3
  · exfalso; apply h1
    apply BitVec.eq_of_toNat_eq
    simp only [unpackExponent, BitVec.extractLsb'_toNat, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
    rw [hval, Nat.shiftRight_eq_div_pow]
    exact hx
  · exfalso; apply hf
    have := congrArg BitVec.toNat h2
    simp only [unpackMantissa, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.zero_mod] at this
    rw [Nat.mod_eq_of_lt hlt] at this
    exact this
  · have := congrArg BitVec.toNat h3
    rw [hval] at this
    exact this

theorem two_le_pow {e : Nat} (he : 2 ≤ e) : 2 ≤ 2 ^ (e - 1) := by
  have : 2 ^ 1 ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  simpa using this

theorem pow_pred {p : Nat} (hp : 1 ≤ p) : 2 ^ p = 2 * 2 ^ (p - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

/-- A subnormal or zero datum's magnitude is below every normal datum's, as `magText` scales them. -/
theorem sub_lt_normal {p D f f' x' : Nat} (hf : f < 2 ^ (p - 1)) (hx' : 1 ≤ x') :
    f * 2 ^ (1 - D) < (f' + 2 ^ (p - 1)) * 2 ^ (x' - D) :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hf (Nat.two_pow_pos _))
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega)))

/-- The value `magText` writes fixes the sign, the exponent field and the significand field. -/
theorem magVal_inj {p e x f x' f' : Nat} {ng ng' : Bool} (hf : f < 2 ^ (p - 1))
    (hf' : f' < 2 ^ (p - 1)) (h : magVal p e x f ng = magVal p e x' f' ng') : ng = ng' ∧ x = x' ∧ f = f' := by
  have hpos := Nat.two_pow_pos (p - 1)
  have s0 : ∀ {x f : Nat}, sig p x f = 0 ↔ x = 0 ∧ f = 0 := by
    intro x f; unfold sig; split <;> omega
  have sN : ∀ {x f : Nat}, x ≠ 0 → f < 2 ^ (p - 1) → sig p x f = f + 2 ^ (p - 1) := by
    intro x f hx _; unfold sig; rw [if_neg hx]
  have sZ : ∀ {x f : Nat}, x = 0 → sig p x f = f := by
    intro x f hx; unfold sig; rw [if_pos hx]
  have eN : ∀ {x : Nat}, x ≠ 0 → expo x = x := by intro x hx; unfold expo; rw [if_neg hx]
  have eZ : ∀ {x : Nat}, x = 0 → expo x = 1 := by intro x hx; unfold expo; rw [if_pos hx]
  have pow2 : ∀ k, 2 ^ k ≠ 0 := fun k => Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)
  unfold magVal at h
  by_cases z : sig p x f = 0 <;> by_cases z' : sig p x' f' = 0
  · simp only [z, z', if_true, BV.int.injEq] at h
    obtain ⟨h1, h2⟩ := s0.mp z; obtain ⟨h1', h2'⟩ := s0.mp z'
    exact ⟨h.1, by omega, by omega⟩
  · simp only [z, z', if_true, if_false] at h
    by_cases d' : shift p e ≤ expo x' <;> simp only [d', if_true, if_false, reduceCtorEq, BV.int.injEq] at h
    rcases Nat.mul_eq_zero.mp h.2.symm with h0 | h0
    · exact absurd h0 z'
    · exact absurd h0 (pow2 _)
  · simp only [z, z', if_true, if_false] at h
    by_cases d : shift p e ≤ expo x <;> simp only [d, if_true, if_false, reduceCtorEq, BV.int.injEq] at h
    rcases Nat.mul_eq_zero.mp h.2 with h0 | h0
    · exact absurd h0 z
    · exact absurd h0 (pow2 _)
  · simp only [z, z', if_false] at h
    by_cases d : shift p e ≤ expo x <;> by_cases d' : shift p e ≤ expo x' <;>
      simp only [d, d', if_true, if_false, reduceCtorEq, BV.int.injEq, BV.dec.injEq] at h
    · obtain ⟨hng, hm⟩ := h
      refine ⟨hng, ?_⟩
      by_cases hx : x = 0 <;> by_cases hx' : x' = 0
      · rw [sZ hx, sZ hx', eZ hx, eZ hx'] at hm
        exact ⟨by omega, Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hm⟩
      · rw [sZ hx, sN hx' hf', eZ hx, eN hx'] at hm
        exact absurd hm (Nat.ne_of_lt (sub_lt_normal hf (by omega)))
      · rw [sN hx hf, sZ hx', eN hx, eZ hx'] at hm
        exact absurd hm.symm (Nat.ne_of_lt (sub_lt_normal hf' (by omega)))
      · rw [sN hx hf, sN hx' hf'] at hm
        obtain ⟨hj, hM⟩ := mul_pow_inj (p := p) (by omega) (by omega) (by omega) (by omega) hm
        rw [eN hx] at hj d; rw [eN hx'] at hj d'
        exact ⟨by omega, by omega⟩
    · obtain ⟨hng, hm, hk⟩ := h
      have hE : expo x = expo x' := by omega
      rw [hE] at hm
      have hM := Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 5)) hm
      refine ⟨hng, ?_⟩
      by_cases h0 : x = 0 <;> by_cases h0' : x' = 0
      · rw [sZ h0, sZ h0'] at hM; exact ⟨by omega, hM⟩
      · rw [sZ h0, sN h0' hf'] at hM; omega
      · rw [sN h0 hf, sZ h0'] at hM; omega
      · rw [eN h0, eN h0'] at hE; rw [sN h0 hf, sN h0' hf'] at hM; exact ⟨hE, by omega⟩

theorem bne_zero_inj {a b : Nat} (ha : a < 2) (hb : b < 2) (h : (a != 0) = (b != 0)) : a = b := by
  have : a = 0 ∨ a = 1 := by omega
  have : b = 0 ∨ b = 1 := by omega
  rcases ‹a = 0 ∨ a = 1› with rfl | rfl <;> rcases ‹b = 0 ∨ b = 1› with rfl | rfl <;> first | rfl | simp at h

theorem magVal_ne_inf (p e x f : Nat) (ng ng' : Bool) : magVal p e x f ng ≠ .inf ng' := by
  unfold magVal; split <;> (try split) <;> simp

theorem magVal_ne_nan (p e x f : Nat) (ng : Bool) : magVal p e x f ng ≠ .nan := by
  unfold magVal; split <;> (try split) <;> simp

/-- The value `body` writes fixes an encoding within the format's bits, given that two NaN patterns
among them are one encoding. -/
theorem bv_inj_of {p e b b' : Nat} (hp : 1 ≤ p) (hlt : b < 2 ^ (1 + e + (p - 1)))
    (hlt' : b' < 2 ^ (1 + e + (p - 1)))
    (hnan : (fields p e b).2.1 = 2 ^ e - 1 → (fields p e b).2.2 ≠ 0 →
      (fields p e b').2.1 = 2 ^ e - 1 → (fields p e b').2.2 ≠ 0 → b = b')
    (h : bv p e b = bv p e b') : b = b' := by
  have hpe : p + e = 1 + e + (p - 1) := by omega
  have hN : ¬ 2 ^ (p + e) ≤ b := by rw [hpe]; omega
  have hN' : ¬ 2 ^ (p + e) ≤ b' := by rw [hpe]; omega
  have hb := field_bounds p e b hlt
  have hb' := field_bounds p e b' hlt'
  apply eq_of_fields hlt hlt'
  unfold bv at h
  rw [if_neg hN, if_neg hN'] at h
  rcases hF : fields p e b with ⟨sg, x, f⟩
  rcases hF' : fields p e b' with ⟨sg', x', f'⟩
  rw [hF, hF'] at hnan
  rw [hF] at hb h
  rw [hF'] at hb' h
  dsimp only at hnan hb hb' h
  have hsg : (sg != 0) = (sg' != 0) → sg = sg' := bne_zero_inj hb.1 hb'.1
  by_cases hx : x = 2 ^ e - 1 <;> by_cases hx' : x' = 2 ^ e - 1
  · simp only [hx, hx', if_true] at h
    by_cases hf : f = 0 <;> by_cases hf' : f' = 0 <;> simp only [hf, hf', if_true, if_false, reduceCtorEq, BV.inf.injEq] at h
    · rw [hsg h, hx, hx', hf, hf']
    · rw [← hF, ← hF', hnan hx hf hx' hf']
  · simp only [hx, hx', if_true, if_false] at h
    by_cases hf : f = 0 <;> simp only [hf, if_true, if_false] at h
    · exact absurd h.symm (magVal_ne_inf _ _ _ _ _ _)
    · exact absurd h.symm (magVal_ne_nan _ _ _ _ _)
  · simp only [hx, hx', if_true, if_false] at h
    by_cases hf' : f' = 0 <;> simp only [hf', if_true, if_false] at h
    · exact absurd h (magVal_ne_inf _ _ _ _ _ _)
    · exact absurd h (magVal_ne_nan _ _ _ _ _)
  · simp only [hx, hx', if_false] at h
    obtain ⟨hng, rfl, rfl⟩ := magVal_inj hb.2.2 hb'.2.2 h
    rw [hsg hng]

/-- The value `body` writes fixes a valid encoding of the format. -/
theorem bv_inj {p e b b' : Nat} (hp : 2 ≤ p) (he : 2 ≤ e) (s : Format) (hs : spec? p e = some s)
    (hv : validBits s b = true) (hv' : validBits s b' = true) (h : bv p e b = bv p e b') : b = b' := by
  have hn : s.numBits = 1 + e + (p - 1) := by
    unfold spec? at hs; rw [dif_pos ⟨hp, he⟩] at hs; cases hs; rfl
  have hlt : b < 2 ^ (1 + e + (p - 1)) := by
    have := hv; simp only [validBits, Bool.and_eq_true, decide_eq_true_eq] at this; rw [← hn]; exact this.1
  have hlt' : b' < 2 ^ (1 + e + (p - 1)) := by
    have := hv'; simp only [validBits, Bool.and_eq_true, decide_eq_true_eq] at this; rw [← hn]; exact this.1
  exact bv_inj_of (by omega) hlt hlt'
    (fun hx hf hx' hf' => (nan_canonical hp he s hs hv hx hf).trans (nan_canonical hp he s hs hv' hx' hf').symm) h

/-- The value `body` writes fixes an encoding of a format with a field of 1: the NaN code past the
bits is the only encoding written `NaN`, and no other encoding is a NaN pattern. -/
theorem bv_inj_thin {p e b b' : Nat} (h : thinOK p e b = true) (h' : thinOK p e b' = true)
    (hv : bv p e b = bv p e b') : b = b' := by
  simp only [thinOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    ne_eq] at h h'
  obtain ⟨⟨hp, -, -⟩, hb⟩ := h
  obtain ⟨-, hb'⟩ := h'
  have hpe : p + e = 1 + e + (p - 1) := by omega
  have hnan : ∀ {c}, c = 2 ^ (p + e) → bv p e c = .nan := by
    intro c hc; unfold bv; rw [if_pos (by omega)]
  have hne : ∀ {c}, c < 2 ^ (p + e) ∧ (¬ c / 2 ^ (p - 1) % 2 ^ e = 2 ^ e - 1 ∨ c % 2 ^ (p - 1) = 0) →
      bv p e c ≠ .nan := by
    intro c ⟨hc, hc2⟩
    unfold bv; rw [if_neg (by omega)]
    split
    · rename_i hx
      have hf : (fields p e c).2.2 = 0 := hc2.resolve_left (fun h => h hx)
      rw [if_pos hf]; simp
    · exact magVal_ne_nan _ _ _ _ _
  rcases hb with hb | hb <;> rcases hb' with hb' | hb'
  · omega
  · exact absurd ((hnan hb).symm.trans hv).symm (hne hb')
  · exact absurd ((hnan hb').symm.trans hv.symm).symm (hne hb)
  · exact bv_inj_of hp (by rw [← hpe]; exact hb.1) (by rw [← hpe]; exact hb'.1)
      (fun hx hf _ _ => absurd (hb.2.resolve_left (fun h => h hx)) hf) hv

/-! ## The text -/

theorem not_p_digits {n : Nat} : 'p' ∉ Nat.toDigits 10 n := fun h => absurd (digit_of_mem h) (by decide)

theorem not_x_digits {n : Nat} : 'x' ∉ Nat.toDigits 10 n := fun h => absurd (digit_of_mem h) (by decide)

theorem not_p_mag (p e x f : Nat) : 'p' ∉ (magText p e x f).toList := by
  rw [magText_toList]
  split
  · simp [List.mem_append, not_p_digits]
  · split
    · simp [List.mem_append, not_p_digits]
    · simp [List.mem_append, not_p_digits]

theorem not_p_body (p e b : Nat) : 'p' ∉ (body p e b).toList := by
  unfold body
  dsimp only
  split
  · decide
  split
  · split
    · split <;> decide
    · decide
  · split
    · rw [String.empty_append]; exact not_p_mag _ _ _ _
    · rw [String.toList_append]; simp only [List.mem_append, not_or]
      exact ⟨by decide, not_p_mag _ _ _ _⟩

theorem spec_bounds {p e : Nat} {s : Format} (hs : spec? p e = some s) : 2 ≤ p ∧ 2 ≤ e := by
  unfold spec? at hs
  split at hs
  · assumption
  · cases hs

/-- **A Float literal's text determines it**: two encodings with data (`ok`) and one text have the
same format and are one encoding. -/
theorem text_inj {p e b p' e' b' : Nat} (h : ok p e b = true) (h' : ok p' e' b' = true)
    (ht : text p e b = text p' e' b') : p = p' ∧ e = e' ∧ b = b' := by
  have hl := congrArg String.toList ht
  rw [text_eq, text_eq] at hl
  obtain ⟨hbody, hsuf⟩ := append_sep_inj (not_p_body p e b) (not_p_body p' e' b') hl
  obtain ⟨hpd, hed⟩ := append_sep_inj not_x_digits not_x_digits hsuf
  have hp := toDigits_inj hpd
  have he := toDigits_inj hed
  subst hp he
  refine ⟨rfl, rfl, ?_⟩
  have hv := congrArg bodyVal hbody
  rw [bodyVal_body, bodyVal_body, Option.some.injEq] at hv
  unfold ok at h h'
  cases hs : spec? p e with
  | none => rw [hs] at h h'; exact bv_inj_thin h h' hv
  | some s =>
    rw [hs] at h h'
    obtain ⟨hp, he⟩ := spec_bounds hs
    exact bv_inj hp he s hs h h' hv

end KCore.KFloat
