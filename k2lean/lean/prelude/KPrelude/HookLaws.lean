import KPrelude.Ext

/-!
# Laws of the hooks that K states as equations

`domains.md` gives some hooked functions equations or simplification rules besides their hooks
(`bitRangeInt`, `signExtendBitRangeInt`, `_&Int_`, `_modInt_`, `_<=String_`, `replaceFirst`,
`countAllOccurrences`, `rfindChar`). Each theorem below is such an equation, stated over the
hook definitions in the shape the generator writes it (`Equations.lean`), and proved from the
definitions: `k2l_hook_law` (`KPrelude.Tactic`) closes a generated statement with it.

Two equations of `domains.md` are false in this model and have no law here:
`countAllOccurrences` equation 2 at an empty `ToCount`, where the equations give
`countAllOccurrences(S, "") = 1 +Int countAllOccurrences(S, "")` (no total function satisfies
that), and `S1 |Set S2 = S1 (S2 -Set S1)` on carrier values that are not well formed (an
unsorted list is no set, and `_Set_` is undefined on it).
-/

namespace KPrelude.IntHook

/-! ## `INT` -/

theorem one_shl (n : Nat) : (1 : Int) <<< n = 2 ^ n := by rw [Int.shiftLeft_eq]; simp

/-- `bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)` -/
theorem bitRange_eqn (I IDX LEN : Int) :
    bitRange I IDX LEN = (Option.bind (shr I IDX) fun r => (Option.bind (shl (1 : Int) LEN) fun r_1 => (Option.bind (emod r r_1) fun r_3 => some r_3))) := by
  unfold bitRange shr shl emod
  by_cases h1 : IDX < 0
  · rw [ite_eq_left h1, Option.bind_none, ite_eq_right (by omega)]
  · by_cases h2 : LEN < 0
    · rw [ite_eq_right h1, Option.bind_some, ite_eq_left h2, Option.bind_none, ite_eq_right (by omega)]
    · have : (2 : Int) ^ LEN.toNat ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
      rw [ite_eq_right h1, Option.bind_some, ite_eq_right h2, Option.bind_some, one_shl,
        ite_eq_right this, Option.bind_some, ite_eq_left (by omega)]; rfl


theorem signExtend_aux (r H : Int) (_hH : 0 < H) (h0 : 0 ≤ r) (h1 : r < 2 * H) :
    (if r ≥ H then r - 2 * H else r) = (r + H) % (2 * H) - H := by
  by_cases h : r ≥ H
  · rw [ite_eq_left h]
    have e : r + H = (r - H) + 1 * (2 * H) := by omega
    rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]; omega
  · rw [ite_eq_right h, Int.emod_eq_of_lt (by omega) (by omega)]; omega

/-- `signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))` -/
theorem signExtendBitRange_eqn (I IDX LEN : Int) :
    signExtendBitRange I IDX LEN = (Option.bind (bitRange I IDX LEN) fun r => (Option.bind (shl (1 : Int) (sub LEN (1 : Int))) fun r_1 => (Option.bind (shl (1 : Int) LEN) fun r_3 => (Option.bind (emod (add r r_1) r_3) fun r_5 => (Option.bind (shl (1 : Int) (sub LEN (1 : Int))) fun r_7 => some (sub r_5 r_7)))))) := by
  unfold signExtendBitRange bitRange shl emod add sub
  by_cases h1 : 0 ≤ IDX ∧ 0 < LEN
  · obtain ⟨n, hn⟩ : ∃ n : Nat, LEN = n + 1 := ⟨(LEN - 1).toNat, by omega⟩
    subst hn
    have e1 : ((n : Int) + 1).toNat = n + 1 := by omega
    have e2 : ((n : Int) + 1 - 1) = n := by omega
    have hp : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by rw [Int.pow_succ]; omega
    have hH : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
    rw [ite_eq_left h1, ite_eq_left (show 0 ≤ IDX ∧ 0 ≤ (n : Int) + 1 by omega)]
    simp only [e1, e2, Option.bind_some, ite_eq_right (show ¬ (n : Int) < 0 by omega),
      ite_eq_right (show ¬ ((n : Int) + 1) < 0 by omega), one_shl, Int.toNat_natCast,
      Nat.add_sub_cancel, hp, ite_eq_right (show ¬ (2 * (2 : Int) ^ n) = 0 by omega)]
    have hr0 : 0 ≤ (I >>> IDX.toNat) % (2 * 2 ^ n) := Int.emod_nonneg _ (by omega)
    have hr1 : (I >>> IDX.toNat) % (2 * 2 ^ n) < 2 * 2 ^ n := Int.emod_lt_of_pos _ (by omega)
    exact congrArg some (signExtend_aux _ _ hH hr0 hr1)
  · rw [ite_eq_right h1]
    by_cases h2 : 0 ≤ IDX ∧ 0 ≤ LEN
    · rw [ite_eq_left h2, Option.bind_some, ite_eq_left (show LEN - 1 < 0 by omega), Option.bind_none]
    · rw [ite_eq_right h2, Option.bind_none]

/-- `I1 modInt I2 => ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2)` (a simplification
rule with `requires I2 =/=Int 0`; it holds at `0` too, both sides undefined). -/
theorem emod_tmod_abs (I1 I2 : Int) :
    (Option.bind (emod I1 I2) fun r => some r) = (Option.bind (tmod I1 (abs I2)) fun r_1 => (Option.bind (tmod (add r_1 (abs I2)) (abs I2)) fun r_3 => some r_3)) := by
  unfold emod tmod add
  by_cases h : I2 = 0
  · subst h; rfl
  · have ha : abs I2 ≠ 0 := by unfold abs; split <;> omega
    have hp : 0 < abs I2 := by unfold abs; split <;> omega
    rw [ite_eq_right h, ite_eq_right ha]
    simp only [Option.bind_some, ite_eq_right ha]
    congr 1
    have hs0 := Int.lt_tmod_of_pos I1 hp
    have hs1 := Int.tmod_lt_of_pos I1 hp
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    rw [show I1.tmod (abs I2) + abs I2 = I1.tmod (abs I2) + 1 * abs I2 by omega,
      Int.add_mul_emod_self_right, Int.tmod_def, Int.sub_eq_add_neg, ← Int.mul_neg,
      Int.add_mul_emod_self_left]
    show I1 % I2 = I1 % abs I2
    unfold abs; split
    · rw [Int.emod_neg]
    · rfl

theorem testBit_sub_of_imp : ∀ (i : Nat) {x y : Nat}, (∀ j, y.testBit j = true → x.testBit j = true) →
    (x - y).testBit i = (x.testBit i && !y.testBit i)
  | 0, x, y, h => by
    have h0 := h 0
    have hle := Nat.le_of_testBit h
    simp only [Nat.testBit_zero, decide_eq_true_eq] at h0 ⊢
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp_all <;> omega
  | i + 1, x, y, h => by
    have hle := Nat.le_of_testBit h
    have hh : ∀ j, (y / 2).testBit j = true → (x / 2).testBit j = true := by
      intro j; rw [Nat.testBit_div_two, Nat.testBit_div_two]; exact h (j + 1)
    have hle2 := Nat.le_of_testBit hh
    have h0 := h 0
    simp only [Nat.testBit_zero, decide_eq_true_eq] at h0
    have e : (x - y) / 2 = x / 2 - y / 2 := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, e, testBit_sub_of_imp i hh]

/-- Bit `i` of an integer in two's complement. -/
def bitI : Int → Nat → Bool
  | .ofNat n, i => n.testBit i
  | .negSucc n, i => !n.testBit i

theorem bitI_land (x y : Int) (i : Nat) : bitI (land x y) i = (bitI x i && bitI y i) := by
  cases x <;> cases y <;> simp only [land, bitI]
  · exact Nat.testBit_and _ _ _
  · rw [testBit_sub_of_imp i (fun j hj => by simp at hj; exact hj.1)]; simp; cases Nat.testBit _ i <;> simp
  · rw [testBit_sub_of_imp i (fun j hj => by simp at hj; exact hj.2)]; simp; cases Nat.testBit _ i <;> simp
  · simp

theorem bitI_ext {x y : Int} (h : ∀ i, bitI x i = bitI y i) : x = y := by
  cases x with
  | ofNat a => cases y with
    | ofNat b => exact congrArg _ (Nat.eq_of_testBit_eq h)
    | negSucc b =>
      have := h (a + b + 1)
      simp only [bitI, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega : a ≤ a + b + 1))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega : b ≤ a + b + 1)))] at this
      simp at this
  | negSucc a => cases y with
    | ofNat b =>
      have := h (a + b + 1)
      simp only [bitI, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega : a ≤ a + b + 1))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega : b ≤ a + b + 1)))] at this
      simp at this
    | negSucc b =>
      exact congrArg _ (Nat.eq_of_testBit_eq fun i => by simpa [bitI] using h i)

/-- `I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C` -/
theorem land_assoc (I1 I2 C : Int) : land I1 (land I2 C) = land (land I1 I2) C :=
  bitI_ext fun i => by simp only [bitI_land, Bool.and_assoc]

end KPrelude.IntHook

namespace KPrelude.StringHook

/-! ## `STRING` -/

theorem find_go_spec (hs ns : List Char) : ∀ (l : List Char) (k : Nat), l = hs.drop k → k ≤ hs.length →
    (find.go hs ns k l = some (-1) ∧ ∀ p, k ≤ p → ¬ ns <+: hs.drop p) ∨
    (∃ m : Nat, find.go hs ns k l = some (m : Int) ∧ k ≤ m ∧ m ≤ hs.length ∧ ns <+: hs.drop m ∧
      ∀ p, k ≤ p → p < m → ¬ ns <+: hs.drop p)
  | [], k, hl, hk => by
    have hlen : hs.length ≤ k := List.drop_eq_nil_iff.1 hl.symm
    unfold find.go
    by_cases he : ns.isEmpty
    · right; refine ⟨hs.length, by simp [he], by omega, Nat.le_refl _, ?_, fun p h1 h2 => by omega⟩
      simp [List.isEmpty_iff.1 he]
    · left; refine ⟨by simp [he], fun p hp hpre => ?_⟩
      rw [List.drop_eq_nil_iff.2 (by omega)] at hpre
      exact he (List.isEmpty_iff.2 (List.prefix_nil.1 hpre))
  | c :: t, k, hl, hk => by
    have hlt : k < hs.length := by
      rcases Nat.lt_or_ge k hs.length with h | h
      · exact h
      · rw [List.drop_eq_nil_iff.2 h] at hl; cases hl
    unfold find.go
    by_cases hp : ns.isPrefixOf (c :: t) = true
    · right; refine ⟨k, by simp [hp], Nat.le_refl _, by omega, ?_, fun p h1 h2 => by omega⟩
      rw [← hl]; exact List.isPrefixOf_iff_prefix.1 hp
    · have ht : t = hs.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hlt] at hl; exact (List.cons.inj hl).2
      have hk0 : ¬ ns <+: hs.drop k := by rw [← hl]; exact fun h => hp (List.isPrefixOf_iff_prefix.2 h)
      simp only [hp, Bool.false_eq_true, ite_false]
      rcases find_go_spec hs ns t (k + 1) ht (by omega) with ⟨h1, h2⟩ | ⟨m, h1, h2, h3, h4, h5⟩
      · left; refine ⟨h1, fun p hp' => ?_⟩
        rcases Nat.eq_or_lt_of_le hp' with rfl | hp'
        · exact hk0
        · exact h2 p hp'
      · right; refine ⟨m, h1, by omega, h3, h4, fun p hp1 hp2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hp1 with rfl | hp1
        · exact hk0
        · exact h5 p hp1 hp2

/-- `find h n 0`: `-1` when `n` occurs nowhere, else the first index of an occurrence. -/
theorem find_zero_spec (h n : String) :
    (find h n 0 = some (-1) ∧ ∀ p, ¬ n.toList <+: h.toList.drop p) ∨
    (∃ m : Nat, find h n 0 = some (m : Int) ∧ m + n.length ≤ h.length ∧ n.toList <+: h.toList.drop m ∧
      ∀ p, p < m → ¬ n.toList <+: h.toList.drop p) := by
  unfold find
  simp only [show ¬ (0 : Int) < 0 by decide, ite_false, Int.toNat_zero, List.drop_zero,
    show ¬ (0 : Nat) > h.toList.length by omega]
  rcases find_go_spec h.toList n.toList h.toList 0 rfl (by omega) with ⟨h1, h2⟩ | ⟨m, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, fun p => h2 p (by omega)⟩
  · refine Or.inr ⟨m, h1, ?_, h4, fun p hp => h5 p (by omega) hp⟩
    have := h4.length_le
    simp only [List.length_drop, String.length_toList] at this h3
    omega

theorem substr_zero_left (s : String) (m : Nat) (hm : m ≤ s.length) :
    substr s 0 (m : Int) = String.ofList (s.toList.take m) := by
  unfold substr
  have e1 : (max (0 : Int) 0).toNat = 0 := rfl
  have e2 : (min (max (m : Int) 0) (s.length : Int)).toNat = m := by omega
  simp only [e1, e2, Nat.zero_le, ite_true, List.drop_zero, Nat.sub_zero]

theorem substr_to_length (s : String) (a : Nat) (ha : a ≤ s.length) :
    substr s (a : Int) (s.length : Int) = String.ofList (s.toList.drop a) := by
  unfold substr
  have e1 : (max (a : Int) 0).toNat = a := by omega
  have e2 : (min (max (s.length : Int) 0) (s.length : Int)).toNat = s.length := by omega
  simp only [e1, e2, ha, ite_true]
  congr 1
  apply List.take_of_length_le
  simp [String.length_toList]

theorem find_some_of_ge {h n : String}
    (hreq : (Option.bind (find h n 0) fun r => some (IntHook.ge r 0)) = some true) :
    ∃ m : Nat, find h n 0 = some (m : Int) ∧ m + n.length ≤ h.length ∧ n.toList <+: h.toList.drop m ∧
      ∀ p, p < m → ¬ n.toList <+: h.toList.drop p := by
  rcases find_zero_spec h n with ⟨h1, _⟩ | h2
  · rw [h1] at hreq; simp [IntHook.ge] at hreq
  · exact h2

theorem find_none_of_lt {h n : String}
    (hreq : (Option.bind (find h n 0) fun r => some (IntHook.lt r 0)) = some true) :
    find h n 0 = some (-1) ∧ ∀ p, ¬ n.toList <+: h.toList.drop p := by
  rcases find_zero_spec h n with h1 | ⟨m, h1, _⟩
  · exact h1
  · rw [h1] at hreq; simp [IntHook.lt] at hreq; omega

/-- `replaceFirst` equation 1 of `domains.md`. -/
theorem replaceFirst_eqn1 (Replacement Source ToReplace : String)
    (hreq0 : (Option.bind (find Source ToReplace (0 : Int)) fun r => some (IntHook.ge r (0 : Int))) = some true) :
    some (replaceFirst Source ToReplace Replacement) = (Option.bind (find Source ToReplace (0 : Int)) fun r_1 => (Option.bind (find Source ToReplace (0 : Int)) fun r_3 => some (concat (concat (substr Source (0 : Int) r_1) Replacement) (substr Source (IntHook.add r_3 (length ToReplace)) (length Source))))) := by
  obtain ⟨m, hf, hle, _, _⟩ := find_some_of_ge hreq0
  unfold replaceFirst
  simp only [hf, Option.bind_some, IntHook.add, length, concat]
  rw [ite_eq_right (by omega), substr_zero_left _ _ (by omega),
    show (m : Int) + (ToReplace.length : Int) = ((m + ToReplace.length : Nat) : Int) by omega,
    substr_to_length _ _ hle]
  simp only [Int.toNat_natCast, String.ofList_append, String.ofList_toList]

/-- `replaceFirst` equation 2 of `domains.md`. -/
theorem replaceFirst_eqn2 (Gen0 Source ToReplace : String)
    (hreq0 : (Option.bind (find Source ToReplace (0 : Int)) fun r => some (IntHook.lt r (0 : Int))) = some true) :
    replaceFirst Source ToReplace Gen0 = Source := by
  unfold replaceFirst
  rw [(find_none_of_lt hreq0).1]; rfl

theorem countChars_of_none (n : List Char) : ∀ (fuel : Nat) (l : List Char),
    (∀ p, ¬ n <+: l.drop p) → countChars fuel l n = 0
  | 0, _, _ => by simp [countChars]
  | _ + 1, [], _ => by simp [countChars]
  | fuel + 1, c :: cs, h => by
    have h0 : ¬ (c :: cs).take n.length = n := fun e => h 0 (List.prefix_iff_eq_take.2 e.symm)
    simp only [countChars, h0, ite_false]
    exact countChars_of_none n fuel cs (fun p => h (p + 1))

/-- `countAllOccurrences` equation 1 of `domains.md`. -/
theorem countAllOccurrences_eqn1 (Source ToCount : String)
    (hreq0 : (Option.bind (find Source ToCount (0 : Int)) fun r => some (IntHook.lt r (0 : Int))) = some true) :
    countAllOccurrences Source ToCount = (0 : Int) := by
  unfold countAllOccurrences
  split
  · rfl
  · rw [countChars_of_none _ _ _ (find_none_of_lt hreq0).2]; rfl

theorem le_eqn (S1 S2 : String) : le S1 S2 = BoolHook.not (lt S2 S1) := by
  unfold le lt BoolHook.not; rw [← decide_not]; exact decide_eq_decide.mpr String.not_lt.symm

theorem ge_eqn (S1 S2 : String) : ge S1 S2 = BoolHook.not (lt S1 S2) := by
  unfold ge lt BoolHook.not; rw [← decide_not]; exact decide_eq_decide.mpr String.not_lt.symm

/-- The first element of `L` that satisfies `p`, as an integer, or `-1`. -/
def firstI (p : Nat → Bool) (L : List Nat) : Int := ((L.find? p).map fun k => (k : Int)).getD (-1)

theorem firstI_lt {p : Nat → Bool} {L : List Nat} {x : Nat} (h : ∀ y ∈ L, y < x) : firstI p L < x := by
  unfold firstI
  cases hf : L.find? p with
  | none => simp; omega
  | some y => have := h y (List.mem_of_find?_eq_some hf); simp; omega

theorem firstI_or (p q : Nat → Bool) : ∀ (L : List Nat), L.Pairwise (· > ·) →
    firstI (fun k => p k || q k) L = IntHook.max (firstI p L) (firstI q L)
  | [], _ => by simp [firstI, IntHook.max]
  | x :: L, hL => by
    rw [List.pairwise_cons] at hL
    have hlt : ∀ y ∈ L, y < x := fun y hy => hL.1 y hy
    have hp := firstI_lt (p := p) hlt
    have hq := firstI_lt (p := q) hlt
    have e : ∀ (r : Nat → Bool), firstI r (x :: L) = if r x then (x : Int) else firstI r L := by
      intro r; unfold firstI; rw [List.find?_cons]; cases r x <;> simp
    rw [e, e, e]
    cases hpx : p x <;> cases hqx : q x
    · simp only [Bool.or_false, Bool.false_eq_true, ite_false]; exact firstI_or p q L hL.2
    all_goals simp only [Bool.or_true, Bool.or_false, ite_true, Bool.false_eq_true, ite_false,
      IntHook.max]
    all_goals split <;> omega


theorem firstI_congr {p q : Nat → Bool} (h : ∀ k, p k = q k) (L : List Nat) : firstI p L = firstI q L := by
  rw [show p = q from funext h]

theorem firstI_false (L : List Nat) : firstI (fun _ => false) L = -1 := by
  unfold firstI; rw [List.find?_eq_none.2 (by simp)]; rfl

theorem rfindChar_nonneg (h cs : String) (i : Int) (hi : ¬ i < 0) :
    rfindChar h cs i = some (firstI (fun k => match h.toList[k]? with
      | some c => cs.toList.contains c | none => false) (List.range (min i.toNat h.toList.length + 1)).reverse) := by
  unfold rfindChar
  by_cases he : cs.isEmpty = true
  · rw [ite_eq_left he]
    have : cs.toList = [] := by rw [String.isEmpty_iff.1 he]; rfl
    rw [firstI_congr (q := fun _ => false) (fun k => by rw [this]; cases h.toList[k]? <;> rfl), firstI_false]
  · rw [ite_eq_right he, ite_eq_right hi]; rfl

theorem rfind_nonneg (h n : String) (i : Int) (hi : ¬ i < 0) :
    rfind h n i = some (firstI (fun k => n.toList.isPrefixOf (h.toList.drop k))
      (List.range (min i.toNat h.toList.length + 1)).reverse) := by
  unfold rfind; rw [ite_eq_right hi]; rfl

theorem cands_pairwise (n : Nat) : ((List.range n).reverse).Pairwise (· > ·) :=
  List.pairwise_reverse.2 (List.pairwise_lt_range)

/-- `rfindChar` equation 1 of `domains.md`. -/
theorem rfindChar_eqn1 (I : Int) (S1 S2 : String) (hreq0 : ne S2 "" = true) :
    rfindChar S1 S2 I = (Option.bind (rfind S1 (substr S2 (0 : Int) (1 : Int)) I) fun r => (Option.bind (rfindChar S1 (substr S2 (1 : Int) (length S2)) I) fun r_1 => some (IntHook.max r r_1))) := by
  have hne : S2 ≠ "" := by simpa [ne] using hreq0
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, S2.toList = c :: cs := by
    cases h : S2.toList with
    | nil => exact absurd (String.toList_inj.1 (by rw [h]; rfl)) hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hlen : S2.length = cs.length + 1 := by rw [← String.length_toList, hcs]; rfl
  have e0 : substr S2 0 1 = String.ofList [c] := by
    unfold substr
    have e1 : (max (0 : Int) 0).toNat = 0 := rfl
    have e2 : (min (max (1 : Int) 0) (S2.length : Int)).toNat = 1 := by omega
    simp only [e1, e2, Nat.zero_le, ite_true, List.drop_zero, hcs]; rfl
  have e1 : substr S2 1 (length S2) = String.ofList cs := by
    unfold length
    rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, substr_to_length _ _ (by omega), hcs]; rfl
  rw [e0, e1]
  by_cases hI : I < 0
  · unfold rfindChar rfind
    rw [ite_eq_right (by rw [String.isEmpty_iff]; exact hne), ite_eq_left hI, ite_eq_left hI]; rfl
  · rw [rfindChar_nonneg _ _ _ hI, rfind_nonneg _ _ _ hI, rfindChar_nonneg _ _ _ hI]
    simp only [Option.bind_some, String.toList_ofList, hcs]
    rw [← firstI_or _ _ _ (cands_pairwise _)]
    congr 1
    apply firstI_congr
    intro k
    rw [← List.head?_drop]
    cases S1.toList.drop k with
    | nil => rfl
    | cons x t =>
      simp only [List.head?_cons, List.contains_cons, List.isPrefixOf_cons_cons, List.isPrefixOf_nil_left,
        Bool.and_true]
      rw [Bool.beq_comm]

theorem countChars_skip (n : List Char) : ∀ (k fuel : Nat) (l : List Char),
    (∀ p, p < k → ¬ n <+: l.drop p) → k ≤ l.length → k ≤ fuel →
    countChars fuel l n = countChars (fuel - k) (l.drop k) n
  | 0, fuel, l, _, _, _ => by simp
  | k + 1, fuel, l, h, hl, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases l with
    | nil => simp at hl
    | cons c cs =>
      have h0 : ¬ (c :: cs).take n.length = n := fun e => h 0 (by omega) (List.prefix_iff_eq_take.2 e.symm)
      simp only [countChars, h0, ite_false]
      rw [countChars_skip n k f cs (fun p hp => h (p + 1) (by omega)) (by simp at hl; omega) (by omega)]
      simp

theorem countChars_hit {n l : List Char} (h : n <+: l) (hn : n ≠ []) (f : Nat) :
    countChars (f + 1) l n = countChars f (l.drop n.length) n + 1 := by
  cases l with
  | nil => exact absurd (List.prefix_nil.1 h) hn
  | cons c cs =>
    have e : (c :: cs).take n.length = n := (List.prefix_iff_eq_take.1 h).symm
    simp only [countChars, e, ite_true]

theorem countChars_fuel {n : List Char} (hn : n ≠ []) : ∀ (len : Nat) (l : List Char), l.length = len →
    ∀ f₁ f₂, len ≤ f₁ → len ≤ f₂ → countChars f₁ l n = countChars f₂ l n
  | len, [], _, f₁, f₂, _, _ => by cases f₁ <;> cases f₂ <;> rfl
  | len, c :: cs, hl, f₁, f₂, h₁, h₂ => by
    obtain ⟨a, rfl⟩ : ∃ a, f₁ = a + 1 := ⟨f₁ - 1, by simp at hl; omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, f₂ = b + 1 := ⟨f₂ - 1, by simp at hl; omega⟩
    have hlen : 0 < n.length := List.length_pos_iff.2 hn
    simp only [countChars]
    split
    · rw [countChars_fuel hn _ _ rfl a b (by simp at hl ⊢; omega) (by simp at hl ⊢; omega)]
    · exact countChars_fuel hn _ _ rfl a b (by simp at hl ⊢; omega) (by simp at hl ⊢; omega)
termination_by len => len
decreasing_by all_goals simp_wf; simp at hl; omega

/-- `countAllOccurrences` equation 2 of `domains.md` holds at every nonempty `ToCount` (the
statement has no such hypothesis, so it stays open: see `countAllOccurrences_eqn2_empty`). -/
theorem countAllOccurrences_eqn2_of_ne (Source ToCount : String) (hne : ToCount ≠ "")
    (hreq0 : (Option.bind (find Source ToCount (0 : Int)) fun r => some (IntHook.ge r (0 : Int))) = some true) :
    some (countAllOccurrences Source ToCount) = (Option.bind (find Source ToCount (0 : Int)) fun r_1 => some (IntHook.add (1 : Int) (countAllOccurrences (substr Source (IntHook.add r_1 (length ToCount)) (length Source)) ToCount))) := by
  obtain ⟨m, hf, hle, hpre, hfirst⟩ := find_some_of_ge hreq0
  have hn : ToCount.toList ≠ [] := fun h => hne (String.toList_inj.1 (by rw [h]; rfl))
  have he : ToCount.isEmpty = false := by
    cases e : ToCount.isEmpty
    · rfl
    · exact absurd (String.isEmpty_iff.1 e) hne
  have hlen : 0 < ToCount.length := by rw [← String.length_toList]; exact List.length_pos_iff.2 hn
  have h1 : Source.toList.length = Source.length := String.length_toList
  have h2 : ToCount.toList.length = ToCount.length := String.length_toList
  simp only [hf, Option.bind_some, IntHook.add, length]
  rw [show (m : Int) + (ToCount.length : Int) = ((m + ToCount.length : Nat) : Int) by omega,
    substr_to_length _ _ hle]
  unfold countAllOccurrences
  simp only [he, Bool.false_eq_true, ite_false, String.toList_ofList, String.length_ofList,
    Option.some.injEq]
  rw [← String.length_toList, countChars_skip _ m _ _ hfirst (by rw [String.length_toList]; omega) (by rw [String.length_toList]; omega)]
  obtain ⟨f, hf'⟩ : ∃ f, Source.toList.length - m = f + 1 := ⟨Source.toList.length - m - 1, by rw [String.length_toList]; omega⟩
  rw [hf', countChars_hit hpre hn, List.drop_drop,
    countChars_fuel hn _ _ rfl f (Source.toList.drop (m + ToCount.toList.length)).length
      (by simp only [List.length_drop]; omega) (Nat.le_refl _)]
  simp only [List.length_drop, h2]
  omega

/-! ## Equations false in this model -/

/-- `countAllOccurrences` equation 2 at `Source = ToCount = ""`: its condition holds
(`findString("", "", 0)` is `0`) and its two sides differ, since the equation reads
`countAllOccurrences("", "") = 1 +Int countAllOccurrences("", "")`. -/
theorem countAllOccurrences_eqn2_empty :
    (Option.bind (find "" "" (0 : Int)) fun r => some (IntHook.ge r (0 : Int))) = some true ∧
    some (countAllOccurrences "" "") ≠ (Option.bind (find "" "" (0 : Int)) fun r_1 => some (IntHook.add (1 : Int) (countAllOccurrences (substr "" (IntHook.add r_1 (length "")) (length "")) ""))) := by
  unfold countAllOccurrences
  decide

end KPrelude.StringHook

namespace KPrelude.SetHook

open ListIso

/-- `S1 |Set S2 => S1 (S2 -Set S1)` fails at every carrier value that is not well formed:
there `_Set_` is undefined and `|Set` is not. -/
theorem union_eqn_not_wf {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]
    [Std.TransOrd K] [Std.LawfulEqOrd K] {s : S} (h : ¬ MapHook.WF s) :
    some (SetHook.union s SetHook.unit) ≠ (Option.bind (SetHook.concat s (SetHook.difference SetHook.unit s)) fun r => some r) := by
  have hb : SAL.sortedb (toList s) = false := by
    cases e : SAL.sortedb (toList s)
    · rfl
    · exact absurd ((SAL.sortedb_iff _).1 e) h
  simp [SetHook.concat, MapHook.concat, SAL.concat, hb]

/-- A counterexample from any key: the list `[k, k]` (a repeated element) is no set. -/
theorem union_eqn_dup {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]
    [Std.TransOrd K] [Std.LawfulEqOrd K] (k : K) :
    some (SetHook.union (ofList [(k, ()), (k, ())] : S) SetHook.unit) ≠ (Option.bind (SetHook.concat (ofList [(k, ()), (k, ())] : S) (SetHook.difference SetHook.unit (ofList [(k, ()), (k, ())] : S))) fun r => some r) := by
  apply union_eqn_not_wf
  intro hw
  unfold MapHook.WF at hw
  rw [toList_ofList] at hw
  cases hw with
  | cons h _ => have := h (k, ()) (by simp); rw [SAL.cmp_self] at this; cases this

end KPrelude.SetHook
