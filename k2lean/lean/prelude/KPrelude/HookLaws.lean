import KPrelude.Ext
import KPrelude.HookAttr

/-!
# Laws of the hooks that K states as equations

`domains.md` gives some hooked functions equations or simplification rules besides their hooks
(`bitRangeInt`, `signExtendBitRangeInt`, `_&Int_`, `_modInt_`, `_<=String_`, `replaceFirst`,
`countAllOccurrences`, `rfindChar`, `_|Set_`). Each theorem below is such an equation, stated over
the hook definitions in the shape the generator writes it (`Equations.lean`), and proved from the
definitions: `k2l_hook_law` (`KPrelude.Tactic`) closes a generated statement with it.
The simplifications of `MAP-KORE-SYMBOLIC` and `SET-KORE-SYMBOLIC` are rewrite rules of the simp
set `k2l_hook` instead, which the generic proof of a simplification about maps or sets uses.

The generator states an equation of a hooked function for well-formed set and map values only
(premises `SetHook.WF`, `MapHook.WF`, which a law takes as hypotheses): the carriers also hold
lists that represent no K value. `S1 |Set S2 = S1 (S2 -Set S1)` holds on sets (`union_eqn`) and
fails on every carrier value that is not one (`union_eqn_not_wf`: an unsorted list is no set,
and `_Set_` is undefined on it).

One equation of `domains.md` is false in this model and has no law here:
`countAllOccurrences` equation 2 at an empty `ToCount`, where the equations give
`countAllOccurrences(S, "") = 1 +Int countAllOccurrences(S, "")` (no total function satisfies
that).
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

section Union

variable {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem mem_toList_foldl_update (l : List (K × Unit)) :
    ∀ (s : S) (p : K × Unit),
      p ∈ toList (l.foldl (fun s q => MapHook.update s q.1 ()) s) ↔ p ∈ toList s ∨ p ∈ l := by
  induction l with
  | nil => intro s p; simp
  | cons q t ih =>
    intro s p
    rw [List.foldl_cons, ih, MapHook.update_def, toList_ofList, SAL.mem_insert_unit, List.mem_cons]
    have e : p.1 = q.1 ↔ p = q := ⟨fun h => Prod.ext h (Subsingleton.elim _ _), fun h => h ▸ rfl⟩
    rw [e]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

theorem wf_foldl_update (l : List (K × Unit)) :
    ∀ (s : S), MapHook.WF s → MapHook.WF (l.foldl (fun s q => MapHook.update s q.1 ()) s) := by
  induction l with
  | nil => intro s h; exact h
  | cons q t ih => intro s h; exact ih _ (MapHook.wf_update h)

/-- `S1 |Set S2 => S1 (S2 -Set S1)` (`domains.md`, `SET`) on sets: at well-formed carrier
values, the K values of sort `Set`. -/
theorem union_eqn {a b : S} (ha : WF a) (hb : WF b) :
    some (SetHook.union a b) = (Option.bind (SetHook.concat a (SetHook.difference b a)) fun r => some r) := by
  have hd : SAL.Sorted (toList (difference b a)) := by
    unfold difference; rw [toList_ofList]; exact SAL.sorted_filter _ hb
  have hin : ∀ {p : K × Unit}, p ∈ toList a → MapHook.inKeys p.1 a = true := by
    intro p hp
    unfold MapHook.inKeys
    rw [MapRepr.lookupR_eq, SAL.lookup_of_mem ha hp]; rfl
  have hdisj : (toList a).all (fun p => (SAL.lookup p.1 (toList (difference b a))).isNone) = true := by
    rw [List.all_eq_true]
    intro p hp
    cases e : SAL.lookup p.1 (toList (difference b a)) with
    | none => rfl
    | some u =>
      have hm := SAL.lookup_mem e
      unfold difference at hm
      rw [toList_ofList, List.mem_filter] at hm
      simp [hin hp] at hm
  have hc : SAL.concat (toList a) (toList (difference b a)) =
      some ((toList a).foldr (fun q acc => SAL.insert q.1 q.2 acc) (toList (difference b a))) := by
    unfold SAL.concat
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true]
      exact ⟨⟨(SAL.sortedb_iff _).2 ha, (SAL.sortedb_iff _).2 hd⟩, hdisj⟩)]
  simp only [concat, MapHook.concat, hc, Option.map_some, Option.bind_some, Option.some.injEq]
  rw [← ofList_toList (union a b)]
  congr 1
  refine SAL.eq_of_mem_iff (wf_foldl_update _ a ha) (SAL.sorted_foldr_insert hd _) fun p => ?_
  rw [SAL.mem_concat hc, union, mem_toList_foldl_update]
  unfold difference
  rw [toList_ofList, List.mem_filter]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hk : MapHook.inKeys p.1 a = true
      · left
        unfold MapHook.inKeys at hk
        rw [MapRepr.lookupR_eq] at hk
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hk
        have hm := SAL.lookup_mem hu
        rwa [show (p.1, u) = p from Prod.ext rfl (Subsingleton.elim _ _)] at hm
      · exact Or.inr ⟨h, by simpa using hk⟩
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h

end Union

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

namespace KPrelude.MapHook

/-! ## The frontend's map `#Ceil`

`#Ceil(@K0 |-> @K1 @Rest) = {(@K0 in_keys(@Rest)) #Equals false} #And #Ceil(@K1)`, for `Map`
and each cell-map sort. Its variables are set variables, which the generator binds as `Option`s
(a model term denotes at most one value), with the well-formedness premise on the map one: at an
unsorted carrier value, which is no map, `_Map_` is undefined while the key may be absent. -/

/-- `K |-> V R` is defined exactly when `K` is not a key of the map `R`. -/
theorem concat_element_isSome {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
    [Std.TransOrd K] [Std.LawfulEqOrd K] (k : K) (v : V) (r : M) (hwf : WF r) :
    (concat (element k v) r).isSome = !(inKeys k r) := by
  cases h : concat (element k v) r with
  | some m =>
    obtain ⟨_, hl, _⟩ := concat_element_iff.1 h
    simp only [inKeys, ← lookup.eq_def, hl]; rfl
  | none =>
    cases hl : lookup r k with
    | none =>
      have := concat_element_iff (k := k) (v := v) (r := r) (m := update r k v)
      rw [h] at this; simp_all
    | some x => simp only [inKeys, ← lookup.eq_def, hl]; rfl

/-- The generated statement of the map `#Ceil`. -/
theorem ceil_concat_element_eqn {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
    [Std.TransOrd K] [Std.LawfulEqOrd K] (K0 : Option K) (K1 : Option V) (Rest : Option M)
    (hwf0 : ∀ m ∈ Rest, WF m) :
    (((Option.bind K0 fun r => (Option.bind K1 fun r_1 => (Option.bind Rest fun r_2 => (Option.bind (concat (element r r_1) r_2) fun r_3 => some r_3))))).isSome = true) ↔ (((Option.bind K0 fun r_4 => (Option.bind Rest fun r_5 => some (inKeys r_4 r_5))) = some false) ∧ ((True) ∧ (((Option.bind K1 fun r_6 => some r_6)).isSome = true))) := by
  cases K0 <;> cases K1 <;> cases Rest <;> simp_all [concat_element_isSome]

end KPrelude.MapHook

namespace KPrelude.SAL

/-! ## Sorted association lists: insert and erase

Facts the collection simplifications below need. `insert` and `erase` scan a list from the left
whether or not it is sorted; the `Sorted` ones hold at maps only. -/

variable {K V : Type} [Ord K]

/-- `erase` and `lookup` read the same prefix: where `lookup` finds nothing, `erase` changes
nothing, at every list. -/
theorem erase_of_lookup_none {k : K} : ∀ {l : List (K × V)}, lookup k l = none → erase k l = l
  | [], _ => rfl
  | (k', v') :: t, h => by
    cases hc : compare k k' with
    | lt => simp [erase, hc]
    | eq => simp [lookup, hc] at h
    | gt =>
      simp only [lookup, hc] at h
      simp only [erase, hc]; rw [erase_of_lookup_none h]

variable [Std.LawfulEqOrd K]

/-- Two inserts at one key: the second wins, at every list. -/
theorem insert_insert (k : K) (v₀ v : V) : ∀ (l : List (K × V)),
    insert k v (insert k v₀ l) = insert k v l
  | [] => by simp [insert]
  | (k', v') :: t => by
    cases hc : compare k k' with
    | lt => simp [insert, hc]
    | eq => simp [insert, hc]
    | gt => simp only [insert, hc]; rw [insert_insert k v₀ v t]

variable [Std.TransOrd K]

theorem mem_erase_of_ne {k : K} {p : K × V} : ∀ {l : List (K × V)}, p ∈ l → p.1 ≠ k → p ∈ erase k l
  | [], h, _ => by simp at h
  | (k', v') :: t, h, hne => by
    cases hc : compare k k' with
    | lt => simpa [erase, hc] using h
    | eq =>
      cases eq_of_cmp hc
      simp only [erase, hc]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd rfl hne
      · exact h
    | gt =>
      simp only [erase, hc, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mem_erase_of_ne h hne)

theorem mem_erase_iff {k : K} {p : K × V} {l : List (K × V)} (hs : Sorted l) :
    p ∈ erase k l ↔ p ∈ l ∧ p.1 ≠ k := by
  refine ⟨fun h => ⟨mem_erase h, fun he => ?_⟩, fun h => mem_erase_of_ne h.1 h.2⟩
  have h1 := lookup_of_mem (sorted_erase hs) (k := p.1) (v := p.2) h
  rw [he, lookup_erase_self k hs] at h1; cases h1

theorem mem_insert_iff {k : K} {v : V} {p : K × V} {l : List (K × V)} (hs : Sorted l) :
    p ∈ insert k v l ↔ p = (k, v) ∨ (p ∈ l ∧ p.1 ≠ k) := by
  constructor
  · intro h
    by_cases he : p.1 = k
    · left
      have h1 := lookup_of_mem (sorted_insert hs) (k := p.1) (v := p.2) h
      rw [he, lookup_insert_self] at h1
      cases h1; exact Prod.ext he rfl
    · rcases mem_insert h with h | h
      · exact absurd (by rw [h]) he
      · exact Or.inr ⟨h, he⟩
  · rintro (rfl | ⟨h, hne⟩)
    · exact mem_insert_self _ _ _
    · exact mem_insert_of_mem_ne h hne

theorem lookup_iff_mem {k : K} {v : V} {l : List (K × V)} (hs : Sorted l) :
    lookup k l = some v ↔ (k, v) ∈ l := ⟨lookup_mem, lookup_of_mem hs⟩

end KPrelude.SAL

namespace KPrelude.MapHook

/-! ## `MAP-KORE-SYMBOLIC`

Its simplifications, as rewrite rules (`@[k2l_hook]`). The generator states a simplification for
maps only (`MapHook.WF` premises), and some of them are false at a carrier value that is no map
(`inKeys_remove_self`, `concat_element_of_not_inKeys`, `concat_element_remove_ne`): their laws take
the premise. The others hold at every carrier value and are stated without it. -/

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- `M[K]` is defined exactly when `K` is a key of `M` (`#Ceil(M[K])`). -/
@[k2l_hook] theorem lookup_isSome (m : M) (k : K) : (lookup m k).isSome = inKeys k m := rfl

/-- `K in_keys(.Map) => false` -/
@[k2l_hook] theorem inKeys_unit (k : K) : inKeys k (unit : M) = false := by
  unfold inKeys unit; rw [MapRepr.lookupR_eq, toList_ofList]; rfl

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- `K in_keys(M[K <- V]) => true` -/
@[k2l_hook] theorem inKeys_update_same (m : M) (k : K) (v : V) : inKeys k (update m k v) = true := by
  unfold inKeys; rw [MapRepr.lookupR_eq, update_def, toList_ofList, SAL.lookup_insert_self]; rfl

/-- `K1 in_keys(M[K2 <- V]) => K1 in_keys(M) requires K1 =/=K K2` -/
@[k2l_hook] theorem inKeys_update_ne (m : M) {k₁ k₂ : K} (v : V) (h : k₁ ≠ k₂) :
    inKeys k₁ (update m k₂ v) = inKeys k₁ m := by
  unfold inKeys; rw [MapRepr.lookupR_eq, MapRepr.lookupR_eq, update_def, toList_ofList,
    SAL.lookup_insert_ne _ h]

/-- `M[K <- V][K] orDefault D => V` -/
@[k2l_hook] theorem lookupOrDefault_update_self (m : M) (k : K) (v d : V) :
    lookupOrDefault (update m k v) k d = v := by
  unfold lookupOrDefault; rw [MapRepr.lookupR_eq, update_def, toList_ofList, SAL.lookup_insert_self]; rfl

/-- `M[K1 <- V][K2] orDefault D => M[K2] orDefault D requires K1 =/=K K2` -/
@[k2l_hook] theorem lookupOrDefault_update_ne (m : M) {k₁ k₂ : K} (v d : V) (h : k₁ ≠ k₂) :
    lookupOrDefault (update m k₁ v) k₂ d = lookupOrDefault m k₂ d := by
  unfold lookupOrDefault; rw [MapRepr.lookupR_eq, MapRepr.lookupR_eq, update_def, toList_ofList,
    SAL.lookup_insert_ne _ (Ne.symm h)]

attribute [k2l_hook] lookup_update_self

/-- `M[K1 <- V][K2] => M[K2] requires K1 =/=K K2` -/
@[k2l_hook] theorem lookup_update_ne' (m : M) {k₁ k₂ : K} (v : V) (h : k₁ ≠ k₂) :
    lookup (update m k₁ v) k₂ = lookup m k₂ := lookup_update_ne m v (Ne.symm h)

omit [Std.TransOrd K] in
/-- `M[K <- V0][K <- V] => M[K <- V]` -/
@[k2l_hook] theorem update_update_self (m : M) (k : K) (v₀ v : V) :
    update (update m k v₀) k v = update m k v := by
  rw [update_def, update_def, update_def, toList_ofList, SAL.insert_insert]

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- `M[K <- undef] => M requires notBool K in_keys(M)` -/
@[k2l_hook] theorem remove_of_not_inKeys (m : M) (k : K) (h : inKeys k m = false) : remove m k = m := by
  unfold inKeys at h
  rw [MapRepr.lookupR_eq] at h
  have hn : SAL.lookup k (toList m) = none := by simpa using h
  rw [remove_def, SAL.erase_of_lookup_none hn, ofList_toList]

/-- `K in_keys(M[K <- undef]) => false`, for maps: at `[1 |-> 0, 1 |-> 1]` one binding of `1`
stays. -/
@[k2l_hook] theorem inKeys_remove_self (m : M) (k : K) (hw : WF m) : inKeys k (remove m k) = false := by
  unfold inKeys
  rw [MapRepr.lookupR_eq, remove_def, toList_ofList, SAL.lookup_erase_self _ hw]; rfl

/-- `K |-> V M` where `K` is not a key of the map `M`: `M[K <- V] => K |-> V M requires notBool
K in_keys(M)`. At an unsorted list, which is no map, `_Map_` is undefined. -/
@[k2l_hook] theorem concat_element_of_not_inKeys (m : M) (k : K) (v : V) (hw : WF m)
    (h : inKeys k m = false) : concat (element k v) m = some (update m k v) := by
  have hn : lookup m k = none := by unfold inKeys at h; rw [lookup]; simpa using h
  exact concat_element_iff.2 ⟨hw, hn, rfl⟩

/-- `(K |-> V0 M)[K <- V] => K |-> V M`, at every carrier value (both sides undefined where
`K |-> V0 M` is). -/
@[k2l_hook] theorem concat_element_update_self (k : K) (v₀ v : V) (m : M) :
    (concat (element k v₀) m).bind (fun r => some (update r k v)) = concat (element k v) m := by
  unfold concat element
  simp only [toList_ofList]
  cases h : SAL.concat [(k, v₀)] (toList m) with
  | none =>
    have h2 : SAL.concat [(k, v)] (toList m) = none := by
      cases h3 : SAL.concat [(k, v)] (toList m) with
      | none => rfl
      | some l =>
        obtain ⟨s, n, -⟩ := SAL.concat_singleton_iff.1 h3
        exact absurd (SAL.concat_singleton_iff.2 ⟨s, n, rfl⟩) (by rw [h]; simp)
    simp [h2]
  | some l =>
    obtain ⟨s, n, rfl⟩ := SAL.concat_singleton_iff.1 h
    have h2 : SAL.concat [(k, v)] (toList m) = some (SAL.insert k v (toList m)) :=
      SAL.concat_singleton_iff.2 ⟨s, n, rfl⟩
    simp [h2, update_def, toList_ofList, SAL.insert_insert]

/-- `(K1 |-> V1 M)[K2 <- undef] => K1 |-> V1 (M[K2 <- undef]) requires K1 =/=K K2`, for maps:
at `[1 |-> 0, 1 |-> 1]` with `K2 = 1` the left side is undefined and the right side is not. -/
@[k2l_hook] theorem concat_element_remove_ne {k₁ k₂ : K} (v₁ : V) (m : M) (hw : WF m) (hne : k₁ ≠ k₂) :
    (concat (element k₁ v₁) m).bind (fun r => some (remove r k₂)) =
      concat (element k₁ v₁) (remove m k₂) := by
  have hwr : WF (remove m k₂) := wf_remove hw
  have hlk : lookup (remove m k₂) k₁ = lookup m k₁ := by
    rw [lookup_def, lookup_def, remove_def, toList_ofList]
    unfold WF at hw
    apply Option.ext; intro v
    rw [SAL.lookup_iff_mem (SAL.sorted_erase hw), SAL.lookup_iff_mem hw, SAL.mem_erase_iff hw]
    exact ⟨fun h => h.1, fun h => ⟨h, hne⟩⟩
  cases hl : lookup m k₁ with
  | some u =>
    have h1 : concat (element k₁ v₁) m = none := by
      cases e : concat (element k₁ v₁) m with
      | none => rfl
      | some r => rw [(concat_element_iff.1 e).2.1] at hl; cases hl
    have h2 : concat (element k₁ v₁) (remove m k₂) = none := by
      cases e : concat (element k₁ v₁) (remove m k₂) with
      | none => rfl
      | some r => rw [(concat_element_iff.1 e).2.1, hl] at hlk; cases hlk
    rw [h1, h2]; rfl
  | none =>
    rw [concat_element_iff.2 ⟨hw, hl, rfl⟩, concat_element_iff.2 ⟨hwr, by rw [hlk, hl], rfl⟩]
    simp only [Option.bind_some, Option.some.injEq]
    rw [remove_def, update_def, update_def, remove_def, toList_ofList, toList_ofList]
    congr 1
    unfold WF at hw
    refine SAL.eq_of_mem_iff (SAL.sorted_erase (SAL.sorted_insert hw))
      (SAL.sorted_insert (SAL.sorted_erase hw)) fun p => ?_
    rw [SAL.mem_erase_iff (SAL.sorted_insert hw), SAL.mem_insert_iff hw,
      SAL.mem_insert_iff (SAL.sorted_erase hw), SAL.mem_erase_iff hw]
    constructor
    · rintro ⟨rfl | ⟨h, h1⟩, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨h, h2⟩, h1⟩
    · rintro (rfl | ⟨⟨h, h2⟩, h1⟩)
      · exact ⟨Or.inl rfl, hne⟩
      · exact ⟨Or.inr ⟨h, h1⟩, h2⟩

/-- `(K1 |-> V1 M)[K2 <- V2] => K1 |-> V1 (M[K2 <- V2]) requires K1 =/=K K2`, for maps (it also
holds at every other carrier value, where both sides are undefined). -/
@[k2l_hook] theorem concat_element_update_ne {k₁ k₂ : K} (v₁ v₂ : V) (m : M) (hw : WF m) (hne : k₁ ≠ k₂) :
    (concat (element k₁ v₁) m).bind (fun r => some (update r k₂ v₂)) =
      concat (element k₁ v₁) (update m k₂ v₂) := by
  have hlk : lookup (update m k₂ v₂) k₁ = lookup m k₁ := lookup_update_ne m v₂ hne
  cases hl : lookup m k₁ with
  | some u =>
    have h1 : concat (element k₁ v₁) m = none := by
      cases e : concat (element k₁ v₁) m with
      | none => rfl
      | some r => rw [(concat_element_iff.1 e).2.1] at hl; cases hl
    have h2 : concat (element k₁ v₁) (update m k₂ v₂) = none := by
      cases e : concat (element k₁ v₁) (update m k₂ v₂) with
      | none => rfl
      | some r => rw [(concat_element_iff.1 e).2.1, hl] at hlk; cases hlk
    rw [h1, h2]; rfl
  | none =>
    rw [concat_element_iff.2 ⟨hw, hl, rfl⟩, concat_element_iff.2 ⟨wf_update hw, by rw [hlk, hl], rfl⟩]
    simp only [Option.bind_some, Option.some.injEq]
    rw [update_def, update_def, update_def, update_def, toList_ofList, toList_ofList]
    congr 1
    unfold WF at hw
    refine SAL.eq_of_mem_iff (SAL.sorted_insert (SAL.sorted_insert hw))
      (SAL.sorted_insert (SAL.sorted_insert hw)) fun p => ?_
    rw [SAL.mem_insert_iff (SAL.sorted_insert hw), SAL.mem_insert_iff hw,
      SAL.mem_insert_iff (SAL.sorted_insert hw), SAL.mem_insert_iff hw]
    constructor
    · rintro (rfl | ⟨rfl | ⟨h, h1⟩, h2⟩)
      · exact Or.inr ⟨Or.inl rfl, hne.symm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr ⟨h, h2⟩, h1⟩
    · rintro (rfl | ⟨rfl | ⟨h, h1⟩, h2⟩)
      · exact Or.inr ⟨Or.inl rfl, hne⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr ⟨h, h2⟩, h1⟩

/-- `X in_keys(M[K <- V])`: a key of the result is `K` or a key of `M`. -/
@[k2l_hook] theorem inKeys_update [DecidableEq K] (m : M) (x k : K) (v : V) :
    inKeys x (update m k v) = (decide (x = k) || inKeys x m) := by
  by_cases h : x = k
  · subst h; simp [inKeys_update_same]
  · simp [h, inKeys_update_ne m v h]

/-- `X in_keys(K |-> V M)`, where `K |-> V M` is defined: as `X in_keys(M[K <- V])`. -/
@[k2l_hook] theorem bind_concat_element_inKeys [DecidableEq K] (x k : K) (v : V) (m : M) :
    (concat (element k v) m).bind (fun r => some (inKeys x r)) =
      (concat (element k v) m).bind (fun _ => some (decide (x = k) || inKeys x m)) := by
  cases h : concat (element k v) m with
  | none => rfl
  | some r =>
    obtain ⟨_, _, rfl⟩ := concat_element_iff.1 h
    simp [inKeys_update]

end KPrelude.MapHook

namespace KPrelude.SetHook

/-! ## `SET-KORE-SYMBOLIC`

As for maps: `intersectSet(S, S) => S`, `.Set |Set S => S` and `S |Set S => S` are false at a
carrier value that is no set (at `[2, 1]`, `lookup 1` stops at `2`), and take `SetHook.WF`. -/

open ListIso

variable {S K : Type} [Ord K] [ListIso S (K × Unit)] [MapRepr S K Unit]

/-- `S -Set .Set => S` -/
@[k2l_hook] theorem difference_unit_right (s : S) : difference s unit = s := by
  unfold difference unit MapHook.unit MapHook.inKeys
  simp only [MapRepr.lookupR_eq, toList_ofList, SAL.lookup, Option.isSome_none, Bool.not_false]
  rw [List.filter_eq_self.2 (by simp), ofList_toList]

/-- `.Set -Set S => .Set` -/
@[k2l_hook] theorem difference_unit_left (s : S) : difference unit s = (unit : S) := by
  unfold difference unit MapHook.unit; simp [toList_ofList]

/-- `S |Set .Set => S` -/
@[k2l_hook] theorem union_unit_right (s : S) : union s unit = s := by
  unfold union unit MapHook.unit; simp [toList_ofList]

/-- `intersectSet(S, .Set) => .Set` -/
@[k2l_hook] theorem intersection_unit_right (s : S) : intersection s unit = (unit : S) := by
  unfold intersection unit MapHook.unit MapHook.inKeys
  simp only [MapRepr.lookupR_eq, toList_ofList, SAL.lookup, Option.isSome_none]
  rw [List.filter_eq_nil_iff.2 (by simp)]

/-- `intersectSet(.Set, S) => .Set` -/
@[k2l_hook] theorem intersection_unit_left (s : S) : intersection unit s = (unit : S) := by
  unfold intersection unit MapHook.unit; simp [toList_ofList]

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem inKeys_of_mem {s : S} (hw : WF s) {p : K × Unit} (hp : p ∈ toList s) :
    MapHook.inKeys p.1 s = true := by
  unfold MapHook.inKeys; rw [MapRepr.lookupR_eq, SAL.lookup_of_mem hw hp]; rfl

/-- `intersectSet(S, S) => S`, for sets. -/
@[k2l_hook] theorem intersection_self (s : S) (hw : WF s) : intersection s s = s := by
  unfold intersection
  rw [List.filter_eq_self.2 (fun p hp => inKeys_of_mem hw hp), ofList_toList]

/-- A union whose elements are those of the set `b` is `b`. -/
theorem union_eq_of_mem {a b : S} (ha : WF a) (hb : WF b)
    (h : ∀ p, p ∈ toList a ∨ p ∈ toList b ↔ p ∈ toList b) : union a b = b := by
  unfold union
  have e : toList (List.foldl (fun s q => MapHook.update s q.1 ()) a (toList b)) = toList b :=
    SAL.eq_of_mem_iff (wf_foldl_update _ a ha) hb fun p => by
      rw [mem_toList_foldl_update, h]
  rw [← ofList_toList (List.foldl _ a _), e, ofList_toList]

/-- `.Set |Set S => S`, for sets. -/
@[k2l_hook] theorem union_unit_left (s : S) (hw : WF s) : union unit s = s :=
  union_eq_of_mem MapHook.wf_unit hw fun p => by simp [unit, MapHook.unit, toList_ofList]

/-- `S |Set S => S`, for sets. -/
@[k2l_hook] theorem union_self (s : S) (hw : WF s) : union s s = s :=
  union_eq_of_mem hw hw fun _ => ⟨fun h => h.elim id id, Or.inr⟩

/-- `SetItem(X)` added to the set `S` is defined exactly when `X` is not in `S`
(`#Ceil(S SetItem(X))`). -/
@[k2l_hook] theorem concat_element_isSome (s : S) (x : K) (hw : WF s) :
    (concat s (element x)).isSome = !(inSet x s) := by
  have hs : SAL.sortedb (toList s) = true := (SAL.sortedb_iff _).2 hw
  unfold concat MapHook.concat element MapHook.element inSet MapHook.inKeys
  rw [MapRepr.lookupR_eq, toList_ofList]
  simp only [SAL.concat, hs, Bool.true_and]
  have h1 : SAL.sortedb [(x, ())] = true :=
    (SAL.sortedb_iff _).2 (SAL.Sorted.cons (by simp) SAL.Sorted.nil)
  rw [h1]
  cases hl : SAL.lookup x (toList s) with
  | none =>
    have : (toList s).all (fun p => (SAL.lookup p.1 [(x, ())]).isNone) = true := by
      rw [List.all_eq_true]; intro p hp
      cases hc : compare p.1 x with
      | eq =>
        cases SAL.eq_of_cmp hc
        rw [SAL.lookup_of_mem (k := p.1) (v := p.2) hw (by simpa using hp)] at hl; cases hl
      | lt => simp [SAL.lookup, hc]
      | gt => simp [SAL.lookup, hc]
    simp [this]
  | some u =>
    have : (toList s).all (fun p => (SAL.lookup p.1 [(x, ())]).isNone) = false := by
      rw [Bool.eq_false_iff]; intro h
      have := List.all_eq_true.1 h _ (SAL.lookup_mem hl)
      simp [SAL.lookup] at this
    simp [this]

end KPrelude.SetHook

namespace KPrelude

/-! ## Partial terms whose value does not depend on what they bind -/

/-- `{b #Equals T}`, where `T` is `d` wherever the partial `o` is defined. -/
@[k2l_hook] theorem some_eq_bind_const {α β : Type} (o : Option α) (b d : β) :
    (some b = o.bind fun _ => some d) ↔ (o.isSome = true ∧ d = b) := by
  cases o <;> simp [eq_comm]

@[k2l_hook] theorem bind_const_eq_some {α β : Type} (o : Option α) (b d : β) :
    (o.bind (fun _ => some d) = some b) ↔ (o.isSome = true ∧ d = b) := by
  cases o <;> simp

-- the right-hand sides of `domains.md`'s `#Ceil` rules are nested conjunctions
attribute [k2l_hook] and_assoc

end KPrelude
