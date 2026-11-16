/-
  KCore. A finite map keyed by natural numbers, as a binary trie (P1.2, findings/P1.2-tables.md). Frozen
  layer: the lookups of symbols by number (`lookupSig`, `Semantics.lookupFn`, `hook`) read one.

  A list lookup costs the kernel one comparison per entry before the key; the trie costs one step
  per binary digit of the key (about log₂ of the number of symbols), with the kernel's native `Nat`
  division. `ofList` builds the trie of a list of entries, the first entry of a key winning, so
  `find (ofList l) n` is the list's first entry for n (`find_ofList`): every lemma stated about the
  list lookup holds of the trie's. `ofList` nests one insertion per entry, so reaching any key
  unfolds all of them; `ofListBy` builds the trie from the root down, each level a filter of the
  list, so reaching key n unfolds about log₂ n levels (`find_ofListBy`; `hook` reads its table so).
-/
set_option autoImplicit false

namespace KCore

/-- A trie: the root holds the value of key 0; key 2m+1 is key m of the left subtrie, key 2m+2
key m of the right. -/
inductive NatMap (α : Type) where
  | leaf
  | node (v : Option α) (l r : NatMap α)
  deriving Repr, Inhabited, DecidableEq

namespace NatMap

variable {α : Type}

def find : NatMap α → Nat → Option α
  | leaf, _ => none
  | node v l r, n =>
    if n = 0 then v
    else if n % 2 = 1 then find l (n / 2) else find r (n / 2 - 1)

/-- The trie of one entry, with `f` steps of fuel (enough when `n < f`). Structural recursion, so
the kernel evaluates it directly. -/
def single : Nat → Nat → α → NatMap α
  | 0, _, _ => leaf
  | f + 1, n, a =>
    if n = 0 then node (some a) leaf leaf
    else if n % 2 = 1 then node none (single f (n / 2) a) leaf
    else node none leaf (single f (n / 2 - 1) a)

/-- Insert an entry, unless the key has one (the first entry wins). -/
def insertNew : NatMap α → Nat → α → NatMap α
  | leaf, n, a => single (n + 1) n a
  | node v l r, n, a =>
    if n = 0 then node (v <|> some a) l r
    else if n % 2 = 1 then node v (insertNew l (n / 2) a) r
    else node v l (insertNew r (n / 2 - 1) a)

def ofList : List (Nat × α) → NatMap α
  | l => l.foldl (fun t e => insertNew t e.1 e.2) leaf

theorem find_leaf (n : Nat) : find (leaf : NatMap α) n = none := rfl

theorem find_single : ∀ (f n : Nat) (a : α) (m : Nat), n < f →
    find (single f n a) m = if m = n then some a else none
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, a, m, h => by
    unfold single
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      by_cases hm : m = 0
      · subst hm; rfl
      · simp only [find, hm, ite_false]; split <;> rfl
    · simp only [hn, ite_false]
      split
      · rename_i hodd
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, ite_false]
          split
          · rw [find_single f (n / 2) a (m / 2) (by omega)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 ≠ n / 2 := fun h => hmn (by omega)
              simp [this, hmn]
          · rename_i hmeven
            have hmn : m ≠ n := fun h => hmeven (h ▸ hodd)
            simp [hmn, find_leaf]
      · rename_i heven
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, ite_false]
          split
          · rename_i hmodd
            have hmn : m ≠ n := fun h => heven (h ▸ hmodd)
            simp [hmn, find_leaf]
          · rename_i hmeven
            rw [find_single f (n / 2 - 1) a (m / 2 - 1) (by omega)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 - 1 ≠ n / 2 - 1 := fun h => hmn (by omega)
              simp [this, hmn]

theorem find_insertNew : ∀ (t : NatMap α) (n : Nat) (a : α) (m : Nat),
    find (insertNew t n a) m = if m = n then (find t m <|> some a) else find t m
  | leaf, n, a, m => by
    rw [insertNew, find_single _ _ _ _ (Nat.lt_succ_self n)]
    by_cases hmn : m = n <;> simp [hmn, find_leaf]
  | node v l r, n, a, m => by
    unfold insertNew
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      by_cases hm : m = 0
      · subst hm; simp [find]
      · simp [find, hm]
    · simp only [hn, ite_false]
      split
      · rename_i hodd
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, ite_false]
          split
          · rw [find_insertNew l (n / 2) a (m / 2)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 ≠ n / 2 := fun h => hmn (by omega)
              simp [this, hmn]
          · rename_i hmeven
            have hmn : m ≠ n := fun h => hmeven (h ▸ hodd)
            simp [hmn]
      · rename_i heven
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, ite_false]
          split
          · rename_i hmodd
            have hmn : m ≠ n := fun h => heven (h ▸ hmodd)
            simp [hmn]
          · rw [find_insertNew r (n / 2 - 1) a (m / 2 - 1)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 - 1 ≠ n / 2 - 1 := fun h => hmn (by omega)
              simp [this, hmn]

theorem find_foldl : ∀ (l : List (Nat × α)) (t : NatMap α) (n : Nat),
    find (l.foldl (fun t e => insertNew t e.1 e.2) t) n = (find t n <|> (l.find? (·.1 == n)).map (·.2))
  | [], t, n => by simp
  | (k, a) :: l, t, n => by
    rw [List.foldl_cons, find_foldl l, find_insertNew]
    by_cases h : n = k
    · subst h
      cases find t n <;> simp
    · have : (k == n) = false := by simpa [beq_iff_eq] using Ne.symm h
      simp [h, this]

/-- The trie of a list finds the list's first entry of each key. -/
theorem find_ofList (l : List (Nat × α)) (n : Nat) : find (ofList l) n = (l.find? (·.1 == n)).map (·.2) := by
  rw [ofList, find_foldl, find_leaf]; simp

/-! ## Updating an entry, and grouping pairs by their first component -/

/-- Replace the entry of n by `f` of the old one. -/
def update : NatMap α → Nat → (Option α → α) → NatMap α
  | leaf, n, f => single (n + 1) n (f none)
  | node v l r, n, f =>
    if n = 0 then node (some (f v)) l r
    else if n % 2 = 1 then node v (update l (n / 2) f) r
    else node v l (update r (n / 2 - 1) f)

theorem find_update : ∀ (t : NatMap α) (n : Nat) (f : Option α → α) (m : Nat),
    find (update t n f) m = if m = n then some (f (find t n)) else find t m
  | leaf, n, f, m => by
    rw [update, find_single _ _ _ _ (Nat.lt_succ_self n)]
    by_cases hmn : m = n <;> simp [hmn, find_leaf]
  | node v l r, n, f, m => by
    unfold update
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      by_cases hm : m = 0
      · subst hm; simp [find]
      · simp [find, hm]
    · simp only [hn, ite_false]
      split
      · rename_i hodd
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, hn, hodd, ite_false, ite_true]
          split
          · rw [find_update l (n / 2) f (m / 2)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 ≠ n / 2 := fun h => hmn (by omega)
              simp [this, hmn]
          · rename_i hmeven
            have hmn : m ≠ n := fun h => hmeven (h ▸ hodd)
            simp [hmn]
      · rename_i heven
        by_cases hm : m = 0
        · subst hm; simp [find, Ne.symm hn]
        · simp only [find, hm, hn, heven, ite_false]
          split
          · rename_i hmodd
            have hmn : m ≠ n := fun h => heven (h ▸ hmodd)
            simp [hmn]
          · rw [find_update r (n / 2 - 1) f (m / 2 - 1)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m / 2 - 1 ≠ n / 2 - 1 := fun h => hmn (by omega)
              simp [this, hmn]

/-- The pairs grouped by their first component: n ↦ the second components of the pairs (n, _). -/
def group (l : List (Nat × Nat)) : NatMap (List Nat) :=
  l.foldl (fun t e => update t e.1 fun o => e.2 :: o.getD []) leaf

/-- The second components of the pairs with first component n. -/
def succs (t : NatMap (List Nat)) (n : Nat) : List Nat := (find t n).getD []

theorem mem_succs_foldl : ∀ (l : List (Nat × Nat)) (t : NatMap (List Nat)) (n d : Nat),
    d ∈ succs (l.foldl (fun t e => update t e.1 fun o => e.2 :: o.getD []) t) n ↔
      d ∈ succs t n ∨ (n, d) ∈ l
  | [], t, n, d => by simp
  | (a, b) :: l, t, n, d => by
    rw [List.foldl_cons, mem_succs_foldl l]
    simp only [succs, find_update, List.mem_cons, Prod.mk.injEq]
    by_cases h : n = a
    · subst h
      simp only [ite_true, Option.getD_some, List.mem_cons, true_and]
      exact ⟨fun h => by rcases h with (h | h) | h <;> simp_all, fun h => by rcases h with h | h | h <;> simp_all⟩
    · simp only [h, ite_false, false_and, false_or]

theorem mem_group (l : List (Nat × Nat)) (n d : Nat) : d ∈ succs (group l) n ↔ (n, d) ∈ l := by
  rw [group, mem_succs_foldl]; simp [succs, find_leaf]

/-! ## The trie of a list, built level by level -/

/-- The entries of the odd keys 2m+1, as keys m. -/
def oddKeys (l : List (Nat × α)) : List (Nat × α) :=
  l.filterMap fun e => if e.1 % 2 = 1 then some (e.1 / 2, e.2) else none

/-- The entries of the even keys 2m+2, as keys m. -/
def evenKeys (l : List (Nat × α)) : List (Nat × α) :=
  l.filterMap fun e => if e.1 % 2 = 0 ∧ e.1 ≠ 0 then some (e.1 / 2 - 1, e.2) else none

/-- The trie of a list built from the root down, `f` levels deep: the root holds the first entry of
key 0, the left subtrie is that of the odd keys (`oddKeys`), the right that of the even keys but 0
(`evenKeys`). Reaching key n unfolds about log₂ n levels, each a filter of the list one level up,
however long the list (`ofList` nests one insertion per entry, so reaching any key unfolds them
all). `find (ofListBy f l) n` is the list's first entry for n when n + 1 < 2^f, and none otherwise
(`find_ofListBy`). -/
def ofListBy : Nat → List (Nat × α) → NatMap α
  | 0, _ => leaf
  | f + 1, l => node ((l.find? (·.1 == 0)).map (·.2)) (ofListBy f (oddKeys l)) (ofListBy f (evenKeys l))

theorem find?_oddKeys (l : List (Nat × α)) (m : Nat) :
    ((oddKeys l).find? (·.1 == m)).map (·.2) = (l.find? (·.1 == 2 * m + 1)).map (·.2) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, a⟩ := e
    unfold oddKeys at ih ⊢
    by_cases hk : k % 2 = 1
    · rw [List.filterMap_cons_some (b := (k / 2, a)) (by simp [hk])]
      by_cases hkm : k = 2 * m + 1
      · have : k / 2 = m := by omega
        rw [List.find?_cons_of_pos (by simp [this]), List.find?_cons_of_pos (by simp [hkm])]; rfl
      · have : k / 2 ≠ m := by omega
        rw [List.find?_cons_of_neg (by simp [this]), List.find?_cons_of_neg (by simp [hkm])]
        exact ih
    · have hkm : k ≠ 2 * m + 1 := by omega
      rw [List.filterMap_cons_none (by simp [hk]), List.find?_cons_of_neg (by simp [hkm])]
      exact ih

theorem find?_evenKeys (l : List (Nat × α)) (m : Nat) :
    ((evenKeys l).find? (·.1 == m)).map (·.2) = (l.find? (·.1 == 2 * m + 2)).map (·.2) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, a⟩ := e
    unfold evenKeys at ih ⊢
    by_cases hk : k % 2 = 0 ∧ k ≠ 0
    · rw [List.filterMap_cons_some (b := (k / 2 - 1, a)) (by simp [hk])]
      by_cases hkm : k = 2 * m + 2
      · have : k / 2 - 1 = m := by omega
        rw [List.find?_cons_of_pos (by simp [this]), List.find?_cons_of_pos (by simp [hkm])]; rfl
      · have : k / 2 - 1 ≠ m := by omega
        rw [List.find?_cons_of_neg (by simp [this]), List.find?_cons_of_neg (by simp [hkm])]
        exact ih
    · have hkm : k ≠ 2 * m + 2 := by omega
      rw [List.filterMap_cons_none (by simp only [hk]; rfl), List.find?_cons_of_neg (by simp [hkm])]
      exact ih

/-- The trie built level by level, `f` levels deep, finds the list's first entry of each key n with
n + 1 < 2^f, and nothing at the others. -/
theorem find_ofListBy : ∀ (f : Nat) (l : List (Nat × α)) (n : Nat),
    find (ofListBy f l) n = if n + 1 < 2 ^ f then (l.find? (·.1 == n)).map (·.2) else none
  | 0, _, n => by simp [ofListBy, find]
  | f + 1, l, n => by
    rw [ofListBy, find]
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    by_cases hn : n = 0
    · subst hn
      rw [if_pos (show 0 + 1 < 2 ^ (f + 1) by omega)]; rfl
    · simp only [hn, ite_false]
      split
      · rename_i hodd
        rw [find_ofListBy f _ _, find?_oddKeys]
        have : 2 * (n / 2) + 1 = n := by omega
        rw [this]
        by_cases hb : n / 2 + 1 < 2 ^ f
        · rw [if_pos hb, if_pos (by omega)]
        · rw [if_neg hb, if_neg (by omega)]
      · rename_i heven
        rw [find_ofListBy f _ _, find?_evenKeys]
        have : 2 * (n / 2 - 1) + 2 = n := by omega
        rw [this]
        by_cases hb : n / 2 - 1 + 1 < 2 ^ f
        · rw [if_pos hb, if_pos (by omega)]
        · rw [if_neg hb, if_neg (by omega)]

end NatMap

end KCore
