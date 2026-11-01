import KPrelude.InvDisjoint

/-!
# A measure summed over the bindings of a map

A measure over a cell map (the work left in each task of a coordination script) is written in K as
a fold that adds each binding's weight: `F(.Map) => 0` and `F((K |-> V) R) => g(K, V) +Int F(R)`.
As for a fold of claims (`InvDisjoint`), `K |-> V R` matches modulo associativity and commutativity,
so K fixes no order of the walk. Unlike a fold of claims, the fold's value does not depend on it:
`+Int` is associative and commutative, so every order gives the same total when every binding's
weight is defined, and none does when one is not. The value is `sumOf g m`, the sum of the weights
in the canonical order, which is the sum in any order (`sumOf_concat`, by permutation).

- `fold_sum`: from a fold's instances, its value is `sumOf g m`, and every binding matches the
  fold's patterns with its weight defined (`ClaimsDef T g m`, the predicate of a fold of claims,
  here at `Int`); `fold_sum_isSome`: the fold is defined where that holds.
- `sumOf_concat`, `sumOf_element`, `sumOf_unit`: the sum of a defined `M₁ M₂` is the sum of both,
  which is what a rule's case reads at the maps it matches (`K |-> V REST`) and builds.
- `sumOf_nonneg`: with every weight nonnegative, so is the sum.
-/

set_option linter.unusedSectionVars false

namespace KPrelude.MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- The sum of the weights of a list of bindings (`0` where a weight is undefined). -/
def sumL (g : K → V → Option Int) (ps : List (K × V)) : Int :=
  (ps.map fun p => (g p.1 p.2).getD 0).sum

/-- The sum of the weights of the bindings of `m`. -/
def sumOf (g : K → V → Option Int) (m : M) : Int := sumL g (toList m)

theorem sumL_perm {g : K → V → Option Int} {ps qs : List (K × V)} (h : ps.Perm qs) :
    sumL g ps = sumL g qs := by
  unfold sumL
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.map_cons, List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem sumL_cons (g : K → V → Option Int) (p : K × V) (ps : List (K × V)) :
    sumL g (p :: ps) = (g p.1 p.2).getD 0 + sumL g ps := by
  simp [sumL]

/-- The sum of a defined `M₁ M₂` is the sum of both operands. -/
theorem sumOf_concat {g : K → V → Option Int} {a b m : M} (h : concat a b = some m) :
    sumOf g m = sumOf g a + sumOf g b := by
  unfold sumOf
  rw [sumL_perm (perm_toList_concat h)]
  simp [sumL]

theorem sumOf_element (g : K → V → Option Int) (k : K) (v : V) :
    sumOf g (element k v : M) = (g k v).getD 0 := by
  simp [sumOf, sumL, element, toList_ofList]

theorem sumOf_unit (g : K → V → Option Int) : sumOf g (unit : M) = 0 := by
  simp [sumOf, sumL, unit, toList_ofList]

/-- The operands of a defined `M₁ M₂` are well formed: the hook checks both. -/
theorem wf_operands_of_concat {a b m : M} (h : concat a b = some m) : WF a ∧ WF b := by
  unfold concat at h
  obtain ⟨l, e, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨ha, hb, -⟩ := SAL.concat_eq_some_iff.1 e
  exact ⟨ha, hb⟩

/-- With every weight nonnegative, the sum is. -/
theorem sumOf_nonneg {g : K → V → Option Int} (hg : ∀ k v a, g k v = some a → 0 ≤ a) (m : M) :
    0 ≤ sumOf g m := by
  unfold sumOf sumL
  induction toList m with
  | nil => simp
  | cons p t ih =>
    rw [List.map_cons, List.sum_cons]
    have : 0 ≤ (g p.1 p.2).getD 0 := by
      cases h : g p.1 p.2 with
      | none => simp
      | some a => simpa using hg _ _ _ h
    omega

/-- A fold that adds the weight of each binding, from its instances: `F(.Map) => 0` and, at a
nonempty map, a binding whose weight `a` is defined, the rest's sum `r`, and `F`'s value `a + r`.
Its value is the sum of every binding's weight, and each binding matches the patterns (`T`) with
its weight defined. By induction on the number of bindings, as `fold_claims`. -/
theorem fold_sum {F : M → Option Int} {T : K → V → Prop} {g : K → V → Option Int}
    (h1 : F unit = some 0)
    (h2 : ∀ m s, m ≠ unit → F m = some s → WF m ∧ ∃ k v a r, (k, v) ∈ toList m ∧ T k v ∧
      g k v = some a ∧ F (remove m k) = some r ∧ s = a + r)
    (m : M) (s : Int) (h : F m = some s) : ClaimsDef T g m ∧ s = sumOf g m := by
  suffices H : ∀ n (m : M) (s : Int), (toList m).length = n → F m = some s →
      ClaimsDef T g m ∧ s = sumOf g m from H _ m s rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m s hn h
    by_cases hu : m = unit
    · subst hu
      rw [h1] at h
      cases h
      exact ⟨claimsDef_unit, (sumOf_unit g).symm⟩
    obtain ⟨hw, k, v, a, r, hk, ht, hg, hr, hs⟩ := h2 m s hu h
    have hlt : (toList (remove m k)).length < n := by
      rw [← hn, (perm_toList_remove hw hk).length_eq, List.length_cons]
      exact Nat.lt_succ_self _
    obtain ⟨hd, hrs⟩ := ih _ hlt (remove m k) r rfl hr
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.1 ((perm_toList_remove hw hk).mem_iff.1 hp) with rfl | hp
      · rw [hg]; exact ⟨ht, rfl⟩
      · exact hd p hp
    · unfold sumOf
      rw [sumL_perm (perm_toList_remove hw hk), sumL_cons, hg, Option.getD_some, hs, hrs]
      rfl

/-- The fold is defined wherever every binding matches its patterns with its weight defined: from
its instances, at a nonempty well-formed map whose every binding has a defined weight and a defined
rest, the fold is defined. -/
theorem fold_sum_isSome {F : M → Option Int} {T : K → V → Prop} {g : K → V → Option Int}
    (h1 : F unit = some 0)
    (h3 : ∀ m, m ≠ unit → WF m → (∀ k v, (k, v) ∈ toList m → (T k v ∧ (g k v).isSome) ∧
      (F (remove m k)).isSome) → (F m).isSome)
    (m : M) (hw : WF m) (hd : ClaimsDef T g m) : (F m).isSome := by
  suffices H : ∀ n (m : M), (toList m).length = n → WF m → ClaimsDef T g m → (F m).isSome from
    H _ m rfl hw hd
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hw hd
    by_cases hu : m = unit
    · subst hu; rw [h1]; rfl
    refine h3 m hu hw fun k v hk => ⟨hd (k, v) hk, ?_⟩
    have hlt : (toList (remove m k)).length < n := by
      rw [← hn, (perm_toList_remove hw hk).length_eq, List.length_cons]
      exact Nat.lt_succ_self _
    refine ih _ hlt (remove m k) rfl (wf_remove hw) fun p hp => hd p ?_
    rw [remove_def, toList_ofList] at hp
    exact SAL.mem_erase hp

/-- The fold's value where every binding matches with a defined weight: the sum. -/
theorem fold_sum_eq {F : M → Option Int} {T : K → V → Prop} {g : K → V → Option Int}
    (hs : ∀ m s, F m = some s → ClaimsDef T g m ∧ s = sumOf g m)
    (hi : ∀ m, WF m → ClaimsDef T g m → (F m).isSome)
    {m : M} (hw : WF m) (hd : ClaimsDef T g m) : F m = some (sumOf g m) := by
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.1 (hi m hw hd)
  rw [h, (hs m s h).2]

end KPrelude.MapHook
