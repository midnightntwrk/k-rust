/-
  KCore, checked layer: `GroundTerm.cmp` is a total order (reflexive on equal terms, `.eq` only on
  equal terms, antisymmetric by `swap`, transitive), and the map operations of Hooks.lean keep
  map entries in canonical form (`insertE`, `eraseK`, `union`). Used by subject reduction
  (F2/SubjectReduction.lean): a map hook returns a map value.
-/
import KcoreSpec.Hooks

set_option autoImplicit false

namespace KCore

namespace GroundTerm

/-! ## Strings and `andThen` -/

theorem scmp_refl (s : String) : scmp s s = .eq := by simp [scmp]

theorem scmp_eq {s t : String} (h : scmp s t = .eq) : s = t := by
  unfold scmp at h
  by_cases he : s = t
  · exact he
  · rw [if_neg he] at h
    split at h <;> cases h

theorem scmp_lt {s t : String} : scmp s t = .lt ↔ s < t := by
  unfold scmp
  by_cases he : s = t
  · subst he; simp [String.lt_irrefl]
  · rw [if_neg he]
    by_cases hl : s < t <;> simp [hl]

theorem String.lt_of_ne_not_lt {s t : String} (he : s ≠ t) (hl : ¬ s < t) : t < s :=
  Classical.byContradiction fun h' =>
    he (String.le_antisymm (String.not_lt.mp h') (String.not_lt.mp hl))

theorem scmp_swap (s t : String) : scmp t s = (scmp s t).swap := by
  unfold scmp
  by_cases he : s = t
  · subst he; simp
  · have he' : t ≠ s := fun h => he h.symm
    rw [if_neg he, if_neg he']
    by_cases hl : s < t
    · rw [if_pos hl, if_neg (String.lt_asymm hl)]; rfl
    · rw [if_neg hl, if_pos (String.lt_of_ne_not_lt he hl)]; rfl

theorem scmp_trans {a b c : String} (h1 : scmp a b = .lt) (h2 : scmp b c = .lt) :
    scmp a c = .lt :=
  scmp_lt.mpr (String.lt_trans (scmp_lt.mp h1) (scmp_lt.mp h2))

/-! ## Numbers, Ints, Bools and literals -/

theorem ncmp_refl (s : Nat) : ncmp s s = .eq := by simp [ncmp]
theorem ncmp_eq {s t : Nat} (h : ncmp s t = .eq) : s = t := by
  unfold ncmp at h
  by_cases he : s = t
  · exact he
  · rw [if_neg he] at h
    split at h <;> cases h
theorem ncmp_lt {s t : Nat} : ncmp s t = .lt ↔ s < t := by
  unfold ncmp
  by_cases he : s = t
  · subst he; simp
  · rw [if_neg he]
    by_cases hl : s < t <;> simp [hl]
theorem ncmp_swap (s t : Nat) : ncmp t s = (ncmp s t).swap := by
  unfold ncmp
  by_cases he : s = t
  · subst he; simp
  · rw [if_neg he, if_neg (Ne.symm he)]
    by_cases hl : s < t
    · rw [if_pos hl, if_neg (Nat.lt_asymm hl)]; rfl
    · rw [if_neg hl, if_pos (by omega)]; rfl
theorem ncmp_trans {a b c : Nat} (h1 : ncmp a b = .lt) (h2 : ncmp b c = .lt) : ncmp a c = .lt :=
  ncmp_lt.mpr (Nat.lt_trans (ncmp_lt.mp h1) (ncmp_lt.mp h2))

theorem icmp_refl (s : Int) : icmp s s = .eq := by simp [icmp]
theorem icmp_eq {s t : Int} (h : icmp s t = .eq) : s = t := by
  unfold icmp at h
  by_cases he : s = t
  · exact he
  · rw [if_neg he] at h
    split at h <;> cases h
theorem icmp_lt {s t : Int} : icmp s t = .lt ↔ s < t := by
  unfold icmp
  by_cases he : s = t
  · subst he; simp
  · rw [if_neg he]
    by_cases hl : s < t <;> simp [hl]
theorem icmp_swap (s t : Int) : icmp t s = (icmp s t).swap := by
  unfold icmp
  by_cases he : s = t
  · subst he; simp
  · rw [if_neg he, if_neg (Ne.symm he)]
    by_cases hl : s < t
    · rw [if_pos hl, if_neg (Int.lt_asymm hl)]; rfl
    · rw [if_neg hl, if_pos (by omega)]; rfl
theorem icmp_trans {a b c : Int} (h1 : icmp a b = .lt) (h2 : icmp b c = .lt) : icmp a c = .lt :=
  icmp_lt.mpr (Int.lt_trans (icmp_lt.mp h1) (icmp_lt.mp h2))

theorem bcmp_refl (s : Bool) : bcmp s s = .eq := by simp [bcmp]
theorem bcmp_eq {s t : Bool} (h : bcmp s t = .eq) : s = t := by
  cases s <;> cases t <;> simp_all [bcmp]
theorem bcmp_swap (s t : Bool) : bcmp t s = (bcmp s t).swap := by
  cases s <;> cases t <;> rfl
theorem bcmp_trans {a b c : Bool} (h1 : bcmp a b = .lt) (h2 : bcmp b c = .lt) : bcmp a c = .lt := by
  cases a <;> cases b <;> cases c <;> simp_all [bcmp]

theorem andThen_eq {o p : Ordering} : andThen o p = .eq ↔ o = .eq ∧ p = .eq := by
  cases o <;> cases p <;> simp [andThen]

theorem andThen_lt {o p : Ordering} : andThen o p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> simp [andThen]

theorem andThen_swap (o p : Ordering) : (andThen o p).swap = andThen o.swap p.swap := by
  cases o <;> cases p <;> rfl

/-- Lexicographic transitivity: first components ordered by an order whose `.eq` is equality. -/
theorem andThen_trans {α : Type} (cmpα : α → α → Ordering) (heq : ∀ x y, cmpα x y = .eq → x = y)
    {x y z : α} (hxy : cmpα x y = .lt → cmpα y z = .lt → cmpα x z = .lt)
    {p q r : Ordering} (hpq : p = .lt → q = .lt → r = .lt)
    (h1 : andThen (cmpα x y) p = .lt) (h2 : andThen (cmpα y z) q = .lt)
    (hxz : x = z → cmpα x z = .eq) : andThen (cmpα x z) r = .lt := by
  rw [andThen_lt] at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (hxy h1 h2)
  · rw [← heq _ _ e2]; exact Or.inl h1
  · rw [heq _ _ e1]; exact Or.inl h2
  · have hx := heq _ _ e1
    have hy := heq _ _ e2
    subst hx; subst hy
    exact Or.inr ⟨hxz rfl, hpq h1 h2⟩

theorem fcmp_refl (p e b : Nat) : andThen (ncmp p p) (andThen (ncmp e e) (ncmp b b)) = .eq := by
  simp [ncmp_refl, andThen]
theorem fcmp_eq {p e b p' e' b' : Nat} (h : andThen (ncmp p p') (andThen (ncmp e e') (ncmp b b')) = .eq) :
    Lit.float p e b = .float p' e' b' := by
  rw [andThen_eq, andThen_eq] at h
  rw [ncmp_eq h.1, ncmp_eq h.2.1, ncmp_eq h.2.2]
theorem fcmp_swap (p e b p' e' b' : Nat) :
    andThen (ncmp p' p) (andThen (ncmp e' e) (ncmp b' b)) =
      (andThen (ncmp p p') (andThen (ncmp e e') (ncmp b b'))).swap := by
  rw [ncmp_swap p, ncmp_swap e, ncmp_swap b, andThen_swap, andThen_swap]
theorem fcmp_trans {p e b p' e' b' p'' e'' b'' : Nat}
    (h1 : andThen (ncmp p p') (andThen (ncmp e e') (ncmp b b')) = .lt)
    (h2 : andThen (ncmp p' p'') (andThen (ncmp e' e'') (ncmp b' b'')) = .lt) :
    andThen (ncmp p p'') (andThen (ncmp e e'') (ncmp b b'')) = .lt := by
  have t2 : ∀ {e b e' b' e'' b'' : Nat}, andThen (ncmp e e') (ncmp b b') = .lt →
      andThen (ncmp e' e'') (ncmp b' b'') = .lt → andThen (ncmp e e'') (ncmp b b'') = .lt :=
    fun h1 h2 => andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans ncmp_trans h1 h2
      (fun h => h ▸ ncmp_refl _)
  exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans t2 h1 h2 (fun h => h ▸ ncmp_refl _)

theorem lcmp_refl (l : Lit) : lcmp l l = .eq := by
  cases l <;> simp [lcmp, icmp_refl, bcmp_refl, scmp_refl, fcmp_refl]
theorem lcmp_eq {l m : Lit} (h : lcmp l m = .eq) : l = m := by
  cases l <;> cases m <;> simp only [lcmp, reduceCtorEq] at h
  · rw [icmp_eq h]
  · rw [bcmp_eq h]
  · rw [scmp_eq h]
  · exact fcmp_eq h
theorem lcmp_swap (l m : Lit) : lcmp m l = (lcmp l m).swap := by
  cases l <;> cases m <;> simp only [lcmp] <;>
    first | rfl | apply icmp_swap | apply bcmp_swap | apply scmp_swap | apply fcmp_swap
theorem lcmp_trans {a b c : Lit} (h1 : lcmp a b = .lt) (h2 : lcmp b c = .lt) : lcmp a c = .lt := by
  cases a <;> cases b <;> cases c <;> simp only [lcmp, reduceCtorEq] at h1 h2 ⊢
  · exact icmp_trans h1 h2
  · exact bcmp_trans h1 h2
  · exact scmp_trans h1 h2
  · exact fcmp_trans h1 h2

/-! ## The four laws, by the recursor of the nested type -/

theorem cmp_refl : ∀ a : GroundTerm, cmp a a = .eq := by
  intro a
  refine GroundTerm.rec (motive_1 := fun a => cmp a a = .eq)
    (motive_2 := fun as => cmpList as as = .eq)
    (motive_3 := fun es => cmpEntries es es = .eq)
    (motive_4 := fun e => cmpPair e e = .eq) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro f as ih; simp only [cmp, ncmp_refl, ih, andThen]
  · intro a b t ih; simp only [cmp, ncmp_refl, ih, andThen]
  · intro s l; simp only [cmp, ncmp_refl, lcmp_refl, andThen]
  · intro s es ih; simp only [cmp, ncmp_refl, ih, andThen]
  · intro s es ih; simp only [cmp, ncmp_refl, ih, andThen]
  · intro s es ih; simp only [cmp, ncmp_refl, ih, andThen]
  · simp only [cmpList]
  · intro x xs ih ihs; simp only [cmpList, ih, ihs, andThen]
  · simp only [cmpEntries]
  · intro e es ih ihs; simp only [cmpEntries, ih, ihs, andThen]
  · intro k v ihk ihv; simp only [cmpPair, ihk, ihv, andThen]

theorem cmp_eq : ∀ a b : GroundTerm, cmp a b = .eq → a = b := by
  intro a
  refine GroundTerm.rec (motive_1 := fun a => ∀ b, cmp a b = .eq → a = b)
    (motive_2 := fun as => ∀ bs, cmpList as bs = .eq → as = bs)
    (motive_3 := fun es => ∀ es', cmpEntries es es' = .eq → es = es')
    (motive_4 := fun e => ∀ e', cmpPair e e' = .eq → e = e') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro f as ih b h
    cases b <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq] at h
    rw [ncmp_eq h.1, ih _ h.2]
  · intro a b t ih b' h
    cases b' <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq, andThen_eq] at h
    rw [ncmp_eq h.1, ncmp_eq h.2.1, ih _ h.2.2]
  · intro s l b h
    cases b <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq] at h
    rw [ncmp_eq h.1, lcmp_eq h.2]
  · intro s es ih b h
    cases b <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq] at h
    rw [ncmp_eq h.1, ih _ h.2]
  · intro s es ih b h
    cases b <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq] at h
    rw [ncmp_eq h.1, ih _ h.2]
  · intro s es ih b h
    cases b <;> simp only [cmp, reduceCtorEq] at h
    rw [andThen_eq] at h
    rw [ncmp_eq h.1, ih _ h.2]
  · intro bs h; cases bs <;> simp_all [cmpList]
  · intro x xs ih ihs bs h
    cases bs with
    | nil => simp [cmpList] at h
    | cons y ys =>
      simp only [cmpList, andThen_eq] at h
      rw [ih _ h.1, ihs _ h.2]
  · intro es' h; cases es' <;> simp_all [cmpEntries]
  · intro e es ih ihs es' h
    cases es' with
    | nil => simp [cmpEntries] at h
    | cons e' es' =>
      simp only [cmpEntries, andThen_eq] at h
      rw [ih _ h.1, ihs _ h.2]
  · intro k v ihk ihv e' h
    obtain ⟨k', v'⟩ := e'
    simp only [cmpPair, andThen_eq] at h
    rw [ihk _ h.1, ihv _ h.2]

theorem cmp_swap : ∀ a b : GroundTerm, cmp b a = (cmp a b).swap := by
  intro a
  refine GroundTerm.rec (motive_1 := fun a => ∀ b, cmp b a = (cmp a b).swap)
    (motive_2 := fun as => ∀ bs, cmpList bs as = (cmpList as bs).swap)
    (motive_3 := fun es => ∀ es', cmpEntries es' es = (cmpEntries es es').swap)
    (motive_4 := fun e => ∀ e', cmpPair e' e = (cmpPair e e').swap) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro f as ih b
    cases b <;> simp only [cmp] <;> try rfl
    rw [ncmp_swap, ih, andThen_swap]
  · intro a b t ih b'
    cases b' <;> simp only [cmp] <;> try rfl
    simp only [ncmp_swap a, ncmp_swap b, ih, andThen_swap]
  · intro s l b
    cases b <;> simp only [cmp] <;> try rfl
    simp only [ncmp_swap s, lcmp_swap l, andThen_swap]
  · intro s es ih b
    cases b <;> simp only [cmp] <;> try rfl
    rw [ncmp_swap s, ih, andThen_swap]
  · intro s es ih b
    cases b <;> simp only [cmp] <;> try rfl
    rw [ncmp_swap s, ih, andThen_swap]
  · intro s es ih b
    cases b <;> simp only [cmp] <;> try rfl
    rw [ncmp_swap s, ih, andThen_swap]
  · intro bs; cases bs <;> rfl
  · intro x xs ih ihs bs
    cases bs with
    | nil => rfl
    | cons y ys => simp only [cmpList]; rw [ih, ihs, andThen_swap]
  · intro es'; cases es' <;> rfl
  · intro e es ih ihs es'
    cases es' with
    | nil => rfl
    | cons e' es' => simp only [cmpEntries]; rw [ih, ihs, andThen_swap]
  · intro k v ihk ihv e'
    obtain ⟨k', v'⟩ := e'
    simp only [cmpPair]; rw [ihk, ihv, andThen_swap]

/-- The kind of a term: the order between terms of different constructors. -/
def kind : GroundTerm → Nat
  | .ctor .. => 0
  | .inj .. => 1
  | .dv .. => 2
  | .map .. => 3
  | .set .. => 4
  | .list .. => 5

theorem cmp_of_kind_lt {a b : GroundTerm} (h : kind a < kind b) : cmp a b = .lt := by
  cases a <;> cases b <;> simp [kind] at h <;> simp only [cmp]

theorem kind_le_of_cmp_lt {a b : GroundTerm} (h : cmp a b = .lt) : kind a ≤ kind b := by
  cases a <;> cases b <;> simp only [cmp, reduceCtorEq] at h <;> simp [kind]

theorem cmp_trans : ∀ a b c : GroundTerm, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt := by
  intro a
  refine GroundTerm.rec
    (motive_1 := fun a => ∀ b c, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt)
    (motive_2 := fun as => ∀ bs cs, cmpList as bs = .lt → cmpList bs cs = .lt → cmpList as cs = .lt)
    (motive_3 := fun es => ∀ es' es'', cmpEntries es es' = .lt → cmpEntries es' es'' = .lt →
      cmpEntries es es'' = .lt)
    (motive_4 := fun e => ∀ e' e'', cmpPair e e' = .lt → cmpPair e' e'' = .lt → cmpPair e e'' = .lt)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro f as ih b c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans (ih _ _) h1 h2
      (fun e => e ▸ ncmp_refl _)
  · intro a b t ih b' c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b' <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans
      (fun h1 h2 => andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans (ih _ _) h1 h2
        (fun e => e ▸ ncmp_refl _))
      h1 h2 (fun e => e ▸ ncmp_refl _)
  · intro s l b c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    all_goals first
      | exact cmp_of_kind_lt (by simp [kind])
      | exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans lcmp_trans h1 h2
          (fun e => e ▸ ncmp_refl _)
  · intro s es ih b c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    all_goals first
      | exact cmp_of_kind_lt (by simp [kind])
      | exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans (ih _ _) h1 h2
          (fun e => e ▸ ncmp_refl _)
  · intro s es ih b c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    all_goals first
      | exact cmp_of_kind_lt (by simp [kind])
      | exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans (ih _ _) h1 h2
          (fun e => e ▸ ncmp_refl _)
  · intro s es ih b c h1 h2
    have k1 := kind_le_of_cmp_lt h1
    have k2 := kind_le_of_cmp_lt h2
    cases b <;> cases c <;> simp [kind] at k1 k2 <;> simp only [cmp] at h1 h2 ⊢
    all_goals first
      | exact cmp_of_kind_lt (by simp [kind])
      | exact andThen_trans ncmp (fun _ _ => ncmp_eq) ncmp_trans (ih _ _) h1 h2
          (fun e => e ▸ ncmp_refl _)
  · intro bs cs h1 h2
    cases bs <;> cases cs <;> simp_all [cmpList]
  · intro x xs ih ihs bs cs h1 h2
    cases bs with
    | nil => simp [cmpList] at h1
    | cons y ys =>
      cases cs with
      | nil => simp [cmpList] at h2
      | cons z zs =>
        simp only [cmpList] at h1 h2 ⊢
        exact andThen_trans cmp cmp_eq (ih _ _) (ihs _ _) h1 h2 (fun e => e ▸ cmp_refl _)
  · intro es' es'' h1 h2
    cases es' <;> cases es'' <;> simp_all [cmpEntries]
  · intro e es ih ihs es' es'' h1 h2
    cases es' with
    | nil => simp [cmpEntries] at h1
    | cons e' es' =>
      cases es'' with
      | nil => simp [cmpEntries] at h2
      | cons e'' es'' =>
        simp only [cmpEntries] at h1 h2 ⊢
        have hpe : ∀ x y : GroundTerm × GroundTerm, cmpPair x y = .eq → x = y := by
          intro ⟨k, v⟩ ⟨k', v'⟩ h
          simp only [cmpPair, andThen_eq] at h
          rw [cmp_eq _ _ h.1, cmp_eq _ _ h.2]
        have hpr : ∀ x : GroundTerm × GroundTerm, cmpPair x x = .eq := fun ⟨k, v⟩ => by
          simp only [cmpPair, cmp_refl, andThen]
        exact andThen_trans cmpPair hpe (ih _ _) (ihs _ _) h1 h2 (fun he => he ▸ hpr _)
  · intro k v ihk ihv e' e'' h1 h2
    obtain ⟨k', v'⟩ := e'
    obtain ⟨k'', v''⟩ := e''
    simp only [cmpPair] at h1 h2 ⊢
    exact andThen_trans cmp cmp_eq (ihk _ _) (ihv _ _) h1 h2 (fun e => e ▸ cmp_refl _)

theorem cmp_gt_swap {a b : GroundTerm} (h : cmp a b = .gt) : cmp b a = .lt := by
  rw [cmp_swap, h]; rfl

end GroundTerm

/-! ## Map operations keep entries sorted -/

open GroundTerm

/-- Keys strictly increasing, as a predicate on the first key. -/
theorem keysSorted_cons {k v : GroundTerm} {es : Entries} :
    keysSorted ((k, v) :: es) = true ↔
      keysSorted es = true ∧ ∀ e ∈ es.head?, cmp k e.1 = .lt := by
  cases es with
  | nil => simp [keysSorted]
  | cons e es =>
    obtain ⟨k', v'⟩ := e
    simp [keysSorted, and_comm]

/-- In sorted entries, the first key is below every other key. -/
theorem keysSorted_lt_all : ∀ {k v : GroundTerm} {es : Entries},
    keysSorted ((k, v) :: es) = true → ∀ e ∈ es, cmp k e.1 = .lt
  | _, _, [], _, _, h => nomatch h
  | k, v, (k', v') :: es, h, e, he => by
    rw [keysSorted_cons] at h
    have h1 : cmp k k' = .lt := h.2 _ rfl
    rcases List.mem_cons.mp he with rfl | he
    · exact h1
    · exact cmp_trans _ _ _ h1 (keysSorted_lt_all h.1 e he)

theorem insertE_head {k v : GroundTerm} : ∀ {es : Entries} {x : GroundTerm × GroundTerm},
    x ∈ (insertE k v es).head? → x.1 = k ∨ x ∈ es.head?
  | [], x, h => by simp [insertE] at h; exact Or.inl (h ▸ rfl)
  | (k', v') :: es, x, h => by
    simp only [insertE] at h
    split at h <;> simp at h <;> subst h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem insertE_sorted {k v : GroundTerm} : ∀ {es : Entries}, keysSorted es = true →
    keysSorted (insertE k v es) = true
  | [], _ => by simp [insertE, keysSorted]
  | (k', v') :: es, h => by
    simp only [insertE]
    split
    · rename_i hlt
      rw [keysSorted_cons]
      exact ⟨h, fun e he => by simp at he; subst he; exact hlt⟩
    · rename_i heq
      have := cmp_eq _ _ heq
      subst this
      rw [keysSorted_cons] at h ⊢
      exact h
    · rename_i hgt
      rw [keysSorted_cons] at h ⊢
      refine ⟨insertE_sorted h.1, fun e he => ?_⟩
      rcases insertE_head he with he | he
      · rw [he]; exact cmp_gt_swap hgt
      · exact h.2 e he

theorem eraseK_sublist {k : GroundTerm} : ∀ {es : Entries} {e : GroundTerm × GroundTerm},
    e ∈ eraseK k es → e ∈ es
  | [], _, h => h
  | (k', v') :: es, e, h => by
    simp only [eraseK] at h
    split at h
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (eraseK_sublist h)

theorem eraseK_sorted {k : GroundTerm} : ∀ {es : Entries}, keysSorted es = true →
    keysSorted (eraseK k es) = true
  | [], _ => rfl
  | (k', v') :: es, h => by
    simp only [eraseK]
    split
    · exact (keysSorted_cons.mp h).1
    · rw [keysSorted_cons]
      refine ⟨eraseK_sorted (keysSorted_cons.mp h).1, fun e he => ?_⟩
      have hm : e ∈ eraseK k es := List.mem_of_mem_head? he
      exact keysSorted_lt_all h e (eraseK_sublist hm)

theorem union_sorted : ∀ {a b m : Entries}, keysSorted b = true → union a b = some m →
    keysSorted m = true
  | [], b, m, hb, h => by simp [union] at h; exact h ▸ hb
  | (k, v) :: es, b, m, hb, h => by
    simp only [union, Option.bind_eq_some_iff] at h
    obtain ⟨m', hm', h⟩ := h
    simp only [addNew] at h
    split at h
    · cases h
    · cases h
      exact insertE_sorted (union_sorted hb hm')

/-! ## Map operations keep entries of a property -/

theorem insertE_mem {k v : GroundTerm} : ∀ {es : Entries} {e : GroundTerm × GroundTerm},
    e ∈ insertE k v es → e = (k, v) ∨ e ∈ es
  | [], e, h => by simp [insertE] at h; exact Or.inl h
  | (k', v') :: es, e, h => by
    simp only [insertE] at h
    split at h
    · simpa using h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self ..)
      · rcases insertE_mem h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem union_mem : ∀ {a b m : Entries}, union a b = some m → ∀ e ∈ m, e ∈ a ∨ e ∈ b
  | [], b, m, h, e, he => by simp [union] at h; exact Or.inr (h ▸ he)
  | (k, v) :: es, b, m, h, e, he => by
    simp only [union, Option.bind_eq_some_iff] at h
    obtain ⟨m', hm', h⟩ := h
    simp only [addNew] at h
    split at h
    · cases h
    · cases h
      rcases insertE_mem he with he | he
      · exact Or.inl (he ▸ List.mem_cons_self ..)
      · rcases union_mem hm' e he with he | he
        · exact Or.inl (List.mem_cons_of_mem _ he)
        · exact Or.inr he

theorem findK_mem {k : GroundTerm} : ∀ {es : Entries} {v : GroundTerm}, findK k es = some v →
    ∃ k', (k', v) ∈ es
  | [], _, h => nomatch h
  | (k', v') :: es, v, h => by
    simp only [findK] at h
    split at h
    · cases h; exact ⟨k', List.mem_cons_self ..⟩
    · obtain ⟨k'', hm⟩ := findK_mem h
      exact ⟨k'', List.mem_cons_of_mem _ hm⟩

end KCore
