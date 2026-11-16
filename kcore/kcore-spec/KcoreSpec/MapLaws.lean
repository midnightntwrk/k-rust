/-
  KCore, checked layer: canonical maps toward `Exec.step_iff` (Exec.lean).

  - `entries_canon`: two maps with keys strictly increasing and the same entries are the same list, so a
    finite map has one canonical representation;
  - `union_spec`, `union_exists`: `union a b` (the `_Map_` hook) is defined exactly when the keys
    of `a` are apart from each other and from those of `b`, and then has the entries of both, with
    `b` kept in order;
  - `sortE_spec`: entries with keys apart have a canonical arrangement;
  - `canonV`: every map inside a value is canonical and no injection wraps an injection, which
    `sortOf` guarantees (`canonV_of_sortOf`).
-/
import KcoreSpec.ExecBasics

set_option autoImplicit false

namespace KCore

open GroundTerm

/-- The keys of the entries are pairwise apart. -/
def KeysApart (L : Entries) : Prop := L.Pairwise (fun e e' => cmp e.1 e'.1 ≠ .eq)

theorem apart_symm {e e' : GroundTerm × GroundTerm} (h : cmp e.1 e'.1 ≠ .eq) : cmp e'.1 e.1 ≠ .eq := by
  rw [cmp_swap]; intro h'; apply h
  cases hc : cmp e.1 e'.1 <;> rw [hc] at h' <;> first | rfl | cases h'

theorem KeysApart.perm {L L' : Entries} (h : KeysApart L) (hp : L.Perm L') : KeysApart L' :=
  List.Pairwise.perm h hp apart_symm

theorem sorted_pairwise : ∀ {es : Entries}, keysSorted es = true →
    es.Pairwise (fun e e' => cmp e.1 e'.1 = .lt)
  | [], _ => List.Pairwise.nil
  | (_k, _v) :: _es, h => List.Pairwise.cons (fun e he => keysSorted_lt_all h e he)
      (sorted_pairwise (keysSorted_cons.mp h).1)

theorem sorted_of_pairwise : ∀ {es : Entries}, es.Pairwise (fun e e' => cmp e.1 e'.1 = .lt) →
    keysSorted es = true
  | [], _ => rfl
  | (k, v) :: es, h => by
    rw [List.pairwise_cons] at h
    rw [keysSorted_cons]
    exact ⟨sorted_of_pairwise h.2, fun e he => h.1 e (List.mem_of_mem_head? he)⟩

theorem sorted_apart {es : Entries} (h : keysSorted es = true) : KeysApart es :=
  (sorted_pairwise h).imp fun h' => by rw [h']; exact nofun

theorem sorted_sublist {a b : Entries} (hs : a.Sublist b) (hb : keysSorted b = true) :
    keysSorted a = true :=
  sorted_of_pairwise (List.Pairwise.sublist hs (sorted_pairwise hb))

/-- A finite map has one canonical representation. -/
theorem entries_canon : ∀ {a b : Entries}, keysSorted a = true → keysSorted b = true →
    (∀ e, e ∈ a ↔ e ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], e :: _, _, _, h => absurd ((h e).mpr (List.mem_cons_self ..)) (by simp)
  | e :: _, [], _, _, h => absurd ((h e).mp (List.mem_cons_self ..)) (by simp)
  | e :: a, e' :: b, ha, hb, h => by
    have pa := sorted_pairwise ha
    have pb := sorted_pairwise hb
    rw [List.pairwise_cons] at pa pb
    have hee : e = e' := by
      rcases List.mem_cons.mp ((h e).mp (List.mem_cons_self ..)) with h1 | h1
      · exact h1
      rcases List.mem_cons.mp ((h e').mpr (List.mem_cons_self ..)) with h2 | h2
      · exact h2.symm
      have l1 := pb.1 e h1
      have l2 := pa.1 e' h2
      rw [cmp_swap, l2] at l1
      cases l1
    subst hee
    have irr : ∀ {l : Entries}, (∀ x ∈ l, cmp e.1 x.1 = .lt) → e ∉ l := fun hl hm => by
      have := hl e hm; rw [cmp_refl] at this; cases this
    have ht := entries_canon (sorted_of_pairwise pa.2) (sorted_of_pairwise pb.2) (fun x => by
      constructor
      · intro hx
        rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
        · exact absurd hx (irr pa.1)
        · exact hx'
      · intro hx
        rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
        · exact absurd hx (irr pb.1)
        · exact hx')
    rw [ht]

/-! ## `insertE` of a new key, `union` -/

theorem hasKey_false {k : GroundTerm} {m : Entries} :
    hasKey k m = false ↔ ∀ e ∈ m, cmp k e.1 ≠ .eq := by
  unfold hasKey
  rw [List.any_eq_false]
  exact forall_congr' fun e => imp_congr_right fun _ => by rw [beq_iff_eq]

theorem insertE_mem_of_new {k v : GroundTerm} : ∀ {es : Entries}, hasKey k es = false →
    ∀ e, e ∈ insertE k v es ↔ e = (k, v) ∨ e ∈ es
  | [], _, e => by simp [insertE]
  | (k', v') :: es, h, e => by
    have h' := hasKey_false.mp h
    have hk : cmp k k' ≠ .eq := h' _ (List.mem_cons_self ..)
    have hes : hasKey k es = false := hasKey_false.mpr fun e he => h' e (List.mem_cons_of_mem _ he)
    simp only [insertE]
    split
    · simp
    · contradiction
    · rw [List.mem_cons, insertE_mem_of_new hes, List.mem_cons]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inl h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inl h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

theorem insertE_sublist_of_new {k v : GroundTerm} : ∀ {es : Entries}, hasKey k es = false →
    es.Sublist (insertE k v es)
  | [], _ => by simp [insertE]
  | (k', v') :: es, h => by
    have h' := hasKey_false.mp h
    have hk : cmp k k' ≠ .eq := h' _ (List.mem_cons_self ..)
    have hes : hasKey k es = false := hasKey_false.mpr fun e he => h' e (List.mem_cons_of_mem _ he)
    simp only [insertE]
    split
    · exact List.sublist_cons_self _ _
    · contradiction
    · exact (insertE_sublist_of_new hes).cons_cons _

/-- What a defined union says: its entries are both maps', `b` is kept in order, the keys of `a`
are apart, and apart from those of `b`. -/
theorem union_spec : ∀ {a b m : Entries}, union a b = some m →
    (∀ e, e ∈ m ↔ e ∈ a ∨ e ∈ b) ∧ b.Sublist m ∧ KeysApart a ∧
      (∀ e ∈ a, ∀ e' ∈ b, cmp e.1 e'.1 ≠ .eq)
  | [], b, m, h => by
    simp only [union, Option.some.injEq] at h
    subst h
    exact ⟨by simp, List.Sublist.refl _, List.Pairwise.nil, by simp⟩
  | (k, v) :: es, b, m, h => by
    simp only [union, Option.bind_eq_some_iff] at h
    obtain ⟨m', hm', h⟩ := h
    simp only [addNew] at h
    split at h
    · cases h
    · rename_i hk
      cases h
      have hk' : hasKey k m' = false := by simpa using hk
      obtain ⟨hmem, hsub, hap, hdis⟩ := union_spec hm'
      have hnew := hasKey_false.mp hk'
      refine ⟨fun e => ?_, hsub.trans (insertE_sublist_of_new hk'), ?_, ?_⟩
      · rw [insertE_mem_of_new hk', hmem, List.mem_cons]
        constructor
        · rintro (h1 | h1 | h1)
          · exact Or.inl (Or.inl h1)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr h1
        · rintro ((h1 | h1) | h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h1)
      · exact List.Pairwise.cons (fun e he => hnew e ((hmem e).mpr (Or.inl he))) hap
      · intro e he e' he'
        rcases List.mem_cons.mp he with rfl | he
        · exact hnew e' ((hmem e').mpr (Or.inr he'))
        · exact hdis e he e' he'

/-- A union is defined when the keys are apart. -/
theorem union_exists : ∀ {a b : Entries}, KeysApart a → (∀ e ∈ a, ∀ e' ∈ b, cmp e.1 e'.1 ≠ .eq) →
    ∃ m, union a b = some m ∧ ∀ e, e ∈ m ↔ e ∈ a ∨ e ∈ b
  | [], b, _, _ => ⟨b, rfl, by simp⟩
  | (k, v) :: es, b, ha, hd => by
    rw [KeysApart, List.pairwise_cons] at ha
    obtain ⟨m', hm', hmem⟩ := union_exists ha.2 (fun e he e' he' => hd e (List.mem_cons_of_mem _ he) e' he')
    have hk : hasKey k m' = false := hasKey_false.mpr fun e he => by
      rcases (hmem e).mp he with he | he
      · exact ha.1 e he
      · exact hd (k, v) (List.mem_cons_self ..) e he
    refine ⟨insertE k v m', ?_, fun e => ?_⟩
    · simp [union, hm', addNew, hk]
    · rw [insertE_mem_of_new hk, hmem, List.mem_cons]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)

/-! ## A canonical arrangement of entries -/

def sortE (L : Entries) : Entries := L.foldr (fun e acc => insertE e.1 e.2 acc) []

theorem sortE_spec : ∀ {L : Entries}, KeysApart L →
    keysSorted (sortE L) = true ∧ ∀ e, e ∈ sortE L ↔ e ∈ L
  | [], _ => ⟨rfl, by simp [sortE]⟩
  | (k, v) :: L, h => by
    rw [KeysApart, List.pairwise_cons] at h
    obtain ⟨hs, hm⟩ := sortE_spec h.2
    have hk : hasKey k (sortE L) = false :=
      hasKey_false.mpr fun e he => h.1 e ((hm e).mp he)
    have hdef : sortE ((k, v) :: L) = insertE k v (sortE L) := rfl
    rw [hdef]
    refine ⟨insertE_sorted hs, fun e => ?_⟩
    rw [insertE_mem_of_new hk, hm, List.mem_cons]

/-! ## Canonical values -/

mutual
  /-- Every map inside is canonical, and no injection wraps an injection (inside sets too). -/
  def canonV : GroundTerm → Bool
    | .ctor _ ts => canonVs ts
    | .inj _ _ t => !t.isInj && canonV t
    | .dv _ _ => true
    | .map _ es => keysSorted es && canonEs es
    | .set _ es => canonVs es
    | .list _ es => canonVs es
    termination_by structural t => t
  def canonVs : List GroundTerm → Bool
    | [] => true
    | t :: ts => canonV t && canonVs ts
    termination_by structural ts => ts
  def canonEs : Entries → Bool
    | [] => true
    | e :: es => canonE e && canonEs es
    termination_by structural es => es
  def canonE : GroundTerm × GroundTerm → Bool
    | (k, v) => canonV k && canonV v
    termination_by structural e => e
end

theorem canonEs_mem : ∀ {es : Entries}, canonEs es = true → ∀ e ∈ es, canonV e.1 = true ∧ canonV e.2 = true
  | [], _, _, h => nomatch h
  | (k, v) :: es, h, e, he => by
    simp only [canonEs, canonE, Bool.and_eq_true] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact canonEs_mem h.2 e he

theorem canonEs_of_mem : ∀ {es : Entries}, (∀ e ∈ es, canonV e.1 = true ∧ canonV e.2 = true) →
    canonEs es = true
  | [], _ => rfl
  | (k, v) :: es, h => by
    simp only [canonEs, canonE, Bool.and_eq_true]
    exact ⟨h _ (List.mem_cons_self ..), canonEs_of_mem fun e he => h e (List.mem_cons_of_mem _ he)⟩

variable {c : Semantics}

mutual
  theorem canonV_of_sortOf : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → canonV v = true
    | .ctor f ts, s, h => by
      obtain ⟨ss, hss⟩ := c.sortsOf_of_sortOf_ctor h
      simp only [canonV]; exact canonVs_of_sortsOf hss
    | .inj a b t, s, h => by
      simp only [Semantics.sortOf] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
        simp only [canonV, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨hc.1.2, canonV_of_sortOf hc.2⟩
      · cases h
    | .dv _ _, _, _ => rfl
    | .map _ es, s, h => by
      obtain ⟨_, _, _, _, h1, h2, _⟩ := c.sortOf_map_inv h
      simp only [canonV, Bool.and_eq_true]
      exact ⟨(mapKeys_sorted h1).2, canonEs_of_entriesOK h2⟩
    | .set _ es, s, h => by
      simp only [Semantics.sortOf] at h
      split at h
      · rename_i _ ss _ hss
        simp only [canonV]; exact canonVs_of_sortsOf hss
      · cases h
    | .list _ es, s, h => by
      simp only [Semantics.sortOf] at h
      split at h
      · rename_i _ ss _ hss
        simp only [canonV]; exact canonVs_of_sortsOf hss
      · cases h
  termination_by structural v => v
  theorem canonVs_of_sortsOf : ∀ {ts : List GroundTerm} {ss : List Srt}, c.sortsOf ts = some ss →
      canonVs ts = true
    | [], _, _ => rfl
    | t :: ts, ss, h => by
      simp only [Semantics.sortsOf] at h
      split at h
      · rename_i s ss' ht hts
        simp only [canonVs, Bool.and_eq_true]
        exact ⟨canonV_of_sortOf ht, canonVs_of_sortsOf hts⟩
      · cases h
  termination_by structural ts => ts
  theorem canonEs_of_entriesOK : ∀ {ks vs : Srt} {es : Entries}, c.entriesOK ks vs es = true →
      canonEs es = true
    | _, _, [], _ => rfl
    | _, _, e :: es, h => by
      simp only [Semantics.entriesOK, Bool.and_eq_true] at h
      simp only [canonEs, Bool.and_eq_true]
      exact ⟨canonE_of_entryOK h.1, canonEs_of_entriesOK h.2⟩
  termination_by structural _ _ es => es
  theorem canonE_of_entryOK : ∀ {ks vs : Srt} {e : GroundTerm × GroundTerm}, c.entryOK ks vs e = true →
      canonE e = true
    | _, _, (k, v), h => by
      simp only [Semantics.entryOK, Bool.and_eq_true, beq_iff_eq] at h
      simp only [canonE, Bool.and_eq_true]
      exact ⟨canonV_of_sortOf h.1, canonV_of_sortOf h.2⟩
  termination_by structural _ _ e => e
end

end KCore
