/-
  KCore, checked layer: what `wf` gives of a core's numbering and subsorts (toward `Exec.step_iff`).

  `srReady_of` and `matchReady_of`: the two decidable conditions `step_iff_of` (StepIff.lean)
  and subject reduction (SubjectReduction.lean) take hold of every core with the conjuncts below
  (`sortedOK` and the three name conditions; `matchReady` also no overloading symbol), so of every
  core `wf` accepts (`srReady_of_wf`; `matchReady_of_wf` without overloading symbols).
  - From `idsOK` (P1.1: the definition's own sorts and symbols are numbered densely after the
    registry's): the library's sorts (registry numbers below the generated cells') and the
    definition's sorts (numbered from `nRegSorts`, or the generated cells' `Srt.top` to
    `Srt.counterOpt`, each once) are pairwise apart and none is KItem. Before P1.1 these facts
    came from the shape of the names (a cell sort ends in `Cell`, its `Opt` sort in `Opt`, a
    predicate is `Lblis` followed by the sort).
  - From `hooksApart`: no constructor of the definition (the cells' among them) is a map pattern
    symbol.
  - From `predsApart`: the functions evaluation reads have distinct labels.
  - From `subsortsOK`: the declared pairs (the cells' `XCell < XCellOpt` among them) relate the
    definition's and the library's sorts, and their closure
    (`declaredClosure`) is irreflexive. The closure is transitive whatever the pairs
    (`declaredClosure_trans`): `Nat.repeat` composes with the declared pairs once per pair, and a
    shortest chain of declared pairs never repeats a sort, so it uses each pair at most once.
-/
import KcoreSpec.MatchComplete

set_option autoImplicit false

namespace KCore.NamesApart

open KCore KCore

variable {c : KCore.Semantics}

/-- `omega` over sort and symbol numbers (`Srt`, `Sym` are `Nat`, which `omega` sees only unfolded). -/
local macro "somega" : tactic => `(tactic| ((try simp only [KCore.Srt, KCore.Sym, Srt.top, Srt.topFrag,
  Srt.counter, Srt.counterOpt, Srt.kitem, Srt.k, nRegSorts, nRegSyms, topLabel, topFragLabel, counterLabel,
  noCounter] at *) <;> omega))

/-! ## The definition's sorts -/

/-- `idsOK` holds the library's facts (`Lib.ok`). -/
theorem lib_ok (h : c.idsOK = true) : c.lib.ok = true := by
  unfold Semantics.idsOK at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2

theorem nodupB_iff : ∀ (l : List Srt), nodup l = true ↔ l.Nodup
  | [] => by simp [nodup]
  | a :: l => by
    simp only [nodup, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, nodupB_iff l]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun hm => by simp [List.contains_iff_mem, hm] at h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [List.contains_iff_mem] using h1, h2⟩

theorem lib_ok_parts (h : c.lib.ok = true) :
    (c.lib.sortsBelowKItem.all fun s => decide (s < nRegSorts) && !(decide (17 ≤ s) && decide (s ≤ 20)) && s != Srt.kitem) = true ∧
    nodup c.lib.sortsBelowKItem = true ∧
    (c.lib.subsorts.all fun p => c.lib.sortsBelowKItem.contains p.fst && c.lib.sortsBelowKItem.contains p.snd) = true ∧
    (c.lib.ctors.all fun k => !patternHooks.contains k.name) = true := by
  unfold Lib.ok at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The library's sorts below KItem are registry sorts, none KItem or a generated cell's. -/
theorem lib_sorts_lt (h : c.lib.ok = true) :
    ∀ s ∈ c.lib.sortsBelowKItem, s < nRegSorts ∧ ¬(17 ≤ s ∧ s ≤ 20) ∧ s ≠ Srt.kitem := by
  intro s hs
  have h1 := List.all_eq_true.mp (lib_ok_parts h).1 s hs
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at h1
  obtain ⟨⟨h1, h2⟩, h3⟩ := h1
  refine ⟨h1, fun ⟨a, b⟩ => ?_, h3⟩
  rcases h2 with h2 | h2
  · exact h2 a
  · exact h2 b

theorem lib_sorts_nodup (h : c.lib.ok = true) : c.lib.sortsBelowKItem.Nodup :=
  (nodupB_iff _).mp (lib_ok_parts h).2.1

/-- A list is without repetition when the elements of each side of a predicate are. -/
theorem nodup_of_filter (p : Srt → Bool) : ∀ (l : List Srt),
    (l.filter p).Nodup → (l.filter fun s => !p s).Nodup → l.Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    cases ha : p a
    · rw [List.filter_cons_of_neg (by simp [ha])] at h1
      rw [List.filter_cons_of_pos (by simp [ha]), List.nodup_cons] at h2
      refine List.nodup_cons.mpr ⟨fun hm => h2.1 (List.mem_filter.mpr ⟨hm, by simp [ha]⟩),
        nodup_of_filter p l h1 h2.2⟩
    · rw [List.filter_cons_of_pos (by simp [ha]), List.nodup_cons] at h1
      rw [List.filter_cons_of_neg (by simp [ha])] at h2
      exact List.nodup_cons.mpr ⟨fun hm => h1.1 (List.mem_filter.mpr ⟨hm, ha⟩),
        nodup_of_filter p l h1.2 h2⟩

/-- What `idsOK` gives of the sorts: those of `userSorts` numbered from `nRegSorts` are numbered
densely, each once; the others are the generated configuration's (17 to 20), each once. -/
theorem own_sorts (h : c.idsOK = true) :
    c.userSorts.Nodup ∧ ∀ s ∈ c.userSorts, nRegSorts ≤ s ∨ (17 ≤ s ∧ s ≤ 20) := by
  unfold Semantics.idsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have he : c.ownSorts = _ := h.1.1.1
  obtain ⟨⟨⟨hreg, hgen⟩, -⟩, -⟩ := h.2
  unfold Semantics.ownSorts at he
  have hown : (c.userSorts.filter fun s => decide (nRegSorts ≤ s)).Nodup := by
    rw [he]; exact List.nodup_range' ..
  have hreg' : (c.userSorts.filter fun s => !decide (nRegSorts ≤ s)).Nodup := by
    have : (c.userSorts.filter fun s => !decide (nRegSorts ≤ s)) = c.userSorts.filter fun s => decide (s < nRegSorts) :=
      List.filter_congr fun s _ => by by_cases hs : s < nRegSorts <;> simp [hs] <;> omega
    rw [this]; exact (nodupB_iff _).mp hreg
  refine ⟨nodup_of_filter (fun s => decide (nRegSorts ≤ s)) _ hown hreg', fun s hs => ?_⟩
  by_cases hge : nRegSorts ≤ s
  · exact Or.inl hge
  · right
    have hm := List.all_eq_true.mp hgen s (List.mem_filter.mpr ⟨hs, by simpa using Nat.lt_of_not_le hge⟩)
    simp only [genSorts, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide

/-- The library's and the definition's sorts are apart and each without repetition; KItem is
none of them. -/
theorem sorts_facts (h : c.idsOK = true) :
    (c.lib.sortsBelowKItem ++ c.userSorts).Nodup ∧ Srt.kitem ∉ c.sortsBelowKItem := by
  obtain ⟨hnd, hge⟩ := own_sorts h
  have hlt := lib_sorts_lt (lib_ok h)
  refine ⟨List.nodup_append.mpr ⟨lib_sorts_nodup (lib_ok h), hnd, ?_⟩, ?_⟩
  · intro a ha b hb he
    subst he
    rcases hge a hb with hb | hb
    · have := (hlt a ha).1; somega
    · exact (hlt a ha).2.1 hb
  · intro hk
    simp only [Semantics.sortsBelowKItem, List.mem_append] at hk
    rcases hk with hk | hk
    · exact (hlt _ hk).2.2 rfl
    · rcases hge _ hk with hk | hk
      · exact absurd hk (by decide)
      · exact absurd hk.1 (by decide)

theorem mem_sortsBelowKItem {s : Srt} :
    s ∈ c.sortsBelowKItem ↔ s ∈ c.lib.sortsBelowKItem ∨ s ∈ c.userSorts := by
  unfold Semantics.sortsBelowKItem
  simp only [List.mem_append]

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map (S := fun x y => x ≠ y) f (fun _ _ hab he => hab (congrArg f he)) h

/-! ## The closure of the declared subsorts is transitive -/

section Closure

variable (R : List (Srt × Srt))

/-- One round of `declaredClosure` (`closureStep`, Core.lean). -/
abbrev step (acc : List (Srt × Srt)) : List (Srt × Srt) := closureStep R acc

/-- A chain of declared pairs from `a` to `d` through the sorts `vs` (each pair's second sort). -/
inductive Walk : Srt → Srt → List Srt → Prop where
  | one {a d : Srt} : (a, d) ∈ R → Walk a d [d]
  | cons {a b d : Srt} {vs : List Srt} : (a, b) ∈ R → Walk b d vs → Walk a d (b :: vs)

variable {R}

theorem Walk.snoc : ∀ {a b d : Srt} {vs : List Srt}, Walk R a b vs → (b, d) ∈ R →
    Walk R a d (vs ++ [d])
  | _, _, _, _, .one h, h' => .cons h (.one h')
  | _, _, _, _, .cons h w, h' => .cons h (w.snoc h')

theorem Walk.append : ∀ {a b : Srt} {e : Srt} {vs ws : List Srt}, Walk R a b vs → Walk R b e ws →
    Walk R a e (vs ++ ws)
  | _, _, _, _, _, .one h, w => .cons h w
  | _, _, _, _, _, .cons h w, w' => .cons h (w.append w')

theorem Walk.length_pos : ∀ {a d : Srt} {vs : List Srt}, Walk R a d vs → 1 ≤ vs.length
  | _, _, _, .one _ => by simp
  | _, _, _, .cons _ _ => by simp

theorem Walk.split {a : Srt} {e : Srt} {vs : List Srt} (w : Walk R a e vs) :
    ∀ (xs : List Srt) (y : Srt) (ys : List Srt), vs = xs ++ y :: ys →
      (ys = [] ∧ y = e) ∨ Walk R y e ys := by
  induction w with
  | one h =>
    intro xs y ys he
    cases xs with
    | nil => simp only [List.nil_append, List.cons.injEq] at he; exact Or.inl ⟨he.2.symm, he.1.symm⟩
    | cons x xs => have := congrArg List.length he; simp at this
  | cons h w ih =>
    intro xs y ys he
    cases xs with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr w
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact ih xs y ys he.2

/-- A chain without a repeated sort, no longer than the given one. -/
theorem Walk.shorten : ∀ {a : Srt} {e : Srt} {vs : List Srt}, Walk R a e vs →
    ∃ ws, Walk R a e ws ∧ ws.Nodup ∧ ws.length ≤ vs.length
  | _, _, _, .one h => ⟨_, .one h, (by simp), Nat.le_refl _⟩
  | _, _, _, .cons (b := b) (vs := vs) h w => by
    obtain ⟨ws, w', hnd, hle⟩ := w.shorten
    by_cases hb : b ∈ ws
    · obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hb
      rcases w'.split xs b ys rfl with ⟨rfl, rfl⟩ | w''
      · exact ⟨_, .one h, (by simp), by simp⟩
      · refine ⟨b :: ys, .cons h w'', hnd.sublist (List.sublist_append_right _ _), ?_⟩
        simp only [List.length_append, List.length_cons] at hle ⊢
        omega
    · exact ⟨b :: ws, .cons h w', List.nodup_cons.mpr ⟨hb, hnd⟩, by simp; omega⟩

/-- The declared pairs along a chain. -/
theorem Walk.edges : ∀ {a d : Srt} {vs : List Srt}, Walk R a d vs →
    ∃ es : List (Srt × Srt), es ⊆ R ∧ es.map (·.2) = vs
  | _, _, _, .one h => ⟨[_], by simpa using h, rfl⟩
  | _, _, _, .cons h w => by
    obtain ⟨es, hs, he⟩ := w.edges
    exact ⟨_ :: es, List.cons_subset.mpr ⟨h, hs⟩, by simp [he]⟩

theorem Walk.length_le {a d : Srt} {vs : List Srt} (w : Walk R a d vs) (h : vs.Nodup) :
    vs.length ≤ R.length := by
  obtain ⟨es, hs, rfl⟩ := w.edges
  rw [List.length_map]
  exact (nodup_of_map _ h).length_le_of_subset hs

theorem Walk.unsnoc : ∀ {a d : Srt} {vs : List Srt}, Walk R a d vs → 2 ≤ vs.length →
    ∃ b vs', Walk R a b vs' ∧ (b, d) ∈ R ∧ vs = vs' ++ [d]
  | _, _, _, .one _, h => by simp at h
  | a, d, _, .cons (b := b) h (.one h'), _ => ⟨b, [b], .one h, h', rfl⟩
  | a, d, _, .cons (b := b) h (.cons (b := b') (vs := vs) h' w), _ => by
    obtain ⟨b'', vs'', w'', hR, he⟩ := Walk.unsnoc (.cons h' w)
      (by have := w.length_pos; simp only [List.length_cons]; omega)
    exact ⟨b'', b :: vs'', .cons h w'', hR, by rw [he]; rfl⟩

theorem repeat_succ (k : Nat) : Nat.repeat (step R) (k + 1) R = step R (Nat.repeat (step R) k R) := rfl

theorem repeat_succ' {f : List (Srt × Srt) → List (Srt × Srt)} (k : Nat) (a : List (Srt × Srt)) :
    Nat.repeat f (k + 1) a = f (Nat.repeat f k a) := rfl

theorem repeat_shift {f : List (Srt × Srt) → List (Srt × Srt)} : ∀ (k : Nat) (a : List (Srt × Srt)),
    Nat.repeat f (k + 1) a = Nat.repeat f k (f a)
  | 0, _ => rfl
  | k + 1, a => by rw [repeat_succ', repeat_shift k a]; rfl

theorem mem_step_of {acc : List (Srt × Srt)} {p : Srt × Srt} (h : p ∈ acc) :
    p ∈ step R acc := List.mem_append_left _ h

theorem compose_mem {acc : List (Srt × Srt)} {a b d : Srt} (h : (a, b) ∈ acc)
    (h' : (b, d) ∈ R) : (a, d) ∈ step R acc := by
  unfold step closureStep
  by_cases hin : (a, d) ∈ acc
  · exact List.mem_append_left _ hin
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a, b), h, List.mem_filterMap.mpr ⟨d, ?_, ?_⟩⟩)
    · exact (NatMap.mem_group R b d).mpr h'
    · have : (NatMap.succs (NatMap.group acc) a).contains d = false := by
        rw [Bool.eq_false_iff]; intro hc
        exact hin ((NatMap.mem_group acc a d).mp (List.contains_iff_mem.mp hc))
      simp only [this, Bool.false_eq_true, ite_false]

theorem mem_step {acc : List (Srt × Srt)} {p : Srt × Srt} (h : p ∈ step R acc) :
    p ∈ acc ∨ ∃ b, (p.1, b) ∈ acc ∧ (b, p.2) ∈ R := by
  unfold step closureStep at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · obtain ⟨⟨a, b⟩, hab, h⟩ := List.mem_flatMap.mp h
    obtain ⟨d, hd, h⟩ := List.mem_filterMap.mp h
    split at h
    · cases h
    · cases h
      exact Or.inr ⟨b, hab, (NatMap.mem_group R b d).mp hd⟩

theorem walk_of_mem : ∀ (k : Nat) {p : Srt × Srt}, p ∈ Nat.repeat (step R) k R →
    ∃ vs, Walk R p.1 p.2 vs
  | 0, p, h => ⟨_, .one h⟩
  | k + 1, p, h => by
    rw [repeat_succ] at h
    rcases mem_step h with h | ⟨b, hab, hbd⟩
    · exact walk_of_mem k h
    · obtain ⟨vs, w⟩ := walk_of_mem k hab
      exact ⟨_, w.snoc hbd⟩

theorem mem_of_walk : ∀ (k : Nat) {a d : Srt} {vs : List Srt}, Walk R a d vs →
    vs.length ≤ k + 1 → (a, d) ∈ Nat.repeat (step R) k R
  | 0, a, d, vs, w, h => by
    cases w with
    | one h' => exact h'
    | cons _ w' => have := w'.length_pos; simp only [List.length_cons] at h; omega
  | k + 1, a, d, vs, w, h => by
    rw [repeat_succ]
    by_cases hk : vs.length ≤ k + 1
    · exact mem_step_of (mem_of_walk k w hk)
    · obtain ⟨b, vs', w', hR, rfl⟩ := w.unsnoc (by omega)
      simp only [List.length_append, List.length_singleton] at h hk
      exact compose_mem (mem_of_walk k w' (by omega)) hR

theorem mem_repeat_ends : ∀ (k : Nat) {p : Srt × Srt}, p ∈ Nat.repeat (step R) k R →
    (∃ d, (p.1, d) ∈ R) ∧ (∃ a, (a, p.2) ∈ R)
  | 0, p, h => ⟨⟨_, h⟩, ⟨_, h⟩⟩
  | k + 1, p, h => by
    rw [repeat_succ] at h
    rcases mem_step h with h | ⟨b, hab, hbd⟩
    · exact mem_repeat_ends k h
    · exact ⟨(mem_repeat_ends k hab).1, ⟨_, hbd⟩⟩

/-- The closure after one round per declared pair is transitive. -/
theorem repeat_trans {a b : Srt} {e : Srt} (h1 : (a, b) ∈ Nat.repeat (step R) R.length R)
    (h2 : (b, e) ∈ Nat.repeat (step R) R.length R) : (a, e) ∈ Nat.repeat (step R) R.length R := by
  obtain ⟨vs, w1⟩ := walk_of_mem _ h1
  obtain ⟨ws, w2⟩ := walk_of_mem _ h2
  obtain ⟨us, w, hnd, -⟩ := (w1.append w2).shorten
  exact mem_of_walk _ w (Nat.le_succ_of_le (w.length_le hnd))

/-- A round that adds nothing leaves the pairs as they are. -/
theorem step_eq_of_length {acc : List (Srt × Srt)} (h : (step R acc).length = acc.length) : step R acc = acc := by
  have e : ∀ X : List (Srt × Srt), (acc ++ X).length = acc.length → acc ++ X = acc := fun X hX => by
    rw [List.length_append] at hX
    have h0 : X = [] := List.length_eq_zero_iff.mp (by omega)
    rw [h0, List.append_nil]
  exact e _ h

theorem repeat_fix {acc : List (Srt × Srt)} (h : step R acc = acc) : ∀ k, Nat.repeat (step R) k acc = acc
  | 0 => rfl
  | k + 1 => by rw [repeat_succ', repeat_fix h k, h]

/-- `closeRounds` stops early only at a fixed point, so it is the closure after k rounds. -/
theorem closeRounds_eq : ∀ (k : Nat) (acc : List (Srt × Srt)), closeRounds R k acc = Nat.repeat (step R) k acc
  | 0, _ => rfl
  | k + 1, acc => by
    unfold closeRounds
    simp only [beq_iff_eq]
    split
    · rename_i h
      have hfix := step_eq_of_length (R := R) h
      rw [repeat_shift, hfix, repeat_fix hfix]
    · rw [closeRounds_eq k, repeat_shift]

end Closure

theorem declaredClosure_eq :
    c.declaredClosure = Nat.repeat (step (c.userSubsorts ++ c.lib.subsorts))
      (c.userSubsorts ++ c.lib.subsorts).length (c.userSubsorts ++ c.lib.subsorts) := by
  unfold Semantics.declaredClosure
  exact closeRounds_eq _ _

theorem declaredClosure_trans {a b : Srt} {e : Srt} (h1 : (a, b) ∈ c.declaredClosure)
    (h2 : (b, e) ∈ c.declaredClosure) : (a, e) ∈ c.declaredClosure := by
  rw [declaredClosure_eq] at *
  exact repeat_trans h1 h2

theorem declaredClosure_ends {p : Srt × Srt} (h : p ∈ c.declaredClosure) :
    (∃ d, (p.1, d) ∈ c.userSubsorts ++ c.lib.subsorts) ∧ (∃ a, (a, p.2) ∈ c.userSubsorts ++ c.lib.subsorts) := by
  rw [declaredClosure_eq] at h
  exact mem_repeat_ends _ h

/-! ## Subsorts: transitive and irreflexive under `wf` -/

theorem wf_parts {d : KCore.Definition} (h : KCore.wf d = true) :
    d.sem.hooksApart = true ∧ d.sem.predsApart = true ∧ d.sem.idsOK = true ∧ d.sem.okAll = true := by
  unfold KCore.wf KCore.Definition.namesOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩

theorem subsortsOK_parts {c : KCore.Semantics} (h : c.subsortsOK = true) :
    (∀ a b, (a, b) ∈ c.userSubsorts → (a ∈ c.userSorts ∨ a ∈ c.libValueSorts) ∧
      (b ∈ c.userSorts ∨ b ∈ c.libConsSorts)) ∧
      ∀ a, (a, a) ∉ c.declaredClosure := by
  unfold KCore.Semantics.subsortsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun a b hab => ?_, fun a ha => ?_⟩
  · have := h.1.1 (a, b) hab
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true] at this
    exact ⟨this.1.2, this.2⟩
  · have := h.1.2 (a, a) ha
    simp at this

theorem lib_subsorts_mem (h : c.lib.ok = true) :
    ∀ p ∈ c.lib.subsorts, p.1 ∈ c.lib.sortsBelowKItem ∧ p.2 ∈ c.lib.sortsBelowKItem := by
  intro p hp
  have := List.all_eq_true.mp (lib_ok_parts h).2.2.1 p hp
  rw [Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
  exact this

theorem libValueSorts_sub {s : Srt} (h : s ∈ c.libValueSorts) : s ∈ c.lib.sortsBelowKItem := h

theorem libConsSorts_sub {s : Srt} (h : s ∈ c.libConsSorts) : s ∈ c.lib.sortsBelowKItem :=
  (List.mem_filter.mp (List.mem_filter.mp h).1).1

/-- The sorts of the declared pairs: the user's and the library's. -/
theorem closure_sorts (hl : c.lib.ok = true) (hso : c.subsortsOK = true) {p : Srt × Srt} (h : p ∈ c.declaredClosure) :
    (p.1 ∈ c.userSorts ∨ p.1 ∈ c.lib.sortsBelowKItem) ∧ (p.2 ∈ c.userSorts ∨ p.2 ∈ c.lib.sortsBelowKItem) := by
  have hu := (subsortsOK_parts hso).1
  obtain ⟨⟨d, hd⟩, ⟨a, ha⟩⟩ := declaredClosure_ends h
  refine ⟨?_, ?_⟩
  · rcases List.mem_append.mp hd with hd | hd
    · rcases (hu _ _ hd).1 with h | h
      · exact Or.inl h
      · exact Or.inr (libValueSorts_sub h)
    · exact Or.inr (lib_subsorts_mem hl _ hd).1
  · rcases List.mem_append.mp ha with ha | ha
    · rcases (hu _ _ ha).2 with h | h
      · exact Or.inl h
      · exact Or.inr (libConsSorts_sub h)
    · exact Or.inr (lib_subsorts_mem hl _ ha).2

theorem mem_subsorts {a b : Srt} :
    (a, b) ∈ c.subsorts ↔ (a, b) ∈ c.declaredClosure ∨ (b = Srt.kitem ∧ a ∈ c.sortsBelowKItem) := by
  unfold KCore.Semantics.subsorts
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨x, hx, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hx⟩
  · rintro (h | ⟨rfl, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, hx, rfl, rfl⟩

/-- The definition's and the library's sorts are below KItem, and none is `KItem`. -/
theorem ul_facts (hids : c.idsOK = true) {s : Srt}
    (hs : s ∈ c.userSorts ∨ s ∈ c.lib.sortsBelowKItem) : s ∈ c.sortsBelowKItem ∧ s ≠ Srt.kitem := by
  obtain ⟨-, hk⟩ := sorts_facts hids
  have hsb : s ∈ c.sortsBelowKItem := mem_sortsBelowKItem.mpr (by
    rcases hs with hs | hs
    · exact Or.inr hs
    · exact Or.inl hs)
  exact ⟨hsb, fun he => hk (he ▸ hsb)⟩

theorem okM_subsortsOK {c : KCore.Semantics} (hok : c.okM = true) : c.subsortsOK = true := by
  unfold KCore.Semantics.okM at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1.1.2

theorem ok_subsortsOK {c : KCore.Semantics} (hok : c.ok = true) : c.subsortsOK = true :=
  okM_subsortsOK (KCore.Semantics.okM_of_ok hok)

theorem sortedOK_subsortsOK {c : KCore.Semantics} (hok : c.sortedOK = true) : c.subsortsOK = true := by
  have hok := KCore.Semantics.sortedOK_sorted hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1

/-- The subsorts are transitive in a core whose sorts are numbered in order (`idsOK`) and that
`sortedOK` accepts. -/
theorem subsorts_trans_of (hids : c.idsOK = true) (hok : c.sortedOK = true) :
    ∀ a b e, (a, b) ∈ c.subsorts → (b, e) ∈ c.subsorts → (a, e) ∈ c.subsorts := by
  have hso := sortedOK_subsortsOK hok
  obtain ⟨-, hk⟩ := sorts_facts hids
  intro a b e hab hbe
  rw [mem_subsorts] at hab hbe ⊢
  rcases hab with hab | ⟨rfl, ha⟩
  · have hs := closure_sorts (lib_ok hids) hso hab
    rcases hbe with hbe | ⟨rfl, -⟩
    · exact Or.inl (declaredClosure_trans hab hbe)
    · exact Or.inr ⟨rfl, (ul_facts hids hs.1).1⟩
  · rcases hbe with hbe | ⟨-, hb⟩
    · exact absurd rfl (ul_facts hids (closure_sorts (lib_ok hids) hso hbe).1).2
    · exact absurd hb hk

/-- The subsorts are irreflexive in a core whose sorts are numbered in order (`idsOK`) and that
`sortedOK` accepts. -/
theorem subsorts_irrefl_of (hids : c.idsOK = true) (hok : c.sortedOK = true) :
    ∀ a, (a, a) ∉ c.subsorts := by
  have hso := sortedOK_subsortsOK hok
  obtain ⟨-, hk⟩ := sorts_facts hids
  intro a h
  rw [mem_subsorts] at h
  rcases h with h | ⟨rfl, ha⟩
  · exact (subsortsOK_parts hso).2 a h
  · exact hk ha

theorem subsorts_trans_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) :
    ∀ a b e, (a, b) ∈ d.sem.subsorts → (b, e) ∈ d.sem.subsorts → (a, e) ∈ d.sem.subsorts :=
  subsorts_trans_of (wf_parts hwf).2.2.1 (KCore.Semantics.sortedOK_of_okAll (wf_parts hwf).2.2.2 (KCore.ovlPatsOK_of_wf hwf))

theorem subsorts_irrefl_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) :
    ∀ a, (a, a) ∉ d.sem.subsorts :=
  subsorts_irrefl_of (wf_parts hwf).2.2.1 (KCore.Semantics.sortedOK_of_okAll (wf_parts hwf).2.2.2 (KCore.ovlPatsOK_of_wf hwf))

/-! ## No constructor is a map pattern symbol -/

theorem lib_ctors_names (h : c.lib.ok = true) : ∀ f ∈ patternHooks, ∀ k ∈ c.lib.ctors, k.name ≠ f := by
  intro f hf k hk he
  have := List.all_eq_true.mp (lib_ok_parts h).2.2.2 k hk
  rw [he, Bool.not_eq_true'] at this
  have h2 : patternHooks.contains f = true := List.contains_iff_mem.mpr hf
  rw [h2] at this; exact Bool.noConfusion this

/-- No constructor is a map pattern symbol in a core whose user symbols are not named like hooks
(`hooksApart`) and whose sorts and symbols are numbered in order (`idsOK`). -/
theorem patHooks_of (hha : c.hooksApart = true) (hids : c.idsOK = true) :
    ∀ f ∈ patternHooks, c.isCtor f = false := by
  intro f hf
  have hfix : ∀ k ∈ fixedCtors, k.name ≠ f := by
    have : ∀ f ∈ patternHooks, ∀ k ∈ fixedCtors, k.name ≠ f := by decide
    exact this f hf
  have huser : ∀ k ∈ c.ctors, k.name ≠ f := by
    intro k hk he
    unfold KCore.Semantics.hooksApart at hha
    simp only [Bool.and_eq_true, List.all_eq_true] at hha
    have := hha.1 k hk
    have hin : hookSigs.any (·.name == k.name) = true := by
      have : ∀ f ∈ patternHooks, hookSigs.any (·.name == f) = true := by decide
      rw [he]; exact this f hf
    rw [hin] at this; exact absurd this (by decide)
  unfold KCore.Semantics.isCtor
  rw [lookupSig_eq]
  unfold KCore.Semantics.ctorSigs
  rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, List.find?_eq_none]
  intro k hk hb
  simp only [beq_iff_eq] at hb
  simp only [List.mem_append] at hk
  rcases hk with (hk | hk) | hk
  · exact hfix k hk hb
  · exact lib_ctors_names (lib_ok hids) f hf k hk hb
  · exact huser k hk hb

theorem patHooks_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) :
    ∀ f ∈ patternHooks, d.sem.isCtor f = false :=
  patHooks_of (wf_parts hwf).1 (wf_parts hwf).2.2.1

/-! ## The two conditions -/

/-- `genWf`, one of `faithCoreOK`'s conjuncts. -/
theorem rangeKeys_genWf_of_faithCore (h : c.faithCoreOK = true) : KCore.Faithful.genWf c = true := by
  simp only [KCore.Semantics.faithCoreOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.2

/-- `srReady` holds of a core whose evaluated functions are named apart (`predsApart`), whose
sorts and symbols are numbered in order (`idsOK`), that `sortedOK` accepts, and whose constructor
sorts and overloading symbols are well formed (`genWf`, `overloadsOK`: every Range value is a
KItem, `rangeKeysOK_of_genWf`). -/
theorem srReady_of (hp : c.predsApart = true) (hids : c.idsOK = true) (hok : c.sortedOK = true)
    (hg : KCore.Faithful.genWf c = true) (hov : c.overloadsOK = true) :
    c.srReady = true := by
  have htr := subsorts_trans_of hids hok
  unfold KCore.Semantics.srReady
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hp, ?_⟩, KCore.rangeKeysOK_of_genWf hg hov⟩
  simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem]
  rintro ⟨a, b⟩ hab ⟨b', e⟩ hbe
  by_cases h : b = b'
  · subst h; exact Or.inr (htr a b e hab hbe)
  · exact Or.inl h

/-- `matchReady` holds of a core whose user symbols are not named like hooks (`hooksApart`),
whose sorts and symbols are numbered in order (`idsOK`) and that `sortedOK` accepts. -/
theorem matchReady_of (hha : c.hooksApart = true) (hids : c.idsOK = true) (hok : c.sortedOK = true)
    (hno : c.ovls = []) : c.matchReady = true := by
  have htr := subsorts_trans_of hids hok
  have hir := subsorts_irrefl_of hids hok
  have hph := patHooks_of hha hids
  unfold KCore.Semantics.matchReady
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, fun f hf => hph f hf⟩, by simp [hno]⟩
  · rintro ⟨a, b⟩ hab ⟨b', e⟩ hbe
    by_cases h : b = b'
    · subst h; exact Or.inr (htr a b e hab hbe)
    · exact Or.inl h
  · rintro ⟨a, b⟩ hab hEq
    simp only at hEq
    subst hEq; exact hir _ hab

/-- A well-formed definition's overloading symbols are as subject reduction reads them. -/
theorem ovlCase_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) : d.sem.OvlCase := by
  refine .inr ⟨?_, subsorts_irrefl_of_wf hwf⟩
  unfold KCore.wf at hwf
  simp only [Bool.and_eq_true] at hwf
  exact hwf.2

theorem srReady_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) : d.sem.srReady = true :=
  srReady_of (wf_parts hwf).2.1 (wf_parts hwf).2.2.1 (KCore.Semantics.sortedOK_of_okAll (wf_parts hwf).2.2.2 (KCore.ovlPatsOK_of_wf hwf))
    (rangeKeys_genWf_of_faithCore (KCore.Semantics.faithCoreOK_of_faithOK (KCore.faithOK_of_wf hwf)))
    (by unfold KCore.wf at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.2)

/-- `matchReady` of a well-formed definition without overloading symbols (the executable matcher
reads none). -/
theorem matchReady_of_wf {d : KCore.Definition} (hwf : KCore.wf d = true) (hno : d.sem.ovls = []) :
    d.sem.matchReady = true :=
  matchReady_of (wf_parts hwf).1 (wf_parts hwf).2.2.1 (KCore.Semantics.sortedOK_of_okAll (wf_parts hwf).2.2.2 (KCore.ovlPatsOK_of_wf hwf)) hno

end KCore.NamesApart
