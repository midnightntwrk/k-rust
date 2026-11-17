/-
  KCore. The first-occurrence form of a word: each letter at its first occurrence, the later
  occurrences dropped (`Band.nf`). On words read as nested applications of one associative and
  idempotent symbol, `nf` gives one word per class of the laws it is used for here:
  - `nf (nf u ++ v) = nf (u ++ v)` and `nf (u ++ nf v) = nf (u ++ v)` (`nf_left`, `nf_right`):
    forming a part first changes nothing, so the form of a concatenation does not depend on the
    nesting (associativity);
  - `nf (w ++ w) = nf w` (`nf_idem`): a word twice has the form of the word (idempotence), at a
    word of any length, not only at a letter;
  - `nf (nf w) = nf w` (`nf_nf`): a form is its own form;
  - `x ∈ nf w ↔ x ∈ w` (`nf_mem`), `nf [a] = [a]` (`nf_single`), `nf w ≠ []` for `w ≠ []`
    (`nf_ne_nil`).
  - a form is without repetition, and a word without repetition is its own form (`nf_nodup`,
    `nf_of_nodup`).
  It adds no commutativity: `nf [1, 2] ≠ nf [2, 1]`. It is not the free band's normal form either:
  `aba` and `ab` have one form. No KCore declaration is read here.
-/

set_option autoImplicit false

namespace KCore.Band

variable {α : Type} [DecidableEq α]

/-- The letters of the word not in `seen`, each at its first occurrence. -/
def go (seen : List α) : List α → List α
  | [] => []
  | a :: l => if a ∈ seen then go seen l else a :: go (a :: seen) l

/-- **The first-occurrence form** of a word. -/
def nf (l : List α) : List α := go [] l

theorem go_congr {s s' : List α} (h : ∀ x, x ∈ s ↔ x ∈ s') : ∀ l, go s l = go s' l := by
  intro l
  induction l generalizing s s' with
  | nil => rfl
  | cons a l ih =>
    simp only [go]
    by_cases ha : a ∈ s
    · rw [if_pos ha, if_pos ((h a).mp ha)]; exact ih h
    · rw [if_neg ha, if_neg (fun h' => ha ((h a).mpr h'))]
      congr 1
      exact ih (fun x => by simp [h x])

theorem go_append (s u v : List α) : go s (u ++ v) = go s u ++ go (u ++ s) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append, go]
    by_cases ha : a ∈ s
    · rw [if_pos ha, if_pos ha, ih]
      congr 1
      exact go_congr (fun x => by simp; intro hx; subst hx; exact Or.inr ha) v
    · rw [if_neg ha, if_neg ha, ih, List.cons_append]
      congr 2
      exact go_congr (fun x => by simp; constructor <;> (intro h; rcases h with h | h | h <;> simp [h])) v

theorem go_mem {s l : List α} {x : α} : x ∈ go s l ↔ x ∈ l ∧ x ∉ s := by
  induction l generalizing s with
  | nil => simp [go]
  | cons a l ih =>
    by_cases ha : a ∈ s
    · simp only [go, ha, if_true, ih, List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1, h.2⟩
      · rintro ⟨h | h, hn⟩
        · subst h; exact absurd ha hn
        · exact ⟨h, hn⟩
    · simp only [go, ha, if_false, List.mem_cons, ih, not_or]
      constructor
      · rintro (h | ⟨h, -, hn⟩)
        · subst h; exact ⟨Or.inl rfl, ha⟩
        · exact ⟨Or.inr h, hn⟩
      · rintro ⟨h | h, hn⟩
        · exact Or.inl h
        · by_cases hx : x = a
          · exact Or.inl hx
          · exact Or.inr ⟨h, hx, hn⟩

theorem go_seen {s l : List α} (h : ∀ x ∈ l, x ∈ s) : go s l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [go]
    rw [if_pos (h a (List.mem_cons_self ..))]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem go_go {s t : List α} (h : ∀ x ∈ t, x ∈ s) (v : List α) : go s (go t v) = go s v := by
  induction v generalizing s t with
  | nil => rfl
  | cons a v ih =>
    by_cases hat : a ∈ t
    · have has := h a hat
      simp only [go, hat, has, if_true]; exact ih h
    · by_cases has : a ∈ s
      · simp only [go, hat, has, if_true, if_false]
        exact ih (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact has
          · exact h x hx)
      · simp only [go, hat, has, if_false]
        congr 1
        exact ih (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (h x hx))

/-- The form of a form is itself. -/
theorem nf_nf (w : List α) : nf (nf w) = nf w := go_go (fun _ h => h) w

/-- Associativity, left: forming a part first changes nothing. -/
theorem nf_left (u v : List α) : nf (nf u ++ v) = nf (u ++ v) := by
  unfold nf
  rw [go_append, go_append, go_go (fun _ h => h)]
  congr 1
  exact go_congr (fun x => by simp [go_mem]) v

/-- Associativity, right. -/
theorem nf_right (u v : List α) : nf (u ++ nf v) = nf (u ++ v) := by
  unfold nf
  rw [go_append, go_append]
  congr 1
  exact go_go (fun _ h => by cases h) v

/-- Idempotence: a word twice has the form of the word. -/
theorem nf_idem (w : List α) : nf (w ++ w) = nf w := by
  unfold nf
  rw [go_append, go_seen (s := w ++ []) (l := w) (fun x hx => by simpa using hx), List.append_nil]

/-- A form holds what the word holds. -/
theorem nf_mem {w : List α} {x : α} : x ∈ nf w ↔ x ∈ w := by simp [nf, go_mem]

/-- A word of one letter is its own form. -/
theorem nf_single (a : α) : nf [a] = [a] := by simp [nf, go]

/-- A word with a letter has a form with one. -/
theorem nf_ne_nil {w : List α} (h : w ≠ []) : nf w ≠ [] := by
  cases w with
  | nil => exact absurd rfl h
  | cons a l => simp [nf, go]

/-- The letters kept are without repetition. -/
theorem go_nodup (s : List α) : ∀ l : List α, (go s l).Nodup := by
  intro l
  induction l generalizing s with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    by_cases ha : a ∈ s
    · simp only [go, ha, ↓reduceIte]; exact ih s
    · simp only [go, ha, ↓reduceIte]
      exact List.nodup_cons.mpr ⟨fun h => (go_mem.mp h).2 (List.mem_cons_self ..), ih (a :: s)⟩

/-- A word without repetition and with no letter of `seen` is kept whole. -/
theorem go_of_nodup {s : List α} : ∀ {l : List α}, l.Nodup → (∀ x ∈ l, x ∉ s) → go s l = l := by
  intro l
  induction l generalizing s with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hn hs
    obtain ⟨hal, hn'⟩ := List.nodup_cons.mp hn
    simp only [go, hs a (List.mem_cons_self ..), ↓reduceIte]
    congr 1
    exact ih hn' fun x hx hxs => by
      rcases List.mem_cons.mp hxs with rfl | h
      · exact hal hx
      · exact hs x (List.mem_cons_of_mem _ hx) h

/-- A form is without repetition. -/
theorem nf_nodup (w : List α) : (nf w).Nodup := go_nodup [] w

/-- A word without repetition is its own form. -/
theorem nf_of_nodup {w : List α} (h : w.Nodup) : nf w = w := go_of_nodup h (fun _ _ h' => by cases h')

/-! ## Instances -/

/-- No commutativity: `ab` and `ba` are two forms. -/
example : nf [1, 2] ≠ nf [2, 1] := by decide

/-- Not the free band: `aba` has the form `ab`. -/
example : nf [1, 2, 1] = nf [1, 2] := by decide

/-- The case that defeats merging equal neighbours: `x y x y` has the form `x y`. -/
example : nf ([1, 2] ++ [1, 2]) = nf [1, 2] := nf_idem [1, 2]

example : nf (nf [1, 2, 1] ++ [3, 2]) = nf ([1, 2, 1] ++ [3, 2]) := nf_left [1, 2, 1] [3, 2]
example : nf ([3, 2] ++ nf [1, 2, 1]) = nf ([3, 2] ++ [1, 2, 1]) := nf_right [3, 2] [1, 2, 1]
example : nf (nf [2, 1, 2]) = nf [2, 1, 2] := nf_nf [2, 1, 2]
example : (3 : Nat) ∈ nf [1, 3, 1] := nf_mem.mpr (by decide)
example : nf [7] = [7] := nf_single 7
example : nf [1, 1] ≠ [] := nf_ne_nil (by decide)

end KCore.Band
