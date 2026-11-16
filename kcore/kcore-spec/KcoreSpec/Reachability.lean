/-
  Reachability claims over a relation, and the proof principles a symbolic execution uses.

  A complete path is a finite path that ends where the relation has no successor. `AllPath r P Q`:
  every complete path from a state of P passes through a state of Q (partial correctness: a path
  that never ends is not constrained). Nothing here reads what the states are.
-/
set_option autoImplicit false

namespace KCore.Reachability

variable {α : Type} {r : α → α → Prop}

/-- `x` has a successor. -/
def Progress (r : α → α → Prop) (x : α) : Prop := ∃ y, r x y

/-- `CPath r x l`: `l` is a complete path from `x`: it starts at `x`, follows `r`, and ends at a
state without a successor. -/
inductive CPath (r : α → α → Prop) : α → List α → Prop where
  | stuck {x : α} (h : ¬ Progress r x) : CPath r x [x]
  | cons {x y : α} {l : List α} (h : r x y) (hl : CPath r y l) : CPath r x (x :: l)

/-- Every complete path from a state of `P` passes through a state of `Q`. -/
def AllPath (r : α → α → Prop) (P Q : α → Prop) : Prop :=
  ∀ x, P x → ∀ l, CPath r x l → ∃ z ∈ l, Q z

theorem CPath.head_mem {x : α} {l : List α} (h : CPath r x l) : x ∈ l := by
  cases h <;> exact List.mem_cons_self ..

theorem CPath.length_pos {x : α} {l : List α} (h : CPath r x l) : 0 < l.length := by
  cases h <;> simp

/-- From a state on a complete path, the rest of the path is a complete path. -/
theorem CPath.suffix {x : α} {l : List α} (h : CPath r x l) :
    ∀ z ∈ l, ∃ l', CPath r z l' ∧ (∀ w ∈ l', w ∈ l) ∧ l'.length ≤ l.length := by
  induction h with
  | @stuck x hs =>
    intro z hz
    simp only [List.mem_singleton] at hz
    subst hz
    exact ⟨[z], .stuck hs, fun _ hw => hw, Nat.le_refl _⟩
  | @cons x y l hxy hl ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨z :: l, .cons hxy hl, fun _ hw => hw, Nat.le_refl _⟩
    · obtain ⟨l', h1, h2, h3⟩ := ih z hz
      exact ⟨l', h1, fun w hw => List.mem_cons_of_mem _ (h2 w hw), Nat.le_trans h3 (by simp)⟩

/-! ## Consequence, case split, transitivity -/

theorem AllPath.mono {P P' Q Q' : α → Prop} (h : AllPath r P Q) (hP : ∀ x, P' x → P x)
    (hQ : ∀ x, Q x → Q' x) : AllPath r P' Q' := fun x hx l hl =>
  let ⟨z, hz, hq⟩ := h x (hP x hx) l hl
  ⟨z, hz, hQ z hq⟩

theorem AllPath.refl {P Q : α → Prop} (h : ∀ x, P x → Q x) : AllPath r P Q :=
  fun x hx _ hl => ⟨x, hl.head_mem, h x hx⟩

theorem AllPath.trans {P Q R : α → Prop} (h1 : AllPath r P Q) (h2 : AllPath r Q R) :
    AllPath r P R := fun x hx l hl => by
  obtain ⟨z, hz, hq⟩ := h1 x hx l hl
  obtain ⟨l', hl', hsub, _⟩ := hl.suffix z hz
  obtain ⟨w, hw, hr⟩ := h2 z hq l' hl'
  exact ⟨w, hsub w hw, hr⟩

theorem AllPath.cases {ι : Type} {P : ι → α → Prop} {Q : α → Prop}
    (h : ∀ i, AllPath r (P i) Q) : AllPath r (fun x => ∃ i, P i x) Q :=
  fun x ⟨i, hx⟩ l hl => h i x hx l hl

/-- One step: every state of `P` has a successor, and every successor is in `P'`. -/
def StepsInto (r : α → α → Prop) (P P' : α → Prop) : Prop :=
  ∀ x, P x → Progress r x ∧ ∀ y, r x y → P' y

theorem AllPath.step {P P' Q : α → Prop} (hs : StepsInto r P P') (h : AllPath r P' Q) :
    AllPath r P Q := fun x hx l hl => by
  cases hl with
  | stuck hst => exact absurd (hs x hx).1 hst
  | cons hxy hl' =>
    obtain ⟨z, hz, hq⟩ := h _ ((hs x hx).2 _ hxy) _ hl'
    exact ⟨z, List.mem_cons_of_mem _ hz, hq⟩

/-! ## Circularity

A set of claims `(P i, Q i)` may be used in each other's proofs, and in their own, once a step
has been taken. `Derives C Q x`: from `x`, all paths reach `Q`, by steps of `r` and by the
claims `C`. -/

inductive Derives {ι : Type} (r : α → α → Prop) (P Q : ι → α → Prop) (G : α → Prop) : α → Prop where
  /-- the goal holds here -/
  | done {x : α} (h : G x) : Derives r P Q G x
  /-- `x` has a successor and the goal is derived from every successor -/
  | step {x : α} (hp : Progress r x) (h : ∀ y, r x y → Derives r P Q G y) : Derives r P Q G x
  /-- `x` is in the left-hand side of claim `i`, and the goal is derived from every state of its
  right-hand side -/
  | claim {x : α} (i : ι) (hx : P i x) (h : ∀ z, Q i z → Derives r P Q G z) : Derives r P Q G x

section
variable {ι : Type} {P Q : ι → α → Prop}

theorem derives_sound {n : Nat}
    (S : ∀ i x l, P i x → CPath r x l → l.length ≤ n → ∃ z ∈ l, Q i z)
    {G : α → Prop} {x : α} (d : Derives r P Q G x) :
    ∀ l, CPath r x l → l.length ≤ n → ∃ z ∈ l, G z := by
  induction d with
  | done h => intro l hl _; exact ⟨_, hl.head_mem, h⟩
  | step hp _ ih =>
    intro l hl hn
    cases hl with
    | stuck hst => exact absurd hp hst
    | cons hxy hl' =>
      obtain ⟨z, hz, hg⟩ := ih _ hxy _ hl' (Nat.le_trans (by simp) hn)
      exact ⟨z, List.mem_cons_of_mem _ hz, hg⟩
  | claim i hx _ ih =>
    intro l hl hn
    obtain ⟨z, hz, hq⟩ := S i _ l hx hl hn
    obtain ⟨l', hl', hsub, hlen⟩ := hl.suffix z hz
    obtain ⟨w, hw, hg⟩ := ih z hq l' hl' (Nat.le_trans hlen hn)
    exact ⟨w, hsub w hw, hg⟩

/-- Circularity: if each claim's right-hand side is derived from its left-hand side, where the
derivation either is already at the goal or begins with a step, then every claim is valid. -/
theorem circularity
    (h : ∀ i x, P i x → Q i x ∨ (Progress r x ∧ ∀ y, r x y → Derives r P Q (Q i) y)) :
    ∀ i, AllPath r (P i) (Q i) := by
  have S : ∀ n i x l, P i x → CPath r x l → l.length ≤ n → ∃ z ∈ l, Q i z := by
    intro n
    induction n with
    | zero => intro i x l _ hl hn; exact absurd hl.length_pos (by omega)
    | succ n ih =>
      intro i x l hx hl hn
      rcases h i x hx with hq | ⟨hp, hd⟩
      · exact ⟨x, hl.head_mem, hq⟩
      · cases hl with
        | stuck hst => exact absurd hp hst
        | cons hxy hl' =>
          obtain ⟨z, hz, hg⟩ := derives_sound (ih) (hd _ hxy) _ hl' (by simpa using hn)
          exact ⟨z, List.mem_cons_of_mem _ hz, hg⟩
  exact fun i x hx l hl => S l.length i x l hx hl (Nat.le_refl _)

/-- A derivation from valid claims is valid. -/
theorem Derives.allPath (hC : ∀ i, AllPath r (P i) (Q i)) {G : α → Prop} {x : α}
    (d : Derives r P Q G x) : ∀ l, CPath r x l → ∃ z ∈ l, G z := fun l hl =>
  derives_sound (n := l.length) (fun i x l hx hl _ => hC i x hx l hl) d l hl (Nat.le_refl _)

/-- The invariant form: a set closed under steps until the goal is reached. -/
theorem allPath_of_invariant {I G : α → Prop}
    (h : ∀ x, I x → G x ∨ (Progress r x ∧ ∀ y, r x y → I y)) : AllPath r I G :=
  circularity (ι := Unit) (P := fun _ => I) (Q := fun _ => G)
    (fun _ x hx => (h x hx).imp id fun ⟨hp, hs⟩ =>
      ⟨hp, fun y hy => .claim () (hs y hy) fun _ hz => .done hz⟩) ()

end

end KCore.Reachability
