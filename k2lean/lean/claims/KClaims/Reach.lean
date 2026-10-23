/-!
# Reachability claims over a transition relation

A K claim `φ => ψ` is compiled to the matching-logic formula
`φ → weakAlwaysFinally(∃ ?X. ψ)` (all-path, the default) or
`φ → weakExistsFinally(∃ ?X. ψ)` (one-path, `[one-path]`), where, over the transition
relation `R` that the rewrite rules denote,

* `weakAlwaysFinally(P) = νX. P ∨ (○X ∧ •⊤)`: `P` holds, or there is a successor and every
  successor is again in the set (`○` is "all successors", `•⊤` is "some successor");
* `weakExistsFinally(P) = νX. P ∨ •X`: `P` holds, or some successor is again in the set.

`AF` and `EF` below are these greatest fixpoints, written as the union of all post-fixpoints
(Knaster–Tarski), so the coinduction principle is the definition itself.
"Weak" means partial correctness: an infinite path never refutes either formula.

The file proves the readings of both formulas as path properties
(`AF_iff_not_avoids`: every finite maximal path meets `P`, the all-path semantics of
Ştefănescu et al., RTA 2014; `EF_iff`: a terminating configuration reaches `P`, the one-path
semantics of Roşu et al., LICS 2013), the step-indexed approximation `AFn` of `AF`
(`AF_iff_AFn`), transitivity, and the two circularity principles: a family of claims may assume
all of its members after at least one step (`AF.circularity`, `EF.circularity`).

A configuration whose rule applies but whose right-hand side is `⊥` (for example `X /Int 0`)
has no successor in `R`; for both formulas it counts like a stuck one.
-/

namespace KClaims

section

variable {α : Type} (R : α → α → Prop)

/-- `weakAlwaysFinally(P)`: the greatest fixpoint of `X ↦ P ∨ (○X ∧ •⊤)`. -/
def AF (P : α → Prop) (c : α) : Prop :=
  ∃ X : α → Prop, X c ∧ ∀ d, X d → P d ∨ ((∃ e, R d e) ∧ ∀ e, R d e → X e)

/-- `weakExistsFinally(P)`: the greatest fixpoint of `X ↦ P ∨ •X`. -/
def EF (P : α → Prop) (c : α) : Prop :=
  ∃ X : α → Prop, X c ∧ ∀ d, X d → P d ∨ ∃ e, R d e ∧ X e

/-- A finite maximal path from `c` (its last configuration has no successor) none of whose
configurations satisfies `P`: a counterexample to an all-path claim. -/
inductive Avoids (P : α → Prop) : α → Prop
  | stuck {c : α} : ¬ P c → (∀ e, ¬ R c e) → Avoids P c
  | step {c e : α} : ¬ P c → R c e → Avoids P e → Avoids P c

/-- Some finite path from `c` reaches a configuration satisfying `P`. -/
inductive Reach (P : α → Prop) : α → Prop
  | here {c : α} : P c → Reach P c
  | step {c e : α} : R c e → Reach P e → Reach P c

/-- `c` terminates: no infinite path starts at `c`. -/
def Terminates (c : α) : Prop := Acc (fun a b => R b a) c

/-- One or more steps. -/
inductive Plus : α → α → Prop
  | single {a b : α} : R a b → Plus a b
  | tail {a b c : α} : Plus a b → R b c → Plus a c

/-- The step-indexed approximation of `AF`: every path of at most `n` steps either meets `P`
or can still be extended. -/
def AFn (P : α → Prop) : Nat → α → Prop
  | 0, _ => True
  | n + 1, c => P c ∨ ((∃ e, R c e) ∧ ∀ e, R c e → AFn P n e)

end

variable {α : Type} {R : α → α → Prop} {P Q : α → Prop} {c : α}

/-! ## `AF` -/

theorem AF.coind (X : α → Prop) (hX : ∀ d, X d → P d ∨ ((∃ e, R d e) ∧ ∀ e, R d e → X e))
    (h : X c) : AF R P c := ⟨X, h, hX⟩

theorem AF.unfold : AF R P c ↔ P c ∨ ((∃ e, R c e) ∧ ∀ e, R c e → AF R P e) := by
  constructor
  · rintro ⟨X, hc, hX⟩
    rcases hX c hc with h | ⟨hs, hall⟩
    · exact Or.inl h
    · exact Or.inr ⟨hs, fun e he => ⟨X, hall e he, hX⟩⟩
  · intro h
    refine ⟨fun d => d = c ∨ AF R P d, Or.inl rfl, ?_⟩
    rintro d (rfl | ⟨X, hd, hX⟩)
    · rcases h with h | ⟨hs, hall⟩
      · exact Or.inl h
      · exact Or.inr ⟨hs, fun e he => Or.inr (hall e he)⟩
    · rcases hX d hd with h | ⟨hs, hall⟩
      · exact Or.inl h
      · exact Or.inr ⟨hs, fun e he => Or.inr ⟨X, hall e he, hX⟩⟩

theorem AF.here (h : P c) : AF R P c := AF.unfold.2 (Or.inl h)

theorem AF.step (hs : ∃ e, R c e) (hall : ∀ e, R c e → AF R P e) : AF R P c :=
  AF.unfold.2 (Or.inr ⟨hs, hall⟩)

theorem AF.mono (hPQ : ∀ d, P d → Q d) (h : AF R P c) : AF R Q c := by
  obtain ⟨X, hc, hX⟩ := h
  refine ⟨X, hc, fun d hd => ?_⟩
  rcases hX d hd with h | h
  · exact Or.inl (hPQ d h)
  · exact Or.inr h

/-- Transitivity: a circularity (or a proved claim) `P ⇒ Q` composes with `c ⇒ P`. -/
theorem AF.trans (h : AF R P c) (hPQ : ∀ d, P d → AF R Q d) : AF R Q c := by
  refine AF.coind (fun d => AF R P d ∨ AF R Q d) ?_ (Or.inl h)
  rintro d (hd | hd)
  · rcases AF.unfold.1 hd with hp | ⟨hs, hall⟩
    · rcases AF.unfold.1 (hPQ d hp) with hq | ⟨hs, hall⟩
      · exact Or.inl hq
      · exact Or.inr ⟨hs, fun e he => Or.inr (hall e he)⟩
    · exact Or.inr ⟨hs, fun e he => Or.inl (hall e he)⟩
  · rcases AF.unfold.1 hd with hq | ⟨hs, hall⟩
    · exact Or.inl hq
    · exact Or.inr ⟨hs, fun e he => Or.inr (hall e he)⟩

/-- `AF` is the all-path partial-correctness reading: every finite maximal path from `c` meets
`P` (infinite paths impose nothing). -/
theorem AF_iff_not_avoids : AF R P c ↔ ¬ Avoids R P c := by
  constructor
  · rintro ⟨X, hc, hX⟩ ha
    induction ha with
    | stuck hP hno =>
      rcases hX _ hc with h | ⟨⟨e, he⟩, _⟩
      · exact hP h
      · exact hno e he
    | step hP hr _ ih =>
      rcases hX _ hc with h | ⟨_, hall⟩
      · exact hP h
      · exact ih (hall _ hr)
  · intro h
    refine AF.coind (fun d => ¬ Avoids R P d) ?_ h
    intro d hd
    by_cases hP : P d
    · exact Or.inl hP
    · refine Or.inr ⟨?_, fun e he ha => hd (Avoids.step hP he ha)⟩
      apply Classical.byContradiction
      intro hne
      exact hd (Avoids.stuck hP fun e he => hne ⟨e, he⟩)

/-! ## The step-indexed approximation -/

theorem AFn.zero : AFn R P 0 c := trivial

theorem AFn.here {n : Nat} (h : P c) : AFn R P n c := by
  cases n
  · exact trivial
  · exact Or.inl h

theorem AFn.step {n : Nat} (hs : ∃ e, R c e) (hall : ∀ e, R c e → AFn R P n e) :
    AFn R P (n + 1) c := Or.inr ⟨hs, hall⟩

theorem AFn.mono {n : Nat} (hPQ : ∀ d, P d → Q d) : AFn R P n c → AFn R Q n c := by
  induction n generalizing c with
  | zero => intro _; exact trivial
  | succ n ih =>
    rintro (h | ⟨hs, hall⟩)
    · exact Or.inl (hPQ c h)
    · exact Or.inr ⟨hs, fun e he => ih (hall e he)⟩

theorem AFn.le {m n : Nat} (hmn : m ≤ n) : AFn R P n c → AFn R P m c := by
  induction n generalizing m c with
  | zero => intro _; cases Nat.le_zero.1 hmn; exact trivial
  | succ n ih =>
    intro h
    cases m with
    | zero => exact trivial
    | succ m =>
      rcases h with h | ⟨hs, hall⟩
      · exact Or.inl h
      · exact Or.inr ⟨hs, fun e he => ih (Nat.le_of_succ_le_succ hmn) (hall e he)⟩

theorem AFn.trans {n : Nat} (h : AFn R P n c) (hPQ : ∀ d, P d → AFn R Q n d) : AFn R Q n c := by
  induction n generalizing c with
  | zero => exact trivial
  | succ n ih =>
    rcases h with hp | ⟨hs, hall⟩
    · exact hPQ c hp
    · exact Or.inr ⟨hs, fun e he => ih (hall e he) fun d hd => AFn.le (Nat.le_succ n) (hPQ d hd)⟩

theorem AF.toAFn (h : AF R P c) : ∀ n, AFn R P n c := by
  intro n
  induction n generalizing c with
  | zero => exact trivial
  | succ n ih =>
    rcases AF.unfold.1 h with hp | ⟨hs, hall⟩
    · exact Or.inl hp
    · exact Or.inr ⟨hs, fun e he => ih (hall e he)⟩

/-- `AF` is the intersection of its approximations (the functional preserves intersections of
decreasing chains, whatever the branching of `R`). -/
theorem AF_iff_AFn : AF R P c ↔ ∀ n, AFn R P n c := by
  refine ⟨AF.toAFn, fun h => AF.coind (fun d => ∀ n, AFn R P n d) ?_ h⟩
  intro d hd
  by_cases hP : P d
  · exact Or.inl hP
  · have h1 := hd 1
    rcases h1 with h1 | ⟨hs, _⟩
    · exact absurd h1 hP
    refine Or.inr ⟨hs, fun e he n => ?_⟩
    rcases hd (n + 1) with h | ⟨_, hall⟩
    · exact absurd h hP
    · exact hall e he

/-- **Guarded circularities, all-path.** `Pre i` and `Post i` describe a family of claims
(the index carries the claim and the valuation of its universally quantified variables).
If each claim holds at index `n` assuming every claim at every index `m < n`, every claim holds.
Only `AFn.step` lowers the index, so an assumed claim can be used only after at least one
step: this is K's rule that a circularity applies after one step, and it is sound for partial
correctness by induction on the index (`AF_iff_AFn`). -/
theorem AF.circularity {ι : Type} (Pre Post : ι → α → Prop)
    (h : ∀ n, (∀ m < n, ∀ i d, Pre i d → AFn R (Post i) m d) → ∀ i d, Pre i d → AFn R (Post i) n d) :
    ∀ i d, Pre i d → AF R (Post i) d := by
  have key : ∀ n, ∀ i d, Pre i d → AFn R (Post i) n d := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih => exact h n ih
  intro i d hd
  exact AF_iff_AFn.2 fun n => key n i d hd

/-! ## `EF` -/

theorem EF.coind (X : α → Prop) (hX : ∀ d, X d → P d ∨ ∃ e, R d e ∧ X e) (h : X c) : EF R P c :=
  ⟨X, h, hX⟩

theorem EF.unfold : EF R P c ↔ P c ∨ ∃ e, R c e ∧ EF R P e := by
  constructor
  · rintro ⟨X, hc, hX⟩
    rcases hX c hc with h | ⟨e, he, hXe⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he, X, hXe, hX⟩
  · intro h
    refine ⟨fun d => d = c ∨ EF R P d, Or.inl rfl, ?_⟩
    rintro d (rfl | ⟨X, hd, hX⟩)
    · rcases h with h | ⟨e, he, hef⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, he, Or.inr hef⟩
    · rcases hX d hd with h | ⟨e, he, hXe⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, he, Or.inr ⟨X, hXe, hX⟩⟩

theorem EF.here (h : P c) : EF R P c := EF.unfold.2 (Or.inl h)

theorem EF.step {e : α} (he : R c e) (h : EF R P e) : EF R P c := EF.unfold.2 (Or.inr ⟨e, he, h⟩)

theorem not_terminates_step (h : ¬ Terminates R c) : ∃ e, R c e ∧ ¬ Terminates R e := by
  apply Classical.byContradiction
  intro hne
  exact h (Acc.intro c fun e he => Classical.byContradiction fun ht => hne ⟨e, he, ht⟩)

theorem EF_of_not_terminates (h : ¬ Terminates R c) : EF R P c := by
  refine EF.coind (fun d => ¬ Terminates R d) (fun d hd => ?_) h
  obtain ⟨e, he, hne⟩ := not_terminates_step hd
  exact Or.inr ⟨e, he, hne⟩

/-- `EF` is the one-path partial-correctness reading: if `c` terminates, some path from `c`
reaches `P`. -/
theorem EF_iff : EF R P c ↔ (Terminates R c → Reach R P c) := by
  constructor
  · rintro ⟨X, hc, hX⟩ ht
    induction ht with
    | intro c _ ih =>
      rcases hX c hc with h | ⟨e, he, hXe⟩
      · exact Reach.here h
      · exact Reach.step he (ih e he hXe)
  · intro h
    refine EF.coind (fun d => Terminates R d → Reach R P d) ?_ h
    intro d hd
    by_cases ht : Terminates R d
    · cases hd ht with
      | here hp => exact Or.inl hp
      | step he hr => exact Or.inr ⟨_, he, fun _ => hr⟩
    · obtain ⟨e, he, hne⟩ := not_terminates_step ht
      exact Or.inr ⟨e, he, fun ht' => absurd ht' hne⟩

theorem Plus.head {a d : α} (h : Plus R a d) : ∃ e, R a e ∧ (d = e ∨ Plus R e d) := by
  induction h with
  | single hab => exact ⟨_, hab, Or.inl rfl⟩
  | tail _ hbc ih =>
    obtain ⟨e, hae, hbe⟩ := ih
    rcases hbe with rfl | hp
    · exact ⟨_, hae, Or.inr (Plus.single hbc)⟩
    · exact ⟨_, hae, Or.inr (Plus.tail hp hbc)⟩

/-- **Guarded circularities, one-path.** If each claim holds at `c` assuming every claim at
every configuration reachable from `c` in one or more steps, every claim holds.
Sound for partial correctness: on a terminating configuration by well-founded induction, and a
non-terminating configuration satisfies every `EF` (`EF_of_not_terminates`). -/
theorem EF.circularity {ι : Type} (Pre Post : ι → α → Prop)
    (h : ∀ c, (∀ d, Plus R c d → ∀ j, Pre j d → EF R (Post j) d) → ∀ i, Pre i c → EF R (Post i) c) :
    ∀ i c, Pre i c → EF R (Post i) c := by
  intro i c hc
  by_cases ht : Terminates R c
  · suffices key : ∀ d, (d = c ∨ Plus R c d) → ∀ j, Pre j d → EF R (Post j) d from
      key c (Or.inl rfl) i hc
    clear hc
    induction ht with
    | intro c _ ih =>
      have below : ∀ d, Plus R c d → ∀ j, Pre j d → EF R (Post j) d := by
        intro d hd
        obtain ⟨e, he, hed⟩ := hd.head
        exact ih e he d hed
      rintro d (rfl | hd)
      · exact h d below
      · exact below d hd
  · exact EF_of_not_terminates ht

/-- All-path implies one-path (a configuration that is not in `P` has a successor). -/
theorem AF.toEF (h : AF R P c) : EF R P c := by
  refine EF.coind (AF R P) (fun d hd => ?_) h
  rcases AF.unfold.1 hd with hp | ⟨⟨e, he⟩, hall⟩
  · exact Or.inl hp
  · exact Or.inr ⟨e, he, hall e he⟩

/-- For a deterministic relation the two modalities coincide. -/
theorem AF_iff_EF_of_det (hdet : ∀ a b b', R a b → R a b' → b = b') : AF R P c ↔ EF R P c := by
  constructor
  · intro h
    refine EF.coind (AF R P) (fun d hd => ?_) h
    rcases AF.unfold.1 hd with hp | ⟨⟨e, he⟩, hall⟩
    · exact Or.inl hp
    · exact Or.inr ⟨e, he, hall e he⟩
  · intro h
    refine AF.coind (EF R P) (fun d hd => ?_) h
    rcases EF.unfold.1 hd with hp | ⟨e, he, hef⟩
    · exact Or.inl hp
    · exact Or.inr ⟨⟨e, he⟩, fun e' he' => hdet d e e' he he' ▸ hef⟩

end KClaims
