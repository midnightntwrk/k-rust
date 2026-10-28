import KClaims.Reach

/-!
# Claims over a relation that is not a function

A generated semantics lists the successors of a configuration, `successors`, with
`successors_iff : c' ∈ successors c ↔ Step c c'`, for every definition: deterministic or not,
ranked or not. Where rules overlap (strictness in two positions, matches of several elements
of a cell collection, overlapping rules), `Step` has several successors, and an all-path claim
holds at `c` when some successor exists and the claim holds at every one of them. A one-path
claim needs one.
-/

namespace KClaims

/-- `succ c` lists exactly the successors of `c` under `R`. -/
class ExecSucc {α : Type} (R : α → α → Prop) where
  succ : α → List α
  iff : ∀ {c c' : α}, c' ∈ succ c ↔ R c c'

variable {α : Type} {R : α → α → Prop} [ExecSucc R] {P : α → Prop} {c : α} {l : List α}

theorem AF.of_succ (hl : ExecSucc.succ R c = l) (hne : l ≠ []) (h : ∀ d ∈ l, AF R P d) :
    AF R P c := by
  apply AF.step
  · obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨d, ExecSucc.iff.1 (hl ▸ List.mem_cons_self)⟩
  · intro e he
    exact h e (hl ▸ ExecSucc.iff.2 he)

theorem AFn.of_succ {n : Nat} (hl : ExecSucc.succ R c = l) (hne : l ≠ [])
    (h : ∀ d ∈ l, AFn R P n d) : AFn R P (n + 1) c := by
  apply AFn.step
  · obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨d, ExecSucc.iff.1 (hl ▸ List.mem_cons_self)⟩
  · intro e he
    exact h e (hl ▸ ExecSucc.iff.2 he)

theorem Reach.of_succ {d : α} (hl : ExecSucc.succ R c = l) (hd : d ∈ l) (k : Reach R P d) :
    Reach R P c :=
  Reach.step (ExecSucc.iff.1 (hl ▸ hd)) k

/-- The per-successor goals of `AF.of_succ`, built one element at a time. -/
theorem allMem_cons {p : α → Prop} {a : α} {l : List α} (ha : p a) (hl : ∀ d ∈ l, p d) :
    ∀ d ∈ a :: l, p d := by
  intro d hd
  cases hd with
  | head => exact ha
  | tail _ h => exact hl d h

theorem allMem_nil {p : α → Prop} : ∀ d ∈ ([] : List α), p d := by
  intro d hd
  cases hd

end KClaims
