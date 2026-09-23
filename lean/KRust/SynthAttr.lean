/-
The generic synthesized-attribute lemma (`draft/lean-verification/README.md`, "Case study 3"): an
attribute computed by an algebra over the children and a walk that is a fold over the same children
agree when each algebra step preserves the agreement relation. Case 3 is restated through it
(`hasMacroF_iff`, `kCellsF_eq`); the direct mutual models in `KRust.TermAttributes` remain the
reviewed mirrors of the Rust, and this form is meant for further flags of the same class.
`fold` is well-founded, so the models defined through it run compiled but not in the kernel.
Anchors verified at ce4084a5. The model's `Term` and its equality are those of
`KRust.TermAttributes` (Rust `Eq for Term`).
-/
import KRust.TermAttributes

set_option linter.unusedSimpArgs false

namespace KRust.SynthAttr
open KRust.TermAttributes

/-- The immediate children in the order every walk here visits them: `visit_symbols`
(term.rs:760-805), `find_k_cells` (rule.rs:789-840), the recursive part of `ceil_term_recursive`
(definedness.rs:99-189). Map entries contribute key then value, then the rest; lists heads, then
middle, then tails. -/
def children : Term → List Term
  | .and l r        => [l, r]
  | .app _ _ args   => args
  | .dv _ _         => []
  | .var _ _ _      => []
  | .inj _ _ t      => [t]
  | .map _ es rest  => es.flatMap (fun e => [e.1, e.2]) ++ rest.toList
  | .list _ hs rest => hs ++ (match rest with | none => [] | some (m, ts) => m :: ts)
  | .set _ es rest  => es ++ rest.toList

theorem sizeOf_lt_of_mem_children {u t : Term} (h : u ∈ children t) : sizeOf u < sizeOf t := by
  cases t with
  | and l r => simp [children] at h; rcases h with rfl | rfl <;> simp <;> omega
  | app s ss args =>
      simp only [children] at h; have := List.sizeOf_lt_of_mem h; simp; omega
  | dv _ _ | var _ _ _ => simp [children] at h
  | inj _ _ t => simp [children] at h; subst h; simp; omega
  | map d es rest =>
      simp only [children, List.mem_append, List.mem_flatMap] at h
      rcases h with ⟨e, he, hu⟩ | h
      · have h1 := List.sizeOf_lt_of_mem he
        rcases e with ⟨k, v⟩
        simp at hu h1; rcases hu with rfl | rfl <;> simp <;> omega
      · rcases rest with _ | r <;> simp at h; subst h; simp; omega
  | list d hs rest =>
      simp only [children, List.mem_append] at h
      rcases h with h | h
      · have := List.sizeOf_lt_of_mem h; simp; omega
      · rcases rest with _ | ⟨m, ts⟩ <;> simp at h
        rcases h with rfl | h
        · simp; omega
        · have := List.sizeOf_lt_of_mem h; simp; omega
  | set d es rest =>
      simp only [children, List.mem_append] at h
      rcases h with h | h
      · have := List.sizeOf_lt_of_mem h; simp; omega
      · rcases rest with _ | r <;> simp at h; subst h; simp; omega

/-- The fold of an algebra `f` (the node, and the children's results in visit order). -/
def fold {β} (f : Term → List β → β) (t : Term) : β :=
  f t ((children t).attach.map fun ⟨u, _⟩ => fold f u)
termination_by sizeOf t
decreasing_by exact sizeOf_lt_of_mem_children ‹_›

/-- The generic lemma. If every algebra step preserves `R` from the children to the node, then the
two folds are related by `R` everywhere. `xs` pairs each child with both results. -/
theorem fold_rel {α β} (R : Term → α → β → Prop) (f : Term → List α → α) (g : Term → List β → β)
    (step : ∀ t (xs : List (Term × α × β)), xs.map (·.1) = children t →
      (∀ x ∈ xs, R x.1 x.2.1 x.2.2) → R t (f t (xs.map (·.2.1))) (g t (xs.map (·.2.2)))) :
    ∀ t, R t (fold f t) (fold g t)
  | t => by
      have h := step t ((children t).attach.map fun ⟨u, _⟩ => (u, fold f u, fold g u))
        (by simp [Function.comp_def]) (by
          intro x hx
          simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hx
          obtain ⟨u, hu, rfl⟩ := hx
          exact fold_rel R f g step u)
      rw [fold, fold]
      simpa [List.map_map, Function.comp_def] using h
termination_by t => sizeOf t
decreasing_by exact sizeOf_lt_of_mem_children ‹_›

/-! ### Instance 1: `has_macro_or_alias` against `macro_or_alias_symbol` -/

/-- What a node contributes by itself: an application's symbol, when it is a macro or alias. -/
def ownMacro : Term → Option String
  | .app s _ _ => if s.macroOrAlias then some s.name else none
  | _          => none

/-- The walk: this node's symbol first (preorder), then the first child that finds one. -/
def firstMacroF : Term → Option String :=
  fold fun t os => (ownMacro t).or (os.foldr Option.or none)

/-- The attribute: this node's flag, or any child's. -/
def hasMacroF : Term → Bool :=
  fold fun t bs => (ownMacro t).isSome || bs.any id

theorem any_iff_foldr (xs : List (Term × Bool × Option String))
    (h : ∀ x ∈ xs, (x.2.1 = false ↔ x.2.2 = none)) :
    (xs.map (·.2.1)).any id = false ↔ (xs.map (·.2.2)).foldr Option.or none = none := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [List.any_cons, Option.or_eq_none_iff, ← ih h.2, ← h.1]

/-- Case 3a through the generic lemma. -/
theorem hasMacroF_iff (t : Term) : hasMacroF t = false ↔ firstMacroF t = none :=
  fold_rel (fun _ b o => b = false ↔ o = none) _ _
    (fun t xs _ h => by
      simp only [Bool.or_eq_false_iff, Option.or_eq_none_iff, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none]
      rw [any_iff_foldr xs h]) t

/-! ### Instance 2: the saturated k-cell count against the unbounded list of k cells -/

def ownKCell (t : Term) : Bool :=
  match t with
  | .app s _ _ => s.isKCell
  | _          => false

def allKF : Term → List Term :=
  fold fun t ls => if ownKCell t then [t] else ls.flatten

def kCellsF : Term → Nat :=
  fold fun t ns => if ownKCell t then 1 else ns.foldr satAdd 0

theorem foldr_satAdd (xs : List (Term × Nat × List Term))
    (h : ∀ x ∈ xs, x.2.1 = min 2 x.2.2.length) :
    (xs.map (·.2.1)).foldr satAdd 0 = min 2 (xs.map (·.2.2)).flatten.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [List.map_cons, List.foldr_cons, List.flatten_cons, ih h.2, h.1, satAdd,
        List.length_append]
      omega

/-- Case 3b's key lemma through the generic lemma. -/
theorem kCellsF_eq (t : Term) : kCellsF t = min 2 (allKF t).length :=
  fold_rel (fun _ (n : Nat) (l : List Term) => n = min 2 l.length)
    (fun t ns => if ownKCell t then 1 else ns.foldr satAdd 0)
    (fun t ls => if ownKCell t then [t] else ls.flatten)
    (fun t xs _ h => by
      split
      · simp
      · exact foldr_satAdd xs h) t

end KRust.SynthAttr
