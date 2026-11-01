import KPrelude.Scaffold

/-!
# Defined right-hand sides at a cell map (`gen --progress`, SND-20)

A rule over a cell map matches one or two bindings, `K |-> E REST` (or `K₁ |-> E₁ K₂ |-> E₂ D`),
and its right-hand side writes new values at the same keys over the same rest. The map it builds
is defined: the keys are the matched ones, which the match shows apart from each other and from
the rest, and only the values change. These lemmas give that value (`k2l_map_defined`, the
generated `def_close`'s map step). A right-hand side that binds a new key (a spawn) needs that
key unbound, which a match does not show; an invariant of the definition must.
-/

namespace KPrelude
namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- One matched binding, rewritten at its key over the same rest. -/
theorem concat_element_rebuild {k : K} {v v' : V} {r m : M}
    (h : concat (element k v) r = some m) : ∃ m', concat (element k v') r = some m' := by
  obtain ⟨hw, hn, -⟩ := concat_element_iff.1 h
  exact ⟨_, concat_element_iff.2 ⟨hw, hn, rfl⟩⟩

/-- Two matched bindings (`K₁ |-> E₁ REST` with `REST` matched as `K₂ |-> E₂ D`): the two written
bindings form a map, since the keys differ. -/
theorem concat_element2_rebuild_a {k₁ k₂ : K} {v₁ v₂ w₁ w₂ : V} {r d m : M}
    (h₁ : concat (element k₁ v₁) r = some m) (h₂ : concat (element k₂ v₂) d = some r) :
    ∃ x, concat (element k₁ w₁) (element k₂ w₂ : M) = some x := by
  have n₁ := (concat_element_iff.1 h₁).2.1
  have l₂ := lookup_of_concat_element h₂
  have hne : k₁ ≠ k₂ := fun e => by subst e; rw [l₂] at n₁; cases n₁
  exact ⟨_, concat_element_iff.2 ⟨wf_element, lookup_element_ne hne, rfl⟩⟩

/-- … and that map over the rest `D` is defined. -/
theorem concat_element2_rebuild_b {k₁ k₂ : K} {v₁ v₂ w₁ w₂ : V} {r d m x : M}
    (hx : concat (element k₁ w₁) (element k₂ w₂ : M) = some x)
    (h₂ : concat (element k₂ v₂) d = some r) (h₁ : concat (element k₁ v₁) r = some m) :
    ∃ m', concat x d = some m' := by
  obtain ⟨wr, n₁, rfl⟩ := concat_element_iff.1 h₁
  obtain ⟨wd, n₂, rfl⟩ := concat_element_iff.1 h₂
  have hne : k₁ ≠ k₂ := fun e => by subst e; rw [lookup_update_self] at n₁; cases n₁
  -- `K₂ |-> W₂ D`, then `K₁ |-> W₁` over it, then reassociated
  have e₂ : concat (element k₂ w₂) d = some (update d k₂ w₂) := concat_element_iff.2 ⟨wd, n₂, rfl⟩
  have n₁' : lookup (update d k₂ w₂) k₁ = none := by
    rw [lookup_update_ne _ _ hne]; rwa [lookup_update_ne _ _ hne] at n₁
  have e₁ : concat (element k₁ w₁) (update d k₂ w₂) = some (update (update d k₂ w₂) k₁ w₁) :=
    concat_element_iff.2 ⟨wf_update wd, n₁', rfl⟩
  have := concat_bind_of_concat e₂ e₁
  rw [hx] at this
  exact ⟨_, this⟩

end MapHook

/-- The map step of `def_close`: a cell map that a rule's right-hand side rebuilds at the keys it
matched is defined. -/
macro "k2l_map_defined" : tactic => `(tactic| first
  | (apply MapHook.concat_element_rebuild; assumption)
  | (apply MapHook.concat_element2_rebuild_a <;> assumption)
  | (apply MapHook.concat_element2_rebuild_b <;> assumption))

end KPrelude
