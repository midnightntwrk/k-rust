import KPrelude.Scaffold
import KPrelude.InvColl

/-! A map that holds exactly the bindings of a partial function, through injective encodings of its
arguments and results (`Rep`). Two definitions have their own `KItem`s, so the maps of two
configurations, one of each, are compared through the function both represent: the same bindings,
each written with its own definition's constructors. This compares bindings, not the maps' order:
two libraries may order their keys differently. The lemmas follow `Rep` through the map patterns of
K rules: a lookup, an insertion, a rebinding, an insertion beside a matched binding. -/

set_option linter.unusedSectionVars false

namespace KPrelude.MapRep

open MapHook Classical
section
variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K] {α β : Type} [DecidableEq α]

/-- `m` binds `enc a` to `val b` exactly where `f a = some b`. -/
def Rep (enc : α → K) (val : β → V) (m : M) (f : α → Option β) : Prop :=
  WF m ∧ ∀ k w, lookup m k = some w ↔ ∃ a b, k = enc a ∧ w = val b ∧ f a = some b

/-- `f` with `a` bound to `b`. -/
def upd (f : α → Option β) (a : α) (b : β) : α → Option β := fun x => if x = a then some b else f x

variable {enc : α → K} {val : β → V}

theorem lookup_unit' (k : K) : lookup (unit : M) k = none := by
  rw [lookup_def]; unfold unit; rw [ListIso.toList_ofList]; rfl

theorem rep_unit : Rep enc val (unit : M) (fun _ => none) :=
  ⟨wf_unit, fun k w => by simp [lookup_unit']⟩

theorem rep_lookup (he : Function.Injective enc) {m : M}
    {f : α → Option β} (h : Rep enc val m f) (a : α) : lookup m (enc a) = (f a).map val := by
  cases e : lookup m (enc a) with
  | none =>
    cases fa : f a with
    | none => rfl
    | some b => exact absurd ((h.2 _ _).2 ⟨a, b, rfl, rfl, fa⟩) (by rw [e]; simp)
  | some w =>
    obtain ⟨a', b, ek, rfl, fa⟩ := (h.2 _ _).1 e
    cases he ek
    rw [fa]; rfl

/-- What `f` gives at `a`, read from a binding of `m`. -/
theorem rep_some (he : Function.Injective enc) (hv : Function.Injective val) {m : M}
    {f : α → Option β} (h : Rep enc val m f) {a : α} {b : β} (hl : lookup m (enc a) = some (val b)) :
    f a = some b := by
  rw [rep_lookup he h] at hl
  cases fa : f a with
  | none => rw [fa] at hl; cases hl
  | some b' => rw [fa] at hl; cases hv (Option.some.inj hl); rfl

theorem rep_none (he : Function.Injective enc) {m : M}
    {f : α → Option β} (h : Rep enc val m f) {a : α} (hl : lookup m (enc a) = none) : f a = none := by
  rw [rep_lookup he h] at hl
  cases fa : f a with
  | none => rfl
  | some b => rw [fa] at hl; cases hl

/-- A map whose bindings are `m`'s with `enc a` bound to `val b` represents `upd f a b`. -/
theorem rep_of_lookup (he : Function.Injective enc) {m m' : M} {f : α → Option β}
    (h : Rep enc val m f) (hw : WF m') {a : α} {b : β}
    (hl : ∀ k, lookup m' k = if k = enc a then some (val b) else lookup m k) :
    Rep enc val m' (upd f a b) := by
  refine ⟨hw, fun k w => ?_⟩
  rw [hl k]
  by_cases hk : k = enc a
  · subst hk
    simp only [ite_true, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨a, b, rfl, rfl, by simp [upd]⟩
    · rintro ⟨a', b', e, rfl, fa⟩
      cases he e
      simp [upd] at fa; rw [fa]
  · simp only [hk, ite_false]
    rw [h.2 k w]
    constructor
    · rintro ⟨a', b', rfl, rfl, fa⟩
      exact ⟨a', b', rfl, rfl, by simp [upd, show a' ≠ a from fun e => hk (e ▸ rfl), fa]⟩
    · rintro ⟨a', b', rfl, rfl, fa⟩
      exact ⟨a', b', rfl, rfl, by simpa [upd, show a' ≠ a from fun e => hk (e ▸ rfl)] using fa⟩

/-- An insertion `(enc a ↦ val b) m`. -/
theorem rep_insert (he : Function.Injective enc) {m m' : M} {f : α → Option β}
    (h : Rep enc val m f) {a : α} {b : β} (hc : concat (element (enc a) (val b)) m = some m') :
    Rep enc val m' (upd f a b) := by
  obtain ⟨hw, -, rfl⟩ := concat_element_iff.1 hc
  refine rep_of_lookup he h (wf_update hw) fun k => ?_
  by_cases hk : k = enc a
  · subst hk; simp [lookup_update_self]
  · simp [hk, lookup_update_ne _ _ hk]

/-- A rebinding: `(enc a ↦ v) D` becomes `(enc a ↦ val b) D`. -/
theorem rep_rebind (he : Function.Injective enc) {m m' D : M} {f : α → Option β}
    (h : Rep enc val m f) {a : α} {b : β} {v : V} (h₁ : concat (element (enc a) v) D = some m)
    (h₂ : concat (element (enc a) (val b)) D = some m') : Rep enc val m' (upd f a b) := by
  refine rep_of_lookup he h (wf_of_concat h₂) fun k => ?_
  by_cases hk : k = enc a
  · subst hk; simp [lookup_of_concat_element h₂]
  · simp only [hk, ite_false]
    rw [lookup_concat_right h₂ (lookup_element_ne hk), lookup_concat_right h₁ (lookup_element_ne hk)]

/-- An insertion beside a matched binding: `(k₁ ↦ v₁) D` becomes `(k₁ ↦ v₁) (enc a ↦ val b) D`. -/
theorem rep_insert2 (he : Function.Injective enc) {m m' D x : M} {f : α → Option β}
    (h : Rep enc val m f) {a : α} {b : β} {k₁ : K} {v₁ : V}
    (h₁ : concat (element k₁ v₁) D = some m)
    (h₂ : concat (element k₁ v₁) (element (enc a) (val b)) = some x) (h₃ : concat x D = some m') :
    Rep enc val m' (upd f a b) := by
  refine rep_of_lookup he h (wf_of_concat h₃) fun k => ?_
  rw [lookup_concat h₃, lookup_concat h₂, lookup_concat h₁]
  by_cases hk : k = enc a
  · subst hk
    have hn : lookup (element k₁ v₁ : M) (enc a) = none := by
      rcases concat_disj_lookup h₂ (enc a) with e | e
      · exact e
      · simp [lookup_element_self] at e
    simp [hn, lookup_element_self]
  · simp [hk, lookup_element_ne hk]

/-- An insertion `(k ↦ v) m` exists where `m` does not bind `k`. -/
theorem ins_some {m : M} {k : K} {v : V} (hw : WF m) (hn : lookup m k = none) :
    concat (element k v) m = some (update m k v) :=
  concat_element_iff.2 ⟨hw, hn, rfl⟩

/-- The rebinding of a key `m` binds. -/
theorem rebind_some {m : M} {k : K} {v : V} (hw : WF m) :
    concat (element k v) (remove m k) = some (update (remove m k) k v) :=
  concat_element_iff.2 ⟨wf_remove hw, lookup_remove_self k hw, rfl⟩

/-- A map of one binding. -/
theorem element_eq_update {k : K} {v : V} : (element k v : M) = update unit k v :=
  ext wf_element (wf_update wf_unit) fun j => by
    by_cases hj : j = k
    · subst hj; rw [lookup_element_self, lookup_update_self]
    · rw [lookup_element_ne hj, lookup_update_ne _ _ hj, lookup_unit']

end

end KPrelude.MapRep
