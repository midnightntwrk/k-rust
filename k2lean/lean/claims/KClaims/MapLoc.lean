import KPrelude.Scaffold
import KPrelude.Ext

/-!
# A rule's binding in a map a claim describes

A claim describes a map cell by its explicit bindings and its frames: `K |-> V REST` is the
hypothesis `concat (element K V) REST = some m`, and `A B` is `concat A B = some m` (`_Map_` is
partial: defined when the two sides bind no key in common). A rule that matches the cell at a
key states `concat (element k v) r = some m`. These lemmas locate that binding in the
description, part by part (`of_concat`, then `of_element` or `of_unit` at a leaf), and build it
from the description where a step must be shown to exist (`lookup_left`, `lookup_right`,
`wf_of_concat`).
-/

set_option linter.unusedSectionVars false

namespace KClaims.MapLoc

open KPrelude KPrelude.MapHook ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [Std.TransOrd K]
  [Std.LawfulEqOrd K]

theorem lookup_unit (k : K) : lookup (unit : M) k = none := by
  rw [lookup_def]; unfold unit; rw [toList_ofList]; rfl

theorem wf_of_concat {a b m : M} (h : concat a b = some m) : WF m :=
  SAL.sorted_of_concat (concat_toList h)

theorem wf_left_of_concat {a b m : M} (h : concat a b = some m) : WF a :=
  SAL.sorted_of_concat_left (concat_toList h)

/-- The map without a key `b` does not bind, beside `b`. -/
theorem concat_remove_left {a b m : M} {k : K} (h : concat a b = some m) (hb : lookup b k = none) :
    concat (remove a k) b = some (remove m k) := by
  have wa := wf_left_of_concat h
  have wb := wf_right_of_concat h
  obtain ⟨m', hm'⟩ := concat_exists (wf_remove wa) wb fun j => by
    by_cases e : j = k
    · subst e; exact Or.inl (lookup_remove_self j wa)
    · rw [lookup_remove_ne e wa]; exact concat_disj_lookup h j
  rw [hm']
  congr 1
  apply ext (wf_of_concat hm') (wf_remove (wf_of_concat h))
  intro j
  rw [lookup_concat hm']
  by_cases e : j = k
  · subst e; rw [lookup_remove_self j wa, lookup_remove_self j (wf_of_concat h), hb]; rfl
  · rw [lookup_remove_ne e wa, lookup_remove_ne e (wf_of_concat h), lookup_concat h]

/-- The same on the right. -/
theorem concat_remove_right {a b m : M} {k : K} (h : concat a b = some m) (ha : lookup a k = none) :
    concat a (remove b k) = some (remove m k) := by
  have wa := wf_left_of_concat h
  have wb := wf_right_of_concat h
  obtain ⟨m', hm'⟩ := concat_exists wa (wf_remove wb) fun j => by
    by_cases e : j = k
    · subst e; exact Or.inr (lookup_remove_self j wb)
    · rw [lookup_remove_ne e wb]; exact concat_disj_lookup h j
  rw [hm']
  congr 1
  apply ext (wf_of_concat hm') (wf_remove (wf_of_concat h))
  intro j
  rw [lookup_concat hm']
  by_cases e : j = k
  · subst e; rw [lookup_remove_self j wb, lookup_remove_self j (wf_of_concat h), ha]; rfl
  · rw [lookup_remove_ne e wb, lookup_remove_ne e (wf_of_concat h), lookup_concat h]

/-- A binding of `A B` is `A`'s, at a key `B` does not bind, or `B`'s, at a key `A` does not
bind; the rest of the match is the other side with the rest of the side that binds it. -/
theorem of_concat {k : K} {v : V} {a b m r : M} (hab : concat a b = some m)
    (h : concat (element k v) r = some m) :
    (∃ ra, concat (element k v) ra = some a ∧ lookup b k = none ∧ concat ra b = some r) ∨
    (∃ rb, concat (element k v) rb = some b ∧ lookup a k = none ∧ concat a rb = some r) := by
  have hm := lookup_of_concat_element h
  have hr := remove_of_concat_element h
  cases ha : lookup a k with
  | some w =>
    have e := lookup_of_concat hab ha
    rw [hm] at e
    cases e
    have hb : lookup b k = none := (concat_disj_lookup hab k).resolve_left (by rw [ha]; simp)
    exact Or.inl ⟨remove a k, concat_element_remove (wf_left_of_concat hab) ha, hb,
      hr ▸ concat_remove_left hab hb⟩
  | none =>
    have hb : lookup b k = some v := by rw [← lookup_concat_right hab ha]; exact hm
    exact Or.inr ⟨remove b k, concat_element_remove (wf_right_of_concat hab) hb, rfl,
      hr ▸ concat_remove_right hab ha⟩

/-- A binding of a map of one binding is that binding, and the rest is empty. -/
theorem of_element {k k₀ : K} {v v₀ : V} {r : M} (h : concat (element k v) r = some (element k₀ v₀)) :
    k = k₀ ∧ v = v₀ ∧ r = unit := by
  have hl := lookup_of_concat_element h
  have e : k = k₀ := key_of_lookup_element (by rw [hl]; simp)
  subst e
  rw [lookup_element_self] at hl
  refine ⟨rfl, (Option.some.inj hl).symm, ?_⟩
  obtain ⟨wr, hrk, he⟩ := concat_element_iff.1 h
  apply ext wr wf_unit
  intro j
  rw [lookup_unit]
  by_cases e : j = k
  · subst e; exact hrk
  · have := congrArg (fun m => lookup m j) he
    simp only [lookup_update_ne _ _ e, lookup_element_ne e] at this
    exact this.symm

/-- A binding of a map given by its list (a literal, as evaluation leaves it): one of the list's
pairs, and the rest is the map without its key. -/
theorem of_list {k : K} {v : V} {r m : M} {l : List (K × V)} (h : concat (element k v) r = some m)
    (hl : toList m = l) : (k, v) ∈ l ∧ r = remove m k := by
  have hk := lookup_of_concat_element h
  rw [lookup_def, hl] at hk
  exact ⟨SAL.lookup_mem hk, (remove_of_concat_element h).symm⟩

/-- A binding of a map is its lookup at the key, and the rest is the map without the key (read
where the lookup evaluates: a literal at a key that compares). -/
theorem of_lookup {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    lookup m k = some v ∧ r = remove m k :=
  ⟨lookup_of_concat_element h, (remove_of_concat_element h).symm⟩

/-- A binding at a key the map is known to bind: its value is that binding's, and the rest is
the map without the key. -/
theorem of_found {k : K} {v v₀ : V} {r m : M} (h : concat (element k v) r = some m)
    (hl : lookup m k = some v₀) : v = v₀ ∧ r = remove m k := by
  have := lookup_of_concat_element h
  rw [hl] at this
  exact ⟨(Option.some.inj this).symm, (remove_of_concat_element h).symm⟩

/-- The empty map has no binding. -/
theorem of_unit {k : K} {v : V} {r : M} (h : concat (element k v) r = some (unit : M)) : False := by
  have := lookup_of_concat_element h
  rw [lookup_unit] at this
  cases this

/-- The binding of a key in a map of one binding. -/
theorem lookup_self {k : K} {v : V} : lookup (element k v : M) k = some v := lookup_element_self

/-- A binding of `A` is one of `A B`. -/
theorem lookup_left {a b m : M} (h : concat a b = some m) {k : K} {v : V}
    (ha : lookup a k = some v) : lookup m k = some v := lookup_of_concat h ha

/-- A binding of `B` is one of `A B`. -/
theorem lookup_right {a b m : M} (h : concat a b = some m) {k : K} {v : V}
    (hb : lookup b k = some v) : lookup m k = some v := lookup_of_concat_right h hb

/-- A key a map of one binding binds is that binding's (the absence of a binding read back). -/
theorem ne_of_lookup_element {k k₀ : K} {v₀ : V} (h : lookup (element k₀ v₀ : M) k = none) :
    k ≠ k₀ := by
  rintro rfl; rw [lookup_element_self] at h; cases h

/-- A match whose rest is empty is the binding itself. -/
theorem of_unit_rest {a r : M} (h : concat (unit : M) a = some r) : r = a := eq_of_concat_unit_left h

/-- A match whose other side is empty is the map itself. -/
theorem of_unit_right {a r : M} (h : concat a (unit : M) = some r) : r = a := by
  apply ext (wf_of_concat h) (wf_left_of_concat h)
  intro j
  rw [lookup_concat h, lookup_unit]
  cases lookup a j <;> rfl

/-- A binding put beside a rest that does not bind its key (the result of a rule's right-hand
side): defined, and the rest updated. -/
theorem build {k : K} {v : V} {r : M} (wr : WF r) (hk : lookup r k = none) :
    concat (element k v) r = some (update r k v) := concat_element_iff.2 ⟨wr, hk, rfl⟩

/-- A binding taken from a map that binds it: the rest is the map without it. -/
theorem take {k : K} {v : V} {m : M} (wm : WF m) (hl : lookup m k = some v) :
    concat (element k v) (remove m k) = some m := concat_element_remove wm hl

end KClaims.MapLoc

namespace KClaims.ListLoc

open KPrelude KPrelude.ListHook ListIso

variable {L E : Type} [ListIso L E]

/-- `ListItem(X) REST` is never `.List`. -/
theorem concat_element_ne_unit (x : E) (t : L) : concat (element x) t ≠ (unit : L) := by
  intro h
  have := congrArg toList h
  simp [concat, element, unit, toList_ofList] at this

/-- `ListItem(X) REST` against a list with a first element: `X` is that element and `REST` the
rest of the list. -/
theorem of_cons {x a : E} {t l : L} {rest : List E} (h : concat (element x) t = l)
    (hl : toList l = a :: rest) : x = a ∧ t = ofList rest := by
  have e := congrArg toList h
  simp only [concat, element, toList_ofList, List.singleton_append] at e
  rw [hl] at e
  injection e with e₁ e₂
  exact ⟨e₁, by rw [← e₂, ofList_toList]⟩

/-- `ListItem(X) REST` against the empty list. -/
theorem of_nil {x : E} {t l : L} (h : concat (element x) t = l) (hl : toList l = []) : False := by
  have e := congrArg toList h
  simp only [concat, element, toList_ofList, List.singleton_append] at e
  rw [hl] at e
  cases e

end KClaims.ListLoc
