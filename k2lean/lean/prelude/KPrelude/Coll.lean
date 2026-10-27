import KPrelude.SAL

/-!
# Collection carriers and the `MAP` hooks

A generated project defines its `Map` carrier inside the term block (it must, since map entries
are `KItem`s and `KItem` has a `Map` leaf) as a list-like inductive, and proves it isomorphic to
`List (KItem × KItem)` through `ListIso`. The hooks below are written once, against `ListIso`,
on top of `SAL`.

`MapRepr` lets a generated carrier supply direct implementations of the hot operations (no
conversion to a list), each with a proof that it equals the `SAL` operation on `toList`; the
defaults are the conversions themselves.

The hooks follow `domains.md`'s `MAP` module: `_Map_` (`MAP.concat`) is partial (undefined on
overlapping keys), `MAP.lookup` is partial (undefined on a missing key), `MAP.update` and
`MAP.remove` are total.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

/-- A carrier isomorphic to `List E`. -/
class ListIso (M : Type) (E : outParam Type) where
  toList : M → List E
  ofList : List E → M
  toList_ofList : ∀ l, toList (ofList l) = l
  ofList_toList : ∀ m, ofList (toList m) = m

open ListIso in
/-- Direct implementations of the map operations on a carrier, equal to the list operations. -/
class MapRepr (M : Type) (K V : outParam Type) [Ord K] [ListIso M (K × V)] where
  lookupR : K → M → Option V := fun k m => SAL.lookup k (toList m)
  insertR : K → V → M → M := fun k v m => ofList (SAL.insert k v (toList m))
  eraseR : K → M → M := fun k m => ofList (SAL.erase k (toList m))
  sortedR : M → Bool := fun m => SAL.sortedAdj (toList m)
  lookupR_eq : ∀ k m, lookupR k m = SAL.lookup k (toList m) := by intros; rfl
  insertR_eq : ∀ k v m, insertR k v m = ofList (SAL.insert k v (toList m)) := by intros; rfl
  eraseR_eq : ∀ k m, eraseR k m = ofList (SAL.erase k (toList m)) := by intros; rfl
  sortedR_eq : ∀ m, sortedR m = SAL.sortedAdj (toList m) := by intros; rfl

namespace MapHook

open ListIso

variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V]

/-- The well-formedness invariant of a map value (keys strictly sorted). -/
def WF (m : M) : Prop := SAL.Sorted (toList m)

/-- `.Map` -/
def unit : M := ofList []
/-- `K |-> V` -/
def element (k : K) (v : V) : M := ofList [(k, v)]
/-- `M₁ M₂` (partial) -/
def concat (a b : M) : Option M := (SAL.concat (toList a) (toList b)).map ofList
/-- `M[K <- V]` -/
def update (m : M) (k : K) (v : V) : M := MapRepr.insertR k v m
/-- `M[K]` (partial) -/
def lookup (m : M) (k : K) : Option V := MapRepr.lookupR k m
/-- `M[K] orDefault D` -/
def lookupOrDefault (m : M) (k : K) (d : V) : V := (MapRepr.lookupR k m).getD d
/-- `M[K <- undef]` -/
def remove (m : M) (k : K) : M := MapRepr.eraseR k m
/-- `K in_keys(M)` -/
def inKeys (k : K) (m : M) : Bool := (MapRepr.lookupR k m).isSome
/-- A map literal from its bindings (used for concrete terms; keys are distinct). -/
def ofEntries (l : List (K × V)) : M := l.foldl (fun m p => update m p.1 p.2) unit
/-- `size(M)` -/
def size (m : M) : Int := (toList m).length
/-- The executable check of `WF`. -/
def wfb (m : M) : Bool := MapRepr.sortedR m

theorem update_def (m : M) (k : K) (v : V) : update m k v = ofList (SAL.insert k v (toList m)) :=
  MapRepr.insertR_eq k v m
theorem lookup_def (m : M) (k : K) : lookup m k = SAL.lookup k (toList m) := MapRepr.lookupR_eq k m
theorem remove_def (m : M) (k : K) : remove m k = ofList (SAL.erase k (toList m)) := MapRepr.eraseR_eq k m

section Laws

variable [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem wfb_iff (m : M) : wfb m = true ↔ WF m := by
  unfold wfb WF; rw [MapRepr.sortedR_eq]; exact SAL.sortedAdj_iff _

theorem wf_update {m : M} {k : K} {v : V} (h : WF m) : WF (update m k v) := by
  unfold WF; rw [update_def, toList_ofList]; exact SAL.sorted_insert h

theorem wf_remove {m : M} {k : K} (h : WF m) : WF (remove m k) := by
  unfold WF; rw [remove_def, toList_ofList]; exact SAL.sorted_erase h

theorem wf_unit : WF (unit : M) := by unfold WF unit; rw [toList_ofList]; exact SAL.Sorted.nil

theorem wf_element {k : K} {v : V} : WF (element k v : M) := by
  unfold WF element; rw [toList_ofList]; exact SAL.Sorted.cons (by simp) SAL.Sorted.nil

/-- The pattern `K |-> V REST` with `K` bound, read as the executable matcher reads it. -/
theorem concat_element_iff {k : K} {v : V} {r m : M} :
    concat (element k v) r = some m ↔ WF r ∧ lookup r k = none ∧ m = update r k v := by
  unfold concat element WF
  rw [lookup_def, update_def, toList_ofList]
  constructor
  · intro h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    obtain ⟨h1, h2, rfl⟩ := SAL.concat_singleton_iff.1 hl
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    simp only [Option.map_eq_some_iff]
    exact ⟨_, SAL.concat_singleton_iff.2 ⟨h1, h2, rfl⟩, rfl⟩

theorem wf_of_concat_element {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    WF m := by
  obtain ⟨h1, _, rfl⟩ := concat_element_iff.1 h
  exact wf_update h1

theorem wfb_of_concat_element {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    wfb m = true := (wfb_iff m).2 (wf_of_concat_element h)

theorem wf_rest_of_concat_element {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    WF r := (concat_element_iff.1 h).1

theorem lookup_of_concat_element {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    lookup m k = some v := by
  obtain ⟨_, _, rfl⟩ := concat_element_iff.1 h
  rw [lookup_def, update_def, toList_ofList]; exact SAL.lookup_insert_self k v _

/-- `_Map_` is associative where defined: a match of `a (b c)` is one of `(a b) c` (a pattern
`A B C` of map variables and elements is left-nested). -/
theorem concat_bind_of_concat {a b c bc m : M} (h₁ : concat b c = some bc)
    (h₂ : concat a bc = some m) : (concat a b).bind (fun r => concat r c) = some m := by
  unfold concat at *
  simp only [Option.map_eq_some_iff] at h₁ h₂
  obtain ⟨l₁, e₁, rfl⟩ := h₁
  obtain ⟨l₂, e₂, rfl⟩ := h₂
  rw [toList_ofList] at e₂
  obtain ⟨ab, hab, habc⟩ := SAL.concat_assoc_left e₁ e₂
  simp [hab, toList_ofList, habc]

/-- `M[K <- V][K]` is `V`. -/
theorem lookup_update_self (m : M) (k : K) (v : V) : lookup (update m k v) k = some v := by
  rw [lookup_def, update_def, toList_ofList]; exact SAL.lookup_insert_self k v _

/-- A lookup after an update at another key is unchanged: `M[K <- V][K']` is `M[K']` when
`K' ≠ K`. -/
theorem lookup_update_ne (m : M) {k k' : K} (v : V) (hne : k' ≠ k) :
    lookup (update m k v) k' = lookup m k' := by
  rw [lookup_def, update_def, toList_ofList, SAL.lookup_insert_ne v hne, lookup_def]

theorem remove_of_concat_element {k : K} {v : V} {r m : M} (h : concat (element k v) r = some m) :
    remove m k = r := by
  obtain ⟨h1, h2, rfl⟩ := concat_element_iff.1 h
  rw [lookup_def] at h2
  rw [remove_def, update_def, toList_ofList, SAL.erase_insert_of_lookup_none h1 h2, ofList_toList]

/-- Soundness of the executable matcher of `K |-> V REST`: lookup, and the rest is `remove`. -/
theorem concat_element_remove {k : K} {v : V} {m : M} (hw : WF m) (h : lookup m k = some v) :
    concat (element k v) (remove m k) = some m := by
  rw [lookup_def] at h
  unfold concat element
  rw [remove_def, toList_ofList, toList_ofList, SAL.concat_singleton_erase hw h]
  simp [ofList_toList]

theorem concat_element_unique {k : K} {v₁ v₂ : V} {r₁ r₂ m : M}
    (h₁ : concat (element k v₁) r₁ = some m) (h₂ : concat (element k v₂) r₂ = some m) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  have l₁ := lookup_of_concat_element h₁
  have l₂ := lookup_of_concat_element h₂
  rw [l₁] at l₂
  exact ⟨Option.some.inj l₂, (remove_of_concat_element h₁).symm.trans (remove_of_concat_element h₂)⟩

end Laws

end MapHook

end KPrelude
