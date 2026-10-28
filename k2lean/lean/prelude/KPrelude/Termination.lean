import Lean
import KPrelude.Coll
import KPrelude.Ext
import KPrelude.Hooks

/-!
# Termination of generated recursive functions

A recursive K function becomes a well-founded definition (`termination_by`, `decreasing_by`):
its measure is a `sizeOf`, an integer distance, a shape, or a lexicographic tuple of these and of
ranks (with the arity-indexed term universe no recursion at a fixed sort is structural, so every
one is well-founded). This module gives the facts those
proofs need and the tactic the generator emits:

* `ListSizeOf`: a collection carrier whose `sizeOf` is its list's plus one constructor; the
  generator proves it for each collection sort of the arity-indexed universe (`Term.coll_S l`).
  From it, the hooks that
  destructure a collection give smaller pieces: `ListHook.uncons`, `ListHook.unsnoc`, and the
  value and the rest of a map pattern `K |-> V REST` (`MapHook.lookup`, `MapHook.remove`), for
  a bound key and, through the certificate `MapHook.chooseFirst` passes, for a free one
  (`MapSizeOf`).
* Facts about defined partial hooks, for `omega`: an index accepted by `BytesHook.get` or
  `BytesHook.substr` is in range, a defined `StringHook.find` is `-1` or an index at which the
  needle fits, the length of a `StringHook.substr` is at most what follows its start, a defined `IntHook.tdiv`/`IntHook.emod` by a literal is a
  Euclidean division (`tdiv` of a nonnegative dividend), a defined `IntHook.shr` of a positive
  operand by at least one bit is smaller than it, and a quotient `a * n / m` is smaller
  than `a` in absolute value when `n` is smaller than `m`.
* `Shape`, `ListShape`: the shape of a term (its constructors and builtin values, each counting
  one), a termination measure that ignores the magnitude of integers and byte arrays; the
  generator defines it for the arity-indexed universe (`Term.shape`), and the list hooks give its
  laws (`ListHook.shape_concat`, `shape_uncons`, …).
* `@[k2l_fact]`: lemmas about generated functions (what a function returns, the range of an
  integer function, a bound on a result's shape) that the generator derives and proves, for
  `k2l_facts` to apply.
* `k2l_facts` adds these facts for every matching hypothesis of a goal (and for every application
  of a total function with a registered range), a copy of every Boolean hypothesis (a requires),
  and the value of every failed earlier equation (`he : e = none` with `e` a local definition), so
  that `simp` can rewrite them even where a recursive call's proof depends on the original.
* `k2l_split_hyp` splits a `match`/`if` in some hypothesis; repeated after unfolding a generated
  function in `h : f x = some r`, it enumerates the function's cases; `k2l_fn_facts` proves a fact
  about a generated function that way (`k2l_ih` adds the lemma being proved at the recursive
  calls, for a lemma proved by well-founded recursion).
* `k2l_decreasing [r₁, …]` closes a goal of `decreasing_by`: the facts, each failed guard
  (`(if h : c then … else none) = none`) turned into `¬ c`, the integer and Boolean hooks
  unfolded, lexicographic goals split by `Prod.lex_def`, the given rank functions unfolded,
  then `omega`, and where that fails `simp_all` (which knows the `sizeOf` of the generated
  constructors) and `omega`; `k2l_decreasing_m [m₁, …] using [d₁, …]` first unfolds and splits the measures
  that are definitions by cases (`f.k2l_measure`) and unfolds the shapes and constructors `dᵢ`.

No statement here depends on the exact `sizeOf` of an injection (`Term.inj`): the size laws are
about collection constructors only.
-/

set_option linter.unusedSectionVars false

namespace KPrelude

open ListIso

/-- A collection carrier whose `sizeOf` is one more than the `sizeOf` of its list. -/
class ListSizeOf (M : Type) (E : outParam Type) [ListIso M E] [SizeOf M] [SizeOf E] : Prop where
  sizeOf_ofList : ∀ l : List E, sizeOf (ofList l : M) = 1 + sizeOf l

section
variable {M E : Type} [ListIso M E] [SizeOf M] [SizeOf E] [ListSizeOf M E]

theorem sizeOf_eq_toList (m : M) : sizeOf m = 1 + sizeOf (toList m) := by
  conv => lhs; rw [← ofList_toList m]
  exact ListSizeOf.sizeOf_ofList _

end

theorem sizeOf_dropLast_lt {E : Type} [SizeOf E] : ∀ (xs : List E), xs ≠ [] → sizeOf xs.dropLast < sizeOf xs
  | [], h => absurd rfl h
  | [_], _ => by simp only [List.dropLast, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
  | a :: b :: t, _ => by
    have ih := sizeOf_dropLast_lt (b :: t) (by simp)
    simp only [List.dropLast_cons_cons, List.cons.sizeOf_spec] at ih ⊢
    omega

/-- A list carrier whose `sizeOf` is its list's plus a constant: one (`ListSizeOf`, the
arity-indexed universe) or none (a carrier with constructors `.nil`/`.cons x r`). The termination facts of `ListItem(X) REST` and `REST ListItem(X)`. -/
class ListSizeAffine (L E : Type) [ListIso L E] [SizeOf L] [SizeOf E] : Prop where
  affine : ∃ c : Nat, ∀ l : List E, sizeOf (ofList l : L) = c + sizeOf l

instance listSizeAffine_of_listSizeOf {L E : Type} [ListIso L E] [SizeOf L] [SizeOf E]
    [ListSizeOf L E] : ListSizeAffine L E := ⟨⟨1, ListSizeOf.sizeOf_ofList⟩⟩

namespace ListHook
variable {L E : Type} [ListIso L E] [SizeOf L] [SizeOf E] [ListSizeAffine L E]

/-- The pieces of `ListItem(X) REST` are smaller than the list. -/
theorem sizeOf_uncons {l t : L} {x : E} (h : uncons l = some (x, t)) :
    sizeOf x < sizeOf l ∧ sizeOf t < sizeOf l := by
  obtain ⟨c, hc⟩ := ListSizeAffine.affine (L := L) (E := E)
  unfold uncons at h
  split at h
  · simp at h
  · next y ys hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl' := hc (toList l)
    rw [ofList_toList, hl] at hl'
    rw [hl', hc ys]
    simp only [List.cons.sizeOf_spec]
    omega

/-- The pieces of `REST ListItem(X)` are smaller than the list. -/
theorem sizeOf_unsnoc {l t : L} {x : E} (h : unsnoc l = some (t, x)) :
    sizeOf x < sizeOf l ∧ sizeOf t < sizeOf l := by
  obtain ⟨c, hc⟩ := ListSizeAffine.affine (L := L) (E := E)
  unfold unsnoc at h
  split at h
  · simp at h
  · next y hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hne : toList l ≠ [] := by intro e; simp [e] at hl
    have hmem : y ∈ toList l := List.mem_of_getLast? hl
    have hl' := hc (toList l)
    rw [ofList_toList] at hl'
    rw [hl', hc]
    have h1 := List.sizeOf_lt_of_mem hmem
    have h2 := sizeOf_dropLast_lt (toList l) hne
    omega

end ListHook

namespace SAL
variable {α β : Type} [Ord α] [SizeOf α] [SizeOf β]

theorem sizeOf_erase_lt {k : α} {v : β} : ∀ {m : List (α × β)}, lookup k m = some v → sizeOf (erase k m) < sizeOf m
  | [], h => by simp [lookup] at h
  | (k', v') :: t, h => by
    unfold lookup at h
    unfold erase
    split at h
    · simp at h
    · simp only [List.cons.sizeOf_spec]; omega
    · have := sizeOf_erase_lt h
      simp only [List.cons.sizeOf_spec]
      omega

end SAL

/-- A map carrier whose `sizeOf` decreases from a map to the value and to the rest of a binding:
the termination facts of `K |-> V REST` (key bound or free). Instances: every carrier whose
`sizeOf` is its list's plus one (`ListSizeOf`, the arity-indexed universe), and, through
`MapHook.mapSizeOf_of_add`, a carrier with constructors `.nil`/`.cons k v r`, whose `sizeOf` is
its list's minus its length. -/
class MapSizeOf (M K V : Type) [Ord K] [ListIso M (K × V)] [MapRepr M K V] [SizeOf M] [SizeOf V] :
    Prop where
  sizeOf_lookup : ∀ {m : M} {k : K} {v : V}, MapHook.lookup m k = some v → sizeOf v < sizeOf m
  sizeOf_remove : ∀ {m : M} {k : K} {v : V}, MapHook.lookup m k = some v →
    sizeOf (MapHook.remove m k) < sizeOf m

namespace SAL
variable {α β : Type} [Ord α] [SizeOf α] [SizeOf β]

theorem length_erase_of_lookup {k : α} {v : β} : ∀ {m : List (α × β)}, lookup k m = some v →
    (erase k m).length + 1 = m.length
  | [], h => by simp [lookup] at h
  | (k', v') :: t, h => by
    unfold lookup at h
    unfold erase
    split at h
    · simp at h
    · simp
    · have := length_erase_of_lookup h
      simp only [List.length_cons]
      omega

theorem length_le_sizeOf {γ : Type} [SizeOf γ] : ∀ l : List γ, l.length ≤ sizeOf l
  | [] => by simp
  | _ :: t => by have := length_le_sizeOf t; simp only [List.cons.sizeOf_spec, List.length_cons]; omega

theorem sizeOf_erase_add {k : α} {v : β} : ∀ {m : List (α × β)}, lookup k m = some v →
    sizeOf (erase k m) + 2 + sizeOf v ≤ sizeOf m
  | [], h => by simp [lookup] at h
  | (k', v') :: t, h => by
    unfold lookup at h
    unfold erase
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
      omega
    · have := sizeOf_erase_add h
      simp only [List.cons.sizeOf_spec]
      omega

end SAL

namespace MapHook
variable {M K V : Type} [Ord K] [ListIso M (K × V)] [MapRepr M K V] [SizeOf M] [SizeOf K] [SizeOf V]
  [Std.TransOrd K] [Std.LawfulEqOrd K]

instance mapSizeOf_of_listSizeOf [ListSizeOf M (K × V)] : MapSizeOf M K V where
  sizeOf_lookup {m k v} h := by
    rw [lookup_def] at h
    have h1 := List.sizeOf_lt_of_mem (SAL.lookup_mem h)
    rw [sizeOf_eq_toList m]
    simp only [Prod.mk.sizeOf_spec] at h1
    omega
  sizeOf_remove {m k v} h := by
    rw [lookup_def] at h
    rw [remove_def, sizeOf_eq_toList m, ListSizeOf.sizeOf_ofList]
    have := SAL.sizeOf_erase_lt h
    omega

/-- `MapSizeOf` for a carrier whose `sizeOf` plus its length is its list's `sizeOf` (a carrier
`.nil`/`.cons k v r`: one constructor per binding instead of a cons and a
pair). -/
theorem mapSizeOf_of_add (h : ∀ l : List (K × V), sizeOf (ofList l : M) + l.length = sizeOf l) :
    MapSizeOf M K V where
  sizeOf_lookup {m k v} hl := by
    rw [lookup_def] at hl
    have h2 := h (toList m)
    rw [ofList_toList] at h2
    have h4 := SAL.sizeOf_erase_add hl
    have h5 := SAL.length_erase_of_lookup hl
    have h6 := SAL.length_le_sizeOf (SAL.erase k (toList m))
    omega
  sizeOf_remove {m k v} hl := by
    rw [lookup_def] at hl
    rw [remove_def]
    have h2 := h (toList m)
    rw [ofList_toList] at h2
    have h3 := h (SAL.erase k (toList m))
    have h4 := SAL.sizeOf_erase_add hl
    have h5 := SAL.length_erase_of_lookup hl
    omega

variable [MapSizeOf M K V]

/-- The value of `K |-> V REST` is smaller than the map. -/
theorem sizeOf_lookup {m : M} {k : K} {v : V} (h : lookup m k = some v) : sizeOf v < sizeOf m :=
  MapSizeOf.sizeOf_lookup h

/-- The rest of `K |-> V REST` is smaller than the map. -/
theorem sizeOf_remove {m : M} {k : K} {v : V} (h : lookup m k = some v) :
    sizeOf (remove m k) < sizeOf m :=
  MapSizeOf.sizeOf_remove h

/-- The value and the rest of a match `k |-> v r` of `m` (a free-key pattern's certificate)
are smaller than the map. -/
theorem sizeOf_of_concat_element {m r : M} {k : K} {v : V}
    (h : concat (element k v) r = some m) : sizeOf v < sizeOf m ∧ sizeOf r < sizeOf m := by
  have hl := lookup_of_concat_element h
  refine ⟨sizeOf_lookup hl, ?_⟩
  rw [← remove_of_concat_element h]
  exact sizeOf_remove hl

end MapHook

namespace BytesHook

/-- An index `B[I]` accepts is in range. -/
theorem get_facts {b : List UInt8} {i v : Int} (h : get b i = some v) : 0 ≤ i ∧ i < length b := by
  unfold get at h
  split at h
  · next hi =>
    refine ⟨hi, ?_⟩
    cases hb : b[i.toNat]? with
    | none => simp [hb] at h
    | some x =>
      have := (List.getElem?_eq_some_iff.1 hb).1
      unfold length; omega
  · simp at h

/-- The bounds `substrBytes(B, I, J)` accepts, and the length of its result. -/
theorem substr_facts {b r : List UInt8} {i j : Int} (h : substr b i j = some r) :
    0 ≤ i ∧ i ≤ j ∧ j ≤ length b ∧ length r = j - i := by
  unfold substr at h
  split at h
  · next hb =>
    simp only [Option.some.injEq] at h
    subst h
    unfold length
    simp only [List.length_take, List.length_drop]
    omega
  · simp at h

end BytesHook

namespace StringHook

theorem length_nonneg (s : String) : 0 ≤ length s := by unfold length; omega

/-- The length of `substrString(S, I, J)` (the range clamped to `S`): at most `S`'s, and at most
what follows `I` when `I` is in range. -/
theorem substr_facts (s : String) (i j : Int) :
    0 ≤ length (substr s i j) ∧ length (substr s i j) ≤ length s ∧
      (0 ≤ i → i ≤ length s → length (substr s i j) + i ≤ length s) := by
  unfold substr length
  simp only []
  split
  · simp only [String.length_ofList, List.length_take, List.length_drop, String.length_toList]
    omega
  · simp <;> omega

theorem find_go {ns : List Char} {hs : List Char} : ∀ (t : List Char) (k : Nat) (r : Int),
    k + t.length = hs.length → find.go hs ns k t = some r →
      -1 ≤ r ∧ r ≤ hs.length ∧ (r = -1 ∨ r + ns.length ≤ hs.length)
  | [], k, r, hk, h => by
    simp only [find.go] at h
    split at h <;> simp only [Option.some.injEq] at h <;> subst h
    · next he => simp [List.isEmpty_iff] at he; subst he; simp
    · simp
  | c :: t, k, r, hk, h => by
    simp only [find.go] at h
    split at h
    · next hp =>
      simp only [Option.some.injEq] at h; subst h
      have := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.1 hp)
      simp at hk this; omega
    · exact find_go t (k + 1) r (by simp at hk; omega) h

/-- A defined `findString(H, N, I)`: `-1`, or an index at which `N` fits in `H`. -/
theorem find_facts {h n : String} {i r : Int} (hf : find h n i = some r) :
    -1 ≤ r ∧ r ≤ length h ∧ (r = -1 ∨ r + length n ≤ length h) := by
  unfold find at hf
  split at hf
  · simp at hf
  · simp only at hf
    unfold length
    split at hf
    · simp only [Option.some.injEq] at hf; subst hf; simp
    · have := find_go (ns := n.toList) (hs := h.toList) _ _ r (by simp; omega) hf
      simp only [String.length_toList] at this
      exact this

end StringHook

namespace IntHook

/-- A defined `/Int`: the divisor is not zero, and on a nonnegative dividend it is `Int.ediv`
(which `omega` knows for a literal divisor). -/
theorem tdiv_facts {a b r : Int} (h : tdiv a b = some r) : b ≠ 0 ∧ (0 ≤ a → r = a / b) := by
  unfold tdiv at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨by assumption, fun ha => Int.tdiv_eq_ediv_of_nonneg ha⟩

/-- A defined `modInt` is `Int.emod`. -/
theorem emod_facts {a b r : Int} (h : emod a b = some r) : b ≠ 0 ∧ r = a % b := by
  unfold emod at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    exact ⟨by assumption, h.symm⟩

/-- A defined `>>Int`: the shift is not negative, a nonnegative operand gives a result between `0`
and itself, and a shift of at least one bit makes a positive operand smaller (`a >>> n` is
`a / 2 ^ n`). -/
theorem shr_facts {a b r : Int} (h : shr a b = some r) :
    0 ≤ b ∧ (0 ≤ a → 0 ≤ r ∧ r ≤ a) ∧ (1 ≤ b → 0 < a → r < a) := by
  unfold shr at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [Int.shiftRight_eq_div_pow]
    have hp : 0 < 2 ^ b.toNat := Nat.two_pow_pos _
    refine ⟨by omega, fun ha => ⟨Int.ediv_nonneg ha (by omega), Int.ediv_le_self _ ha⟩, fun h1 ha => ?_⟩
    have h2 : (2 : Int) ≤ ((2 ^ b.toNat : Nat) : Int) := by
      have : 2 ^ 1 ≤ 2 ^ b.toNat := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    apply Int.ediv_lt_of_lt_mul (by omega)
    have := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt ha)
    omega

/-- A quotient `a * n / m` is smaller than `a` in absolute value when `n` is smaller than `m`. -/
theorem tdiv_mul_facts {a n m r : Int} (h : tdiv (mul a n) m = some r) :
    n.natAbs < m.natAbs → r.natAbs < a.natAbs ∨ a = 0 := by
  intro hn
  unfold tdiv mul at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases ha : a = 0
    · exact Or.inr ha
    · left
      have ha' : 0 < a.natAbs := Int.natAbs_pos.2 ha
      rw [Int.natAbs_tdiv, Int.natAbs_mul]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm m.natAbs]; exact Nat.mul_lt_mul_of_pos_left hn ha')

/-- A divisor `d * i` is at least `i` in absolute value. -/
theorem tdiv_mul_divisor_facts {a d i r : Int} (h : tdiv a (mul d i) = some r) :
    i.natAbs ≤ (mul d i).natAbs ∧ d.natAbs ≤ (mul d i).natAbs := by
  unfold tdiv mul at h
  unfold mul
  split at h
  · simp at h
  · next hne =>
    have hd : d ≠ 0 := fun e => hne (by simp [e])
    have hi : i ≠ 0 := fun e => hne (by simp [e])
    rw [Int.natAbs_mul]
    exact ⟨Nat.le_mul_of_pos_left _ (Int.natAbs_pos.2 hd), Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 hi)⟩

end IntHook

/-! ## Shapes

The shape of a term is the number of its constructors and builtin values, every builtin value
counting one whatever its magnitude, and every element of a collection one more than its own
shape. A function that rebuilds a term from the pieces of another, replacing integers or byte
arrays by others, keeps its shape; Lean's `sizeOf` grows with an integer's magnitude. The
generator defines `Shape` for the arity-indexed universe and proves `ListShape` for its
collections. -/

/-- The shape of a value (a termination measure). -/
class Shape (α : Type) where
  shape : α → Nat

instance : Shape Unit := ⟨fun _ => 0⟩
instance {α β : Type} [Shape α] [Shape β] : Shape (α × β) := ⟨fun p => Shape.shape p.1 + Shape.shape p.2⟩

theorem shape_prod {α β : Type} [Shape α] [Shape β] (a : α) (b : β) :
    Shape.shape (a, b) = Shape.shape a + Shape.shape b := rfl
theorem shape_unit (u : Unit) : Shape.shape u = 0 := rfl

/-- A collection carrier whose shape is the sum of its elements' shapes, one more each. -/
class ListShape (M : Type) (E : outParam Type) [ListIso M E] [Shape M] [Shape E] : Prop where
  shape_ofList : ∀ l : List E, Shape.shape (ofList l : M) = (l.map (fun x => Shape.shape x + 1)).sum

section
variable {M E : Type} [ListIso M E] [Shape M] [Shape E] [ListShape M E]

theorem shape_eq_toList (m : M) : Shape.shape m = ((toList m).map (fun x => Shape.shape x + 1)).sum := by
  conv => lhs; rw [← ofList_toList m]
  exact ListShape.shape_ofList _

end

namespace ListHook
variable {L E : Type} [ListIso L E] [Shape L] [Shape E] [ListShape L E]

theorem shape_unit : Shape.shape (unit : L) = 0 := by
  simp [unit, ListShape.shape_ofList]

theorem shape_element (x : E) : Shape.shape (element x : L) = Shape.shape x + 1 := by
  simp [element, ListShape.shape_ofList]

theorem shape_concat (a b : L) : Shape.shape (concat a b) = Shape.shape a + Shape.shape b := by
  rw [concat, ListShape.shape_ofList, List.map_append, List.sum_append, ← shape_eq_toList,
    ← shape_eq_toList]

/-- `ListItem(X) REST`: the list's shape is the pieces', plus one. -/
theorem shape_uncons {l t : L} {x : E} (h : uncons l = some (x, t)) :
    Shape.shape l = Shape.shape x + 1 + Shape.shape t := by
  rw [← concat_element_of_uncons h, shape_concat, shape_element]

/-- `REST ListItem(X)`: the list's shape is the pieces', plus one. -/
theorem shape_unsnoc {l t : L} {x : E} (h : unsnoc l = some (t, x)) :
    Shape.shape l = Shape.shape x + 1 + Shape.shape t := by
  rw [← concat_element_of_unsnoc h, shape_concat, shape_element]; omega

end ListHook

namespace ListHook
variable {L E : Type} [ListIso L E]

/-- `ListItem(X) REST`: the rest is one element shorter. -/
theorem length_uncons {l t : L} {x : E} (h : uncons l = some (x, t)) :
    (toList l).length = (toList t).length + 1 := by
  rw [← concat_element_of_uncons h]
  simp [concat, element, toList_ofList]

/-- `REST ListItem(X)`: the rest is one element shorter. -/
theorem length_unsnoc {l t : L} {x : E} (h : unsnoc l = some (t, x)) :
    (toList l).length = (toList t).length + 1 := by
  rw [← concat_element_of_unsnoc h]
  simp [concat, element, toList_ofList]

end ListHook

open Lean Meta

/-! ## Facts about generated functions

`@[k2l_fact]` registers a lemma about a generated function for `k2l_facts`. A lemma whose last
explicit hypothesis is `f x₁ … xₙ = r` (`f` partial, `r` a pattern) is applied to every hypothesis
of that form; any other lemma, with explicit arguments `x₁ … xₙ` (`f` total), is applied to every
application `f a₁ … aₙ` in the goal and its hypotheses. The generator derives and proves these
lemmas (the range of an integer function, the facts a function's result satisfies, a bound on a
result's shape) for the termination proofs that need them. -/

/-- A registered fact lemma: the function it is about, whether it is triggered by a hypothesis
`f … = r` (rather than by an application of `f`), and the number of explicit arguments of `f`
it takes in the latter case. -/
structure FactLemma where
  fn : Name
  lemma : Name
  byHyp : Bool
  arity : Nat
  deriving Inhabited

initialize factExt : SimpleScopedEnvExtension FactLemma (Array FactLemma) ←
  registerSimpleScopedEnvExtension { addEntry := fun s e => s.push e, initial := #[] }

/-- The function a fact lemma is about (see the module comment). -/
private def factLemmaOf (lemma : Name) : MetaM FactLemma := do
  let info ← getConstInfo lemma
  forallTelescopeReducing info.type fun xs body => do
    -- the last explicit binder, if it is an equation `f … = r`
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    if let some h := explicit.back? then
      let ty ← instantiateMVars (← inferType h)
      if let some (_, lhs, _) := ty.eq? then
        if let some f := lhs.getAppFn.constName? then
          if !(body.containsFVar h.fvarId!) then
            return { fn := f, lemma, byHyp := true, arity := 0 }
    -- else: an application of `f` to exactly the explicit binders
    let found ← IO.mkRef (none : Option Name)
    forEachExpr body fun e => do
      if (← found.get).isNone then
        if let some f := e.getAppFn.constName? then
          let args := e.getAppArgs
          if explicit.size > 0 && args.size ≥ explicit.size &&
              (args.extract (args.size - explicit.size) args.size) == explicit then
            found.set (some f)
    match ← found.get with
    | some f => return { fn := f, lemma, byHyp := false, arity := explicit.size }
    | none => throwError "k2l_fact: {lemma} is neither `… → f … = r → P` nor about an application `f x₁ … xₙ` of its explicit arguments"

initialize registerBuiltinAttribute {
  name := `k2l_fact
  descr := "a fact about a generated function, for `k2l_facts` (KPrelude.Termination)"
  add := fun decl _ kind => do
    -- a lemma proved by well-founded recursion is elaborated through an auxiliary `_unary`
    -- (or `_mutual`) declaration, which synchronous elaboration (`-DElab.async=false`) also
    -- gives the lemma's attributes; the lemma itself is registered when it is added (TERM-3)
    if decl.isInternalDetail then return
    let e ← (factLemmaOf decl).run' {} {}
    factExt.add e kind
}

/-- The registered fact lemmas. -/
def factLemmasRegistered : CoreM (Array FactLemma) := return factExt.getState (← getEnv)

open Lean Meta Elab Tactic

/-- The facts about every application of a total hook (`k2l_facts`): the lemma, applied to the
application's last `arity` arguments. -/
private def totalHookLemmas : Array FactLemma :=
  #[{ fn := ``StringHook.length, lemma := ``StringHook.length_nonneg, byHyp := false, arity := 1 },
    { fn := ``StringHook.substr, lemma := ``StringHook.substr_facts, byHyp := false, arity := 3 }]

/-- The fact lemmas `k2l_facts` applies, keyed by the head of an equation's left-hand side. -/
private def factLemmas : List (Name × List Name) :=
  [(``ListHook.uncons, [``ListHook.sizeOf_uncons, ``ListHook.shape_uncons, ``ListHook.length_uncons]),
   (``ListHook.unsnoc, [``ListHook.sizeOf_unsnoc, ``ListHook.shape_unsnoc, ``ListHook.length_unsnoc]),
   (``MapHook.lookup, [``MapHook.sizeOf_lookup, ``MapHook.sizeOf_remove]),
   (``MapHook.concat, [``MapHook.sizeOf_of_concat_element]),
   (``BytesHook.get, [``BytesHook.get_facts]),
   (``BytesHook.substr, [``BytesHook.substr_facts]),
   (``StringHook.find, [``StringHook.find_facts]),
   (``IntHook.tdiv, [``IntHook.tdiv_facts, ``IntHook.tdiv_mul_facts, ``IntHook.tdiv_mul_divisor_facts]),
   (``IntHook.emod, [``IntHook.emod_facts]),
   (``IntHook.shr, [``IntHook.shr_facts])]

/-- The applications in `e` (without loose bound variables) of the functions `fns`. -/
private def appsOf (fns : Std.HashSet Name) (e : Expr) : MetaM (Array Expr) := do
  let acc ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun s => do
    if s.hasLooseBVars then return
    if let some f := s.getAppFn.constName? then
      if fns.contains f then acc.modify (·.push s)
  acc.get

/-- Add the facts a termination goal needs from its hypotheses (see the module comment): the
prelude's facts about hooks, and the registered (`@[k2l_fact]`) facts about generated functions,
for every matching hypothesis and every application of a total function. -/
elab "k2l_facts" : tactic => withMainContext do
  let reg ← factLemmasRegistered
  let mut facts : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let push (facts : Array Expr) (seen : Std.HashSet Expr) (p : Expr) : MetaM (Array Expr × Std.HashSet Expr) := do
    let t ← instantiateMVars (← inferType p)
    if seen.contains t then return (facts, seen) else return (facts.push p, seen.insert t)
  let mut types : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    types := types.push ty
    let some (eqTy, lhs, rhs) := ty.eq? | continue
    if eqTy.isConstOf ``Bool then
      facts := facts.push d.toExpr
    if rhs.isAppOf ``Option.none && lhs.isFVar then
      if let some v ← lhs.fvarId!.getValue? then
        facts := facts.push (← mkExpectedTypeHint d.toExpr (← mkEq v rhs))
    for (head, lemmas) in factLemmas do
      unless lhs.isAppOf head do continue
      for l in lemmas do
        try (facts, seen) ← push facts seen (← mkAppM l #[d.toExpr]) catch _ => pure ()
    for l in reg do
      unless l.byHyp && lhs.isAppOf l.fn do continue
      try (facts, seen) ← push facts seen (← mkAppM l.lemma #[d.toExpr]) catch _ => pure ()
  -- total functions: every application in the goal or a hypothesis (the registered lemmas
  -- about generated functions, and the prelude's about total hooks)
  let total := reg.filter (!·.byHyp) ++ totalHookLemmas
  if !total.isEmpty then
    let fns : Std.HashSet Name := total.foldl (fun s l => s.insert l.fn) {}
    for ty in types do
      for a in ← appsOf fns ty do
        let args := a.getAppArgs
        for l in total do
          unless a.isAppOf l.fn && args.size ≥ l.arity do continue
          try (facts, seen) ← push facts seen (← mkAppM l.lemma (args.extract (args.size - l.arity) args.size))
          catch _ => pure ()
  -- the length of a string literal, which `omega` does not compute: `length "…" = n` by `rfl`
  -- (in the goal, the hypotheses and the facts above, such as `find_facts`'s needle length)
  let factTypes ← facts.mapM fun p => do instantiateMVars (← inferType p)
  for ty in types ++ factTypes do
    for a in ← appsOf ({``StringHook.length} : Std.HashSet Name) ty do
      if let some (Expr.lit (Literal.strVal str)) := a.getAppArgs.back?.map (·.consumeMData) then
        let eq ← mkEq a (toExpr (str.length : Int))
        (facts, seen) ← push facts seen (← mkExpectedTypeHint (← mkEqRefl a) eq)
  liftMetaTactic fun g => do
    let mut g := g
    for p in facts do
      let (_, g') ← (← g.assert `k2l_fact (← inferType p) p).intro1P
      g := g'
    return [g]

/-- `k2l_ih h`: for a lemma `h : … → f … = r → P` (the lemma being proved, in its own proof by
well-founded recursion), add `P` for every hypothesis `f … = r` of the goal. -/
elab "k2l_ih " t:term : tactic => withMainContext do
  let f ← Lean.Elab.Tactic.elabTerm t none
  let mut facts : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).isEq do continue
    try facts := facts.push (← mkAppM' f #[d.toExpr]) catch _ => pure ()
  liftMetaTactic fun g => do
    let mut g := g
    for p in facts do
      let (_, g') ← (← g.assert `k2l_ih (← inferType p) p).intro1P
      g := g'
    return [g]

/-- Replace every reducible abbreviation of `Int` (a generated `SortInt`) by `Int` in the goal and
the hypotheses, a change up to definitional equality: `omega` reads relations at `Int` only. -/
elab "k2l_int_types" : tactic => liftMetaTactic fun g => g.withContext do
  let norm (e : Expr) : MetaM Expr := Meta.transform e (pre := fun x => do
    if let .const n [] := x then
      if n != ``Int then
        if let some (.defnInfo _) := (← getEnv).find? n then
          if (← whnfR x).isConstOf ``Int then return .done (mkConst ``Int)
    return .continue)
  let mut g := g
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let t' ← norm t
    if t' != t then g ← g.replaceLocalDeclDefEq d.fvarId t'
  let t ← instantiateMVars (← g.getType)
  let t' ← norm t
  if t' != t then g ← g.replaceTargetDefEq t'
  return [g]

/-- Split every conjunction among the hypotheses into its parts (`omega` does not use a conjunction
one of whose parts it cannot read). -/
elab "k2l_hyp_ands" : tactic => liftMetaTactic fun g => do
  let mut g := g
  let mut progress := true
  while progress do
    progress := false
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isAppOfArity ``And 2 then
        let gs ← g.cases d.fvarId
        let some sg := gs[0]? | throwError "k2l_hyp_ands: cases failed"
        g := sg.mvarId
        progress := true
        break
  return [g]

/-- Split the first `match` or `if` found in a hypothesis (for facts about a generated function,
proved by unfolding it in a hypothesis `f x = some r` and splitting its cascade). -/
elab "k2l_split_hyp" : tactic => liftMetaTactic fun g => do
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    if let some gs ← splitLocalDecl? g d.fvarId then return gs
  throwError "k2l_split_hyp: nothing to split"

/-- The hooks a termination goal or a fact about a generated function is stated with, unfolded
to `Int`, `Bool` and `List` operations `omega` reads. -/
macro "k2l_hook_simp" : tactic => `(tactic| (try simp only [IntHook.le, IntHook.lt, IntHook.ge,
  IntHook.gt, IntHook.eq, IntHook.ne, IntHook.add, IntHook.sub, IntHook.mul, BoolHook.not,
  BoolHook.and, BoolHook.or, BytesHook.length, decide_eq_true_eq, decide_eq_false_iff_not,
  Bool.not_eq_true', Bool.and_eq_true, Bool.or_eq_true, dite_eq_right_iff, ite_eq_right_iff,
  reduceCtorEq, imp_false, not_and, not_or, Bool.not_eq_true] at *))

/-- Prove a fact about a generated function from a hypothesis `f x = r` whose definitions are
unfolded: split every `match` and `if` of the hypotheses (the function's cascade), identify the
results, add the facts of the hooks and of the registered lemmas (and, with `using h`, of `h`,
the lemma being proved, at the recursive calls), unfold the given definitions (shapes,
constructors), then `omega`. -/
syntax "k2l_fn_facts" " [" ident,* "]" (" using " ident)? : tactic

/-- The first half of `k2l_fn_facts`: split the cascade, identify the results. -/
macro "k2l_fn_split" : tactic => `(tactic| (
  repeat' k2l_split_hyp
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at *)
  all_goals (try subst_vars)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at *)
  all_goals (try subst_vars)))

/-- Decompose the equations between constructor applications among the hypotheses (`ids`: the
constructors and their injectivity lemmas), and substitute. -/
syntax "k2l_fn_inj" " [" ident,* "]" : tactic

macro_rules
  | `(tactic| k2l_fn_inj [$ids,*]) => do
    -- not the shapes: those are unfolded with the facts, by `k2l_fn_close`
    let ids := ids.getElems.filter fun i =>
      !(i.getId.getString!.startsWith "shape" && i.getId.getPrefix.getString! == "Term")
    let simps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ids.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      (try simp only [reduceCtorEq, true_and, and_true, false_and, and_false, $simps,*] at *)
      all_goals (k2l_hyp_ands; (try subst_vars))))

/-- The second half of `k2l_fn_facts`: facts, unfoldings, `omega`. -/
syntax "k2l_fn_close" " [" ident,* "]" : tactic

macro_rules
  | `(tactic| k2l_fn_close [$ids,*]) => do
    let simps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ids.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      k2l_facts
      k2l_hook_simp
      (try simp only [ListHook.shape_concat, ListHook.shape_element, ListHook.shape_unit,
        shape_prod, shape_unit, reduceCtorEq, true_and, and_true, false_and, and_false, $simps,*] at *)
      all_goals (
        k2l_hyp_ands
        (try subst_vars)
        k2l_int_types
        (repeat' apply And.intro)
        all_goals (first | done | omega))))

macro_rules
  | `(tactic| k2l_fn_facts [$ids,*]) =>
    `(tactic| (k2l_fn_split; all_goals (first | done | k2l_fn_close [$ids,*])))
  | `(tactic| k2l_fn_facts [$ids,*] using $h:ident) =>
    -- the constructor equations decomposed first, so that the recursive calls' arguments are
    -- pieces of the parameters (the lemma's own measure must see them decrease)
    `(tactic| (k2l_fn_split; all_goals (first | done | (k2l_fn_inj [$ids,*]; k2l_ih @$h; k2l_fn_close [$ids,*]))))

/-- Close a `decreasing_by` goal whose measures are definitions by cases (`ms`, unfolded and split
first; a measure of a mutual group: a distance, then the function's rank), unfolding `us` in the
facts (shapes, constructors). -/
syntax "k2l_decreasing_m" " [" ident,* "]" " using" " [" ident,* "]" : tactic

macro_rules
  | `(tactic| k2l_decreasing_m [$ms,*] using [$us,*]) => do
    let measures : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ms.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    let simps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      us.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      simp_wf
      (try simp only [$measures,*])
      (repeat' split)
      all_goals (first | done | (
        (try subst_vars)
        k2l_facts
        k2l_hook_simp
        (try simp only [ListHook.shape_concat, ListHook.shape_element, ListHook.shape_unit,
          shape_prod, shape_unit, reduceCtorEq, true_and, and_true, false_and, and_false, $simps,*] at *)
        all_goals (
          k2l_hyp_ands
          (try subst_vars)
          k2l_int_types
          (try simp only [Prod.lex_def] at ⊢)
          (try simp only [true_and, and_true, Nat.lt_irrefl, false_or, or_false] at ⊢)
          first | done | omega)))))

/-- Close a `decreasing_by` goal of a generated function; the identifiers are rank functions of
the measure to unfold. -/
syntax "k2l_decreasing" (" [" ident,* "]")? (" using" " [" ident,* "]")? : tactic

macro_rules
  | `(tactic| k2l_decreasing) => `(tactic| k2l_decreasing [])
  | `(tactic| k2l_decreasing [$ids,*] using [$us,*]) => do
    let ranks : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ids.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    let simps : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      us.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      simp_wf
      first | done | (
      (try subst_vars)
      k2l_facts
      k2l_hook_simp
      (try simp only [ListHook.shape_concat, ListHook.shape_element, ListHook.shape_unit,
        shape_prod, shape_unit, reduceCtorEq, true_and, and_true, false_and, and_false, $simps,*] at *)
      (try simp only [Prod.lex_def] at ⊢)
      (try dsimp only [$ranks,*] at ⊢)
      (try simp only [true_and, and_true, Nat.lt_irrefl, false_or, or_false] at ⊢)
      first | done | omega)))
  | `(tactic| k2l_decreasing [$ids,*]) => do
    let ranks : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ids.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| (
      simp_wf
      first | done | (
      (try subst_vars)
      k2l_facts
      -- a failed guard's condition is extracted before the hooks are unfolded: unfolding a hook
      -- inside the condition of a `dite` leaves its `Decidable` instance stated for the folded
      -- condition, and on Lean v4.34.0 `dite_eq_right_iff` no longer rewrites such a `dite`
      (try simp only [dite_eq_right_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at *)
      (try simp only [IntHook.le, IntHook.lt, IntHook.ge, IntHook.gt, IntHook.eq, IntHook.ne,
        IntHook.add, IntHook.sub, IntHook.mul, BoolHook.not, BoolHook.and, BoolHook.or,
        BytesHook.length, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
        Bool.and_eq_true, Bool.or_eq_true, dite_eq_right_iff, ite_eq_right_iff, reduceCtorEq,
        imp_false] at *)
      (try simp only [Prod.lex_def] at ⊢)
      (try dsimp only [$ranks,*] at ⊢)
      (try simp only [true_and, and_true, Nat.lt_irrefl, false_or, or_false] at ⊢)
      -- last, the default simp set, which has the `sizeOf` equations of the generated
      -- constructors: a call on the payload of an injected list element needs
      -- `sizeOf (inj x) = n + sizeOf x` beside the list's fact (simp's step bound ends it)
      first | done | omega | ((try simp_all) <;> omega))))

end KPrelude

