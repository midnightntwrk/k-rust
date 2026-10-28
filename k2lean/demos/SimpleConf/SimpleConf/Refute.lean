import SimpleConf.Views
import KSimple.Fuel
import KSimpleTest.Cases

/-! SIMPLE is not confluent, so the premises of `terminal_unique_of` are false together and that
theorem holds of no program (`k2lean/docs/design.md`, sections 3.6 and 8.1).

The witness is SIMPLE's own test `div-nondet` (`print(++ x / (++ x / x), "\n")`): its strict
operands have effects, and krust's search finds three final configurations
(`KSimpleTest.Cases`). Two runs to two of them are paths of
indices into `successorsF`, whose steps are steps of `Step` (`successorsF_sound`); terminality
is read off `successors`, which lists every step (`successors_iff`).
The paths are pinned, since the kernel's own search (`pathTo`) costs 40 s and 9.7 GB against
20 s and 3.7 GB; if the generator reorders successors, `#eval pathTo fuel expected1_0 depth init1`
finds them again. -/

namespace SimpleConf.Refute

open KPrelude KSimple KSimpleTest

/-- The `i`th element of a list. -/
def nth : List SortGeneratedTopCell → Nat → Option SortGeneratedTopCell
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

theorem mem_of_nth : ∀ {l : List SortGeneratedTopCell} {i x}, nth l i = some x → x ∈ l
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by cases h; exact List.mem_cons_self
  | _ :: ys, i + 1, _, h => List.mem_cons_of_mem _ (mem_of_nth (l := ys) (i := i) h)

/-- The configuration a path of successor indices leads to. -/
def follow (n : Nat) : SortGeneratedTopCell → List Nat → Option SortGeneratedTopCell
  | c, [] => some c
  | c, i :: p => match nth (successorsF n c) i with
    | some c' => follow n c' p
    | none => none

theorem star_of_follow (n : Nat) : ∀ (p : List Nat) {c c' : SortGeneratedTopCell},
    follow n c p = some c' → Star Step c c'
  | [], c, _, h => by cases h; exact .refl c
  | _ :: p, _, _, h => by
    unfold follow at h
    split at h
    · rename_i h₁; exact .step (successorsF_sound (mem_of_nth h₁)) (star_of_follow n p h)
    · cases h

/-- A path of at most `d` steps from `c` to `t`, depth first. -/
def pathTo (n : Nat) (t : SortGeneratedTopCell) : Nat → SortGeneratedTopCell → Option (List Nat)
  | 0, c => if c = t then some [] else none
  | d + 1, c => if c = t then some [] else
      (successorsF n c).zipIdx.findSome? fun (c', i) => (pathTo n t d c').map (i :: ·)

theorem terminal_of_nil {c : SortGeneratedTopCell} (h : successors c = []) : Terminal Step c :=
  fun _ hs => by have := successors_iff.mpr hs; rw [h] at this; cases this

/-- The fuel of the functions' twins, and the length bound of the search. -/
abbrev fuel : Nat := 64
abbrev depth : Nat := 60

/-- `init1` and `expected1_*` are `div-nondet`'s. -/
theorem init1_is : (cases.find? (·.name == "div-nondet")).map (·.init) = some init1 := by
  decide +kernel

/-- The two runs: they differ in the order of the division's strict operands (step 25). -/
def path0 : List Nat := List.replicate 24 0 ++ [1, 1] ++ List.replicate 29 0
def path1 : List Nat := List.replicate 55 0

set_option maxRecDepth 100000 in
theorem reach0 : follow fuel init1 path0 = some expected1_0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem reach1 : follow fuel init1 path1 = some expected1_1 := by decide +kernel

theorem final0 : successors expected1_0 = [] := by decide +kernel
theorem final1 : successors expected1_1 = [] := by decide +kernel
theorem differ : expected1_0 ≠ expected1_1 := by decide +kernel

/-- SIMPLE is not confluent: one configuration has two different terminal configurations. -/
theorem terminalUnique.refuted : ¬ ∀ {c n₁ n₂ : SortGeneratedTopCell}, Star Step c n₁ →
    Terminal Step n₁ → Star Step c n₂ → Terminal Step n₂ → n₁ = n₂ :=
  fun h => differ (h (star_of_follow _ _ reach0) (terminal_of_nil final0)
    (star_of_follow _ _ reach1) (terminal_of_nil final1))

/-- The premises of `terminal_unique_of`. -/
def Premises.statement : Prop := OpenJoins ∧ SameThreadJoins

/-- They are false together: `terminal_unique_of` would give the uniqueness refuted above. -/
theorem Premises.refuted : ¬ Premises.statement :=
  fun ⟨O, S⟩ => terminalUnique.refuted (terminal_unique_of O S)

#k2l_assert_axioms terminalUnique.refuted
#k2l_refuted Premises

end SimpleConf.Refute
