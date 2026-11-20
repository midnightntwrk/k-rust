/-
  KCore, outside the cone: the sentences of a text's function equations, aligned with the clauses
  of `c` when one sentence gives several clauses or a clause's sentence is not found by its key.

  `TiePair.fnTextOf` takes one sentence per clause key `(function name, priority)`, and skips a key
  that finds none, so every later position shifts. Two readings make that happen: one equation
  read as several clauses of one key (all its clauses take the first key's sentence, the others
  find none), and a clause whose priority no attribute of its sentence states (the key finds no
  sentence, or the wrong one).

  `fnTextMany c us pins` has one entry per clause key, in `clauseKeys c`'s order. `pins` holds
  pairs `(position, sentence index)`: a pinned position holds the sentence of `us` of that index
  (`AxiomDecl.index`), so several positions may hold one sentence; the pinned sentences are taken
  out of `us`, and every other position takes, as `fnTextFrom` does, the first remaining sentence
  of its key that no earlier position took, or `none` where there is none, without shifting the
  later positions.

  The list is a witness only: what it is worth is the `shapeB` of its sentences against
  `gammaPats c`, so any way of choosing the pins is sound. The Bools a tie decides by kernel:
  `pinsOK` (each pin names a clause position and an equation sentence of that clause's function,
  no position twice, and the positions of one sentence consecutive), `manyAllSomeB` (no position is
  `none`) and `manyLengthB` (one entry per item of `fnItems c`).

  - `fnTextMany_length`: one entry per clause key.
  - `fnTextMany_nil`: with no pin, the sentences are `fnTextOf c us`.
  - `fnTextMany_pin`: a pinned position holds the sentence of its pin.
  - `fnTextMany_filterMap_getElem?`, `fnTextMany_filterMap_length`: where no entry is `none`, the
    list of sentences has the same positions.
-/
import KcoreSpec.TiePairs

set_option autoImplicit false

namespace KCore

namespace TiePair

open Faithful KoreAML

/-- `fnTextFrom` with pins, from the position `j` on: a position that `pins` names holds the
sentence of `all` of the pinned index; every other position takes the first sentence of its key
among `us` that no earlier position took, or none. One entry per key. -/
def fnTextPinFrom (all : List AxiomDecl) (pins : List (Nat × Nat)) :
    Nat → List (String × Nat) → List AxiomDecl → List (Option AxiomDecl)
  | _, [], _ => []
  | j, k :: ks, us => match pins.lookup j with
    | some i => all.find? (·.index == i) :: fnTextPinFrom all pins (j + 1) ks us
    | none => match takeEqn k us with
      | some (ad, rest) => some ad :: fnTextPinFrom all pins (j + 1) ks rest
      | none => none :: fnTextPinFrom all pins (j + 1) ks us

/-- The sentences among `us` of the clauses of `c`, one entry per clause in `clauseKeys c`'s order:
the pinned positions hold their pinned sentences, which are taken out of `us` before the other
positions are matched by key (`fnTextPinFrom`). -/
def fnTextMany (c : Semantics) (us : List AxiomDecl) (pins : List (Nat × Nat)) :
    List (Option AxiomDecl) :=
  fnTextPinFrom us pins 0 (clauseKeys c) (us.filter fun ad => !pins.any (·.2 == ad.index))

/-- Each pin names a clause position and a sentence of `us` that is an equation with that clause's
function at the head of its left side and no `simplification`; no position is pinned twice; the
positions pinned to one sentence are consecutive. The priority is not compared: a reading may give
a clause a priority its sentence does not state. -/
def pinsOK (c : Semantics) (us : List AxiomDecl) (pins : List (Nat × Nat)) : Bool :=
  (pins.all fun p => match (clauseKeys c)[p.1]?, us.find? (·.index == p.2) with
    | some k, some ad => AttrsAgree.eqnHeadIs k.1 ad.ax.pattern &&
        !AttrsAgree.has ad.ax.attributes "simplification"
    | _, _ => false) &&
  (pins.map (·.1)).eraseDups.length == pins.length &&
  pins.all fun p => pins.all fun q =>
    !(p.2 == q.2 && p.1 < q.1) || (List.range (q.1 - p.1)).all fun d => pins.contains (p.1 + d, p.2)

/-- No position is `none`. -/
def manyAllSomeB (l : List (Option AxiomDecl)) : Bool := l.all Option.isSome

/-- One entry per item of `fnItems c`. -/
def manyLengthB (c : Semantics) (l : List (Option AxiomDecl)) : Bool :=
  l.length == (fnItems c).length

theorem fnTextPinFrom_length (all : List AxiomDecl) (pins : List (Nat × Nat)) :
    ∀ (j : Nat) (ks : List (String × Nat)) (us : List AxiomDecl),
      (fnTextPinFrom all pins j ks us).length = ks.length
  | _, [], _ => rfl
  | j, k :: ks, us => by
    unfold fnTextPinFrom
    split
    · simp only [List.length_cons, fnTextPinFrom_length all pins (j + 1) ks us]
    · split <;> simp only [List.length_cons, fnTextPinFrom_length]

/-- One entry per clause key. -/
theorem fnTextMany_length (c : Semantics) (us : List AxiomDecl) (pins : List (Nat × Nat)) :
    (fnTextMany c us pins).length = (clauseKeys c).length :=
  fnTextPinFrom_length _ _ _ _ _

theorem fnTextPinFrom_nil (all : List AxiomDecl) :
    ∀ (j : Nat) (ks : List (String × Nat)) (us : List AxiomDecl),
      (fnTextPinFrom all [] j ks us).filterMap id = fnTextFrom ks us
  | _, [], _ => rfl
  | j, k :: ks, us => by
    simp only [fnTextPinFrom, fnTextFrom, List.lookup_nil]
    cases takeEqn k us with
    | none => exact fnTextPinFrom_nil all (j + 1) ks us
    | some p => exact congrArg (p.1 :: ·) (fnTextPinFrom_nil all (j + 1) ks p.2)

/-- With no pin, the sentences are `fnTextOf`'s. -/
theorem fnTextMany_nil (c : Semantics) (us : List AxiomDecl) :
    (fnTextMany c us []).filterMap id = fnTextOf c us := by
  unfold fnTextMany fnTextOf
  have hf : (us.filter fun ad => !([] : List (Nat × Nat)).any (·.2 == ad.index)) = us := by
    exact List.filter_eq_self.mpr fun _ _ => rfl
  rw [hf]
  exact fnTextPinFrom_nil _ _ _ _

theorem fnTextPinFrom_pin (all : List AxiomDecl) (pins : List (Nat × Nat)) :
    ∀ (j : Nat) (ks : List (String × Nat)) (us : List AxiomDecl) (n i : Nat),
      n < ks.length → pins.lookup (j + n) = some i →
      (fnTextPinFrom all pins j ks us)[n]? = some (all.find? (·.index == i))
  | _, [], _, n, _, hn, _ => absurd hn (Nat.not_lt_zero n)
  | j, k :: ks, us, 0, i, _, hl => by
    unfold fnTextPinFrom
    rw [Nat.add_zero] at hl
    rw [hl]
    rfl
  | j, k :: ks, us, n + 1, i, hn, hl => by
    have hn' : n < ks.length := Nat.lt_of_succ_lt_succ hn
    have hl' : pins.lookup (j + 1 + n) = some i := by rw [Nat.add_assoc, Nat.add_comm 1 n]; exact hl
    unfold fnTextPinFrom
    split
    · exact fnTextPinFrom_pin all pins (j + 1) ks us n i hn' hl'
    · split
      · exact fnTextPinFrom_pin all pins (j + 1) ks _ n i hn' hl'
      · exact fnTextPinFrom_pin all pins (j + 1) ks us n i hn' hl'

/-- A pinned position holds the sentence of `us` of its pinned index. -/
theorem fnTextMany_pin (c : Semantics) (us : List AxiomDecl) (pins : List (Nat × Nat)) {j i : Nat}
    (hj : j < (clauseKeys c).length) (hl : pins.lookup j = some i) :
    (fnTextMany c us pins)[j]? = some (us.find? (·.index == i)) :=
  fnTextPinFrom_pin us pins 0 (clauseKeys c) _ j i hj (by rw [Nat.zero_add]; exact hl)

theorem fnTextMany_filterMap_getElem? :
    ∀ {l : List (Option AxiomDecl)}, manyAllSomeB l = true → ∀ (j : Nat), (l.filterMap id)[j]? = l[j]?.bind id
  | [], _, j => by simp only [List.filterMap_nil, List.getElem?_nil, Option.bind_none]
  | none :: _, h, _ => by simp only [manyAllSomeB, List.all_cons, Option.isSome_none, Bool.false_and] at h; cases h
  | some a :: l, h, j => by
    have hl : manyAllSomeB l = true := by
      simp only [manyAllSomeB, List.all_cons, Option.isSome_some, Bool.true_and] at h ⊢; exact h
    cases j with
    | zero => rfl
    | succ j =>
      exact fnTextMany_filterMap_getElem? hl j

/-- Where no entry is `none`, the list of sentences has one entry per position. -/
theorem fnTextMany_filterMap_length :
    ∀ {l : List (Option AxiomDecl)}, manyAllSomeB l = true → (l.filterMap id).length = l.length
  | [], _ => rfl
  | none :: _, h => by simp only [manyAllSomeB, List.all_cons, Option.isSome_none, Bool.false_and] at h; cases h
  | some a :: l, h => by
    have hl : manyAllSomeB l = true := by
      simp only [manyAllSomeB, List.all_cons, Option.isSome_some, Bool.true_and] at h ⊢; exact h
    show (a :: l.filterMap id).length = l.length + 1
    rw [List.length_cons, fnTextMany_filterMap_length hl]

end TiePair

end KCore
