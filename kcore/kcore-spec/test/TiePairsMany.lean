/-
  `TiePair.fnTextMany` (KcoreSpec/TiePairsMany.lean) on the literals `defn` and `U` of two construct
  fixtures, one per kind of pin. Nothing here reads `Parse.parse` or `emit`. Run from the package
  root: `lake env lean -j1 test/TiePairsMany.lean`.

  `OrNest`, `f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore` (fixture e3-ml-eq-rhs-or-nest): the
  functions f, g, h, k of the text have 1, 1, 3 and 1 clauses, at the positions 0, 1, 2 to 4 and 5
  of `clauseKeys c`; h's three clauses are read from one equation, sentence 208, whose right side is a disjunction (one
  clause per alternative, then the clause where none applies), all of priority 50. By key alone
  (`fnTextOf`) the second and third keys of h find no sentence and every later position shifts
  (`fnTextOf_short`). With h's three positions pinned to 208 (`pins`), the pins are well formed
  (`pins_ok`), no position is `none` and there is one per item of Γ (`text_all`), the three positions
  hold 208 (`text_at2` … `text_at4`, from `TiePair.fnTextMany_pin`) and the next position holds k's
  sentence 241 (`text_at5`): nothing shifts.

  `OvlFn`, `f2-examples/e5-ovl-fn-fn.kompile.kore` (fixture e5-ovl-fn-fn): `negExp` has two clauses
  at positions 0 and 1; the one at 0 is read from the `symbol-overload` axiom 124, which states no
  priority, and has priority 0. With no pin, key `(negExp, 0)` finds no sentence: position 0 is
  `none` and the length is kept (`nil_at0`, `nil_length`), and by `TiePair.fnTextMany_nil` the
  sentences are `fnTextOf`'s, one fewer than Γ's items (`nil_short`). With position 0 pinned to 124,
  the pin is well formed, every position holds a sentence (`pins_ok`, `text_all`), position 0 holds
  124 and position 1, the clause of key `(negExp, 50)`, holds 245, not 124: the pinned sentence was
  taken out of the sentences matched by key (`text_at0`, `text_at1`).
-/
import KcoreSpec.TiePairsMany
import KcoreSpec.TieCmd

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TiePairsManyTest

open KCore ML Faithful KoreAML

#check @TiePair.fnTextMany_length
#check @TiePair.fnTextMany_nil
#check @TiePair.fnTextMany_pin
#check @TiePair.fnTextMany_filterMap_getElem?
#check @TiePair.fnTextMany_filterMap_length
#print axioms TiePair.fnTextMany_nil
#print axioms TiePair.fnTextMany_pin
#print axioms TiePair.fnTextMany_filterMap_getElem?

/-! ## e3-ml-eq-rhs-or-nest: one sentence at three positions -/

namespace OrNest

definition_of defn from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or-nest.kompile.kore" module "E3-ML-EQ-RHS-OR-NEST"

noncomputable abbrev c : Semantics := defn.sem

/-- h's three clauses, at positions 2, 3, 4, from sentence 208. -/
def pins : List (Nat × Nat) := [(2, 208), (3, 208), (4, 208)]

noncomputable def textO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all pins

theorem keys_length : (TiePair.clauseKeys c).length = 33 := by decide +kernel

/-- By key alone two positions find no sentence. -/
theorem fnTextOf_short : (TiePair.fnTextOf c U.all).length + 2 = (fnItems c).length := by decide +kernel

theorem pins_ok : TiePair.pinsOK c U.all pins = true := by decide +kernel

theorem text_all : TiePair.manyAllSomeB textO = true ∧ TiePair.manyLengthB c textO = true := by
  decide +kernel

theorem find208 : U.all.find? (·.index == 208) = some U.ax208 := by kernel_rfl

theorem text_at2 : textO[2]? = some (some U.ax208) := by
  rw [← find208]; exact TiePair.fnTextMany_pin c U.all pins (by rw [keys_length]; decide) rfl
theorem text_at3 : textO[3]? = some (some U.ax208) := by
  rw [← find208]; exact TiePair.fnTextMany_pin c U.all pins (by rw [keys_length]; decide) rfl
theorem text_at4 : textO[4]? = some (some U.ax208) := by
  rw [← find208]; exact TiePair.fnTextMany_pin c U.all pins (by rw [keys_length]; decide) rfl

/-- The position after the group holds k's sentence. -/
theorem text_at5 : textO[5]? = some (some U.ax241) := by kernel_rfl

/-- The sentences, one per item of Γ, at the same positions. -/
theorem text_sentences_at2 : (textO.filterMap id)[2]? = some U.ax208 := by
  rw [TiePair.fnTextMany_filterMap_getElem? text_all.1, text_at2]; rfl

end OrNest

/-! ## e5-ovl-fn-fn: a clause whose priority its sentence does not state -/

namespace OvlFn

definition_of defn from "f2-examples/e5-ovl-fn-fn.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn.kompile.kore" module "E5-OVL-FN-FN"

noncomputable abbrev c : Semantics := defn.sem

/-- No pin: position 0 is `none`, and nothing shifts. -/
theorem nil_at0 : (TiePair.fnTextMany c U.all [])[0]? = some none := by kernel_rfl
theorem nil_length : TiePair.manyLengthB c (TiePair.fnTextMany c U.all []) = true := by decide +kernel

/-- With no pin the sentences are `fnTextOf`'s, one fewer than Γ's items. -/
theorem nil_short : ((TiePair.fnTextMany c U.all []).filterMap id).length + 1 = (fnItems c).length := by
  rw [TiePair.fnTextMany_nil]; decide +kernel

/-- negExp's clause at position 0, from the overload axiom 124. -/
def pins : List (Nat × Nat) := [(0, 124)]

noncomputable def textO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all pins

theorem pins_ok : TiePair.pinsOK c U.all pins = true := by decide +kernel

theorem text_all : TiePair.manyAllSomeB textO = true ∧ TiePair.manyLengthB c textO = true := by
  decide +kernel

theorem find124 : U.all.find? (·.index == 124) = some U.ax124 := by kernel_rfl

theorem text_at0 : textO[0]? = some (some U.ax124) := by
  rw [← find124]; exact TiePair.fnTextMany_pin c U.all pins (by decide +kernel) rfl

/-- Key `(negExp, 50)` takes 245: 124 is no longer among the sentences matched by key. -/
theorem text_at1 : textO[1]? = some (some U.ax245) := by kernel_rfl

end OvlFn

end KCore.TiePairsManyTest
