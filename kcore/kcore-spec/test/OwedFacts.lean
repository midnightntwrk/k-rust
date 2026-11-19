/-
  The owed conditions rule by rule and clause by clause, and `FnFacts` (FnObligations.lean), at
  semantics that `coreOK` accepts, that are not `plain`, and that owe a `CondDecided`. Run from the
  package root: `lake env lean -j1 test/OwedFacts.lean`. Kernel-checked (`decide +kernel`).

  - `cR`: the reader's semantics for `f2-examples/symrule.kompile.kore` with the rule `ok2`
    (`a() => a() requires H ==Int 0`, H:Int, `needsWitness`), as in `test/OpenRulesCore.lean`.
    `owedRules` is `ok2`'s position; `openRules_of_owed` gives the rule side of `OpenDecided` from
    `ok2`'s witness H := 0. The text has no function, so `FnFacts.of_nil` holds, and
    `consistent_of_fnFacts` (and its `withHooks` form) gives the model with no owed condition read;
    `FnFacts.obligations` with the witness gives `FnObligations`, so `sound_fn` applies.
  - `cOW`: the reader's semantics for `f2-examples/opencl.kompile.kore` with `g`'s clause `clW`
    (`g(1) => 1 requires H ==Int 0`, H:Int, `needsWitness`) first, as in `test/OpenRulesCore.lean`.
    `owedClauses` is `[(0, 0)]`; `openClauses_of_owed` gives the clause side from `clW`'s witness.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OwedFacts

/-! ## Rules: `cR` -/

namespace R

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)
/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(b), V0)), cnt)`. -/
def cfg (cnt : Term) : Term :=
  .app 71 [.app 383 [.app 0 [.inj 32 1 (.app 386 []), .var 0]], cnt]

noncomputable def sK : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 1 0
noncomputable def sC : Srt := ((c.rules.map (·.vars)).getD 0 []).getD 2 0

/-- `a() => a() requires H ==Int 0` -/
noncomputable def ok2 : Rule :=
  { vars := [sK, sC, Srt.int], lhs := cfg (.var 1), req := some (.app intEq [.var 2, i 0]),
    rhs := cfg (.var 1), ens := none, prio := 50 }

/-- The text's semantics with `ok2`. -/
noncomputable abbrev cR : Semantics := { c with rules := c.rules ++ [ok2] }

/-- **`cR` has `coreOK`, is not `plain`, and owes `ok2`'s condition** (its position is the text's
rule count); it owes no clause; no function or parameter is named; `RightHeld` is decided. -/
theorem shapeR : cR.coreOK = true ∧ cR.plain = false ∧ c.rules.length = 1 ∧ cR.owedRules = [1] ∧
    cR.owedClauses = [] ∧ ok2.condVars = [2] ∧ cR.rightValued = true := by
  decide_cheap

/-- **`ok2` is `Witnessed`** at H := 0: `0 ==Int 0` evaluates to `true`. -/
theorem wit2 : ok2.Witnessed cR := by
  refine ⟨[(2, .dv Srt.int (.int 0))], fun j hj s hs => ?_, fun t ht => ?_, .top⟩
  · rw [shapeR.2.2.2.2.2.1] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.int = some s from hs)
    exact ⟨_, rfl, sortOf_int 0⟩
  · cases ht
    exact .hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- **`OpenDecided` at `cR` from the one owed rule** (`openRules_of_owed`, `openClauses_of_owed`). -/
theorem odR : OpenDecided cR :=
  ⟨openRules_of_owed (by
      rw [shapeR.2.2.2.1]
      intro j hj r hr
      cases List.mem_singleton.mp hj
      cases (show some ok2 = some r from (show (c.rules ++ [ok2])[1]? = some ok2 by
        rw [List.getElem?_append_right (Nat.le_of_eq shapeR.2.2.1), shapeR.2.2.1]; rfl).symm.trans hr)
      exact Or.inl wit2),
   openClauses_of_owed (by rw [shapeR.2.2.2.2.1]; intro p hp; cases hp)⟩

/-- The `withHooks` equations at `cR`. -/
example (H : HookParams) : (cR.withHooks H).owedRules = [1] ∧ (cR.withHooks H).owedClauses = [] :=
  ⟨(Semantics.owedRules_withHooks cR H).trans shapeR.2.2.2.1,
   (Semantics.owedClauses_withHooks cR H).trans shapeR.2.2.2.2.1⟩

theorem rhR : cR.RightHeld := Semantics.rightHeld_of_valued shapeR.2.2.2.2.2.2

/-- **`FnFacts` at `cR`**: no function and no open parameter. -/
theorem factsR : FnFacts cR [] [] :=
  FnFacts.of_nil (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **`FnDet`, `FnSolves` and the model at `cR`**, a text that owes a rule's condition, with no
owed condition read (`fnModel_of_fnFacts`, `consistent_of_fnFacts`). -/
example : FnDet cR ∧ FnSolves cR := fnModel_of_fnFacts shapeR.1 rhR factsR

theorem consR : Consistent cR := consistent_of_fnFacts shapeR.1 rhR factsR

/-- `consistent_of_fnFacts_withHooks` at `cR`. -/
example (H : HookParams) : Consistent (cR.withHooks H) :=
  consistent_of_fnFacts_withHooks (ord := []) (tp := []) shapeR.1 rhR H
    (FnFacts.of_nil
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; decide +kernel)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans (by decide +kernel))
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans (by decide +kernel))
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans (by decide +kernel))
      (show cR.params.all (fun k => !k.raw) = true by decide +kernel))

/-- **`FnFacts.obligations`**: with the owed rule decided, `FnObligations`, so soundness. -/
example : SoundC cR :=
  sound_fn cR [] [] shapeR.1 rhR ParamsTotal.nil (factsR.obligations odR)

/-- info: 'OwedFacts.R.consR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consR

end R

/-! ## Clauses: `cOW` -/

namespace C

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def i (n : Int) : Term := .dv Srt.int (.int n)

/-- `g`'s clauses in the text: `g(_) => 0 [owise]`. -/
noncomputable def gText : List Clause := (c.fns.map (·.clauses)).getD 0 []
/-- `g(1) => 1 requires H ==Int 0` -/
def clW : Clause := { vars := [Srt.int], pats := [i 1], req := some (.app intEq [.var 0, i 0]), rhs := i 1, ens := none }
noncomputable def gW : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clW :: gText }

noncomputable abbrev cOW : Semantics := { c with fns := gW :: c.fns.drop 1 }

/-- **`cOW` owes `clW`'s condition**, the first clause of the first function, and no rule's. -/
theorem shapeOW : cOW.owedClauses = [(0, 0)] ∧ cOW.owedRules = [] := by decide +kernel

/-- `clW` is `Witnessed` in `cOW` at H := 0. -/
theorem witOW : clW.Witnessed cOW := by
  refine Clause.witnessed_of_top rfl (σ := [(0, .dv Srt.int (.int 0))]) (fun j _ s hs => ?_) (fun t ht => ?_)
  · cases j with
    | zero => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 0⟩
    | succ j => cases (show (none : Option Srt) = some s from hs)
  · cases ht
    refine ⟨.hook (by decide +kernel) (by decide +kernel) (.cons .var (.cons .dv .nil))
      (fun vs hvs => by cases hvs; rfl) (fun h => by cases h), fun r hr => ?_⟩
    cases hr with
    | ctor h _ => exact absurd h (by decide +kernel)
    | hook h hhk hts hh hund =>
      cases hts with
      | cons h1 hs1 =>
        cases h1
        cases hs1 with
        | cons h2 hs2 =>
          cases h2
          cases hs2
          have h3 := hh _ rfl
          have h4 : cOW.hookRes intEq [.dv Srt.int (.int 0), .dv Srt.int (.int 0)] =
              some (some (.dv Srt.bool (.bool true))) := by rfl
          exact Option.some.inj (h3.symm.trans h4)
    | param h hhk hp _ _ => exact absurd hhk (by decide +kernel)
    | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
    | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
    | ovl _ ho _ => exact absurd ho (by decide +kernel)
    | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- **`OpenDecided` at `cOW` from the one owed clause** (`openClauses_of_owed`). -/
theorem odOW : OpenDecided cOW :=
  ⟨openRules_of_owed (by rw [shapeOW.2]; intro j hj; cases hj),
   openClauses_of_owed (by
      rw [shapeOW.1]
      intro p hp fn hfn cl hcl
      cases List.mem_singleton.mp hp
      cases (show some gW = some fn from (rfl : cOW.fns[0]? = some gW).symm.trans hfn)
      cases (show some clW = some cl from (rfl : gW.clauses[0]? = some clW).symm.trans hcl)
      exact Or.inl witOW)⟩

end C

end OwedFacts
