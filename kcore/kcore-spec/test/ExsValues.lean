/-
  `CE.exs_values` (KcoreSpec/ExsValues.lean): its decided hypotheses on hand-built clauses, by
  `decide`, and the two about `post`'s truth value at one of them.
  Run from the package root: `lake env lean -j1 test/ExsValues.lean`.

  The semantics `c` has the cell sorts only: Bool is confined, Int is not.

  | Clause | `exs`, `post` | `clauseExOK` | `Cond.bound` of `post` | `clausePlainEx` |
  |---|---|---|---|---|
  | `clB` | `?B:Bool`, `⊤` | true | true | true: B is confined |
  | `clFix` | `?Z:Int`, `Z ∈ 3` | true | true | true: `post` fixes Z |
  | `clLeft` | `?Z:Int` that is the pattern's variable, `Z ∈ 3` | false | true | true |
  | `clBind` | `?Z:Int`, `∃B:Int. Z ∈ 3` | true | false: the binder's sort is not confined | true |

  `fix_dec`: at `clFix` and the match X ↦ 0, an extension by a value exists and `post` has a truth
  value at every extension.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ExsValuesTest

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

abbrev I := Srt.int
abbrev B := Srt.bool
def i3 : Term := .dv I (.int 3)

/-- A clause `f(X) => rhs` over the variables `vars`, X the variable 0. -/
def mk (vars : List Srt) (exs : List Nat) (rhs : Term) (post : Cond) : Clause :=
  { vars := vars, pats := [.var 0], req := none, rhs := rhs, ens := none, exs := exs, post := post }

def clB : Clause := mk [B, B] [1] (.var 1) .top
def clFix : Clause := mk [I, I] [1] (.var 1) (.mem I (.var 1) i3)
def clLeft : Clause := mk [I] [0] (.var 0) (.mem I (.var 0) i3)
def clBind : Clause := mk [I, I] [1] (.var 1) (.ex I (.mem I (.var 1) i3))

theorem clB_ok : c.clauseExOK clB = true ∧ Cond.bound c clB.vars.length clB.post = true ∧
    c.clausePlainEx clB = true := by decide +kernel
theorem clFix_ok : c.clauseExOK clFix = true ∧ Cond.bound c clFix.vars.length clFix.post = true ∧
    c.clausePlainEx clFix = true ∧ c.confined I = false := by decide +kernel
theorem clLeft_no : c.clauseExOK clLeft = false ∧ Cond.bound c clLeft.vars.length clLeft.post = true ∧
    c.clausePlainEx clLeft = true := by decide +kernel
theorem clBind_no : c.clauseExOK clBind = true ∧ Cond.bound c clBind.vars.length clBind.post = false ∧
    c.clausePlainEx clBind = true := by decide +kernel

theorem clFix_free : clFix.exs.filter (!clFix.leftVars.contains ·) = [1] := by decide

/-- At the match X ↦ 0 an extension by a value exists, and `post` has a truth value at every
extension. -/
theorem fix_dec :
    (∃ σ', AgreeOff (clFix.exs.filter (!clFix.leftVars.contains ·)) [(0, .dv I (.int 0))] σ' ∧
      c.WellSorted clFix.vars σ') ∧
    ∀ σ', AgreeOff (clFix.exs.filter (!clFix.leftVars.contains ·)) [(0, .dv I (.int 0))] σ' →
      c.WellSorted clFix.vars σ' → ∃ b, Holds c clFix.vars.length σ' clFix.post b :=
  ⟨⟨[(0, .dv I (.int 0)), (1, .dv I (.int 0))], by
      rw [clFix_free]; intro i hi
      have h1 : (i == 1) = false := by simpa using hi
      simp [List.lookup, h1],
    by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩⟩,
   fun σ' _ _ => ⟨_, .mem (.var (i := 1)) .dv⟩⟩

example := @CE.exs_values

/-- info: 'KCore.CE.exs_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.exs_values

/-- info: 'KCore.CE.exs_values_hr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.exs_values_hr

/-- info: 'KCore.CE.fixes_value_hr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.CE.fixes_value_hr

/-- info: 'KCore.Faithful.holdsRead_den4ClPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.holdsRead_den4ClPre

/-- info: 'KCore.Faithful.instIs_den4ClPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.instIs_den4ClPre

/-- info: 'KCore.ExsValuesTest.fix_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ExsValuesTest.fix_dec

end ExsValuesTest

end KCore
