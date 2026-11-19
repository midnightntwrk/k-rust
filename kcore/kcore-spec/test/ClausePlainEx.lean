/-
  `Semantics.clausePlainEx` (KcoreSpec/ClausePlainEx.lean) on hand-built clauses, by `decide`.
  Run from the package root: `lake env lean -j1 test/ClausePlainEx.lean`.

  The semantics `c` has the cell sorts only: Bool is confined (its values are the two literals),
  Int and KItem are not. `fT`, `gT` are applications of symbols the examples never evaluate.

  | Clause | `exs`, `post` | `fixedExs c.confined c.valued` | `clausePlainEx` |
  |---|---|---|---|
  | `clB` | `?B:Bool`, `⊤` | `[]` | true: B is confined |
  | `clOr` | `Z:Int`, `Z ∈ f(X) ∨ Z ∈ g(X)` | `[Z]` | true: each alternative fixes Z |
  | `clTwo` | `Z, W:Int`, `W ∈ g(Z) ∧ Z ∈ f(X)` | `[Z, W]` | true: Z in the first round, W in the second |
  | `clZ` | `?Z:Int`, `(Z *Int 2 ==Int X) = true` | `[]` | false: Z neither confined nor fixed |
  | `clOne` | `Z:Int`, `Z ∈ f(X) ∨ ⊤` | `[]` | false: one alternative does not fix Z |
  | `clInj` | `B:Bool, Z:KItem`, `Z ∈ inj(B)` | `[Z]` | true: B confined and not fixed, Z fixed by a term over B |
  | `clInj`, no sort admitted | | `fixedExs noS noS` is `[]` | (B is then not admitted in the term) |
  | `clInjI` | the same with `B:Int` | `[]` | false: B neither, and Z by a term over B |
  | `clBind` | `Z:Int`, `Z ∈ 3 ∨ ∃B:Int. (Z ∈ B ∧ B = 3)` | `[Z]` | true: the binder's sort Int is not confined but has a value (`c.valued`), and the body fixes B by `B = 3` |
  | `clBind`, no sort admitted by a value | | `fixedExs c.confined noS` is `[]` | (B is then not admitted in the term) |
  | `clBindFree` | `Z:Int`, `Z ∈ 3 ∨ ∃B:Int. Z ∈ B` | `[]` | false: the body does not fix B |
  | `clBindB` | `Z:Bool` (as a KItem), `Z ∈ inj(true) ∨ ∃B:Bool. Z ∈ inj(B)` | `[Z]` | true: the binder's sort is confined |
  | `clNone` | none, `⊤` | `[]` | true |
  | `clPost` | none, `X ∈ X` | `[]` | false: a predicate without an existential variable |
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ClausePlainExTest

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

def noS : Srt → Bool := fun _ => false
abbrev I := Srt.int
abbrev B := Srt.bool
abbrev K := Srt.kitem
def fT (t : Term) : Term := .app 900 [t]
def gT (t : Term) : Term := .app 901 [t]
def i3 : Term := .dv I (.int 3)

/-- A clause `f(X) => rhs` over the variables `vars`, X the variable 0. -/
def mk (vars : List Srt) (exs : List Nat) (rhs : Term) (post : Cond) : Clause :=
  { vars := vars, pats := [.var 0], req := none, rhs := rhs, ens := none, exs := exs, post := post }

theorem confined_sorts : c.confined B = true ∧ c.confined I = false ∧ c.confined K = false := by
  decide +kernel

/-! ### Confined -/

def clB : Clause := mk [B, B] [1] (.var 1) .top
theorem clB_ok : c.clausePlainEx clB = true ∧ clB.fixedExs c.confined c.valued = [] := by decide +kernel

/-! ### Fixed -/

def clOr : Clause := mk [I, I] [1] (.var 1) (.or (.mem I (.var 1) (fT (.var 0))) (.mem I (.var 1) (gT (.var 0))))
theorem clOr_ok : c.clausePlainEx clOr = true ∧ clOr.fixedExs c.confined c.valued = [1] := by decide +kernel

def clTwo : Clause := mk [I, I, I] [1, 2] (.var 2)
  (.and (.mem I (.var 2) (gT (.var 1))) (.mem I (.var 1) (fT (.var 0))))
theorem clTwo_ok : c.clausePlainEx clTwo = true ∧ clTwo.fixedExs c.confined c.valued = [1, 2] := by decide +kernel

/-! ### Neither -/

def clZ : Clause := mk [I, I] [1] (.var 1)
  (.equals B (.app 902 [.app 903 [.var 1, .dv I (.int 2)], .var 0]) (.dv B (.bool true)))
theorem clZ_no : c.clausePlainEx clZ = false ∧ clZ.fixedExs c.confined c.valued = [] := by decide +kernel

def clOne : Clause := mk [I, I] [1] (.var 1) (.or (.mem I (.var 1) (fT (.var 0))) .top)
theorem clOne_no : c.clausePlainEx clOne = false := by decide +kernel

/-! ### Fixed by a term over a confined existential variable -/

def clInj : Clause := mk [I, B, K] [1, 2] (.var 2) (.mem K (.var 2) (.inj B K (.var 1)))
theorem clInj_ok : c.clausePlainEx clInj = true ∧ clInj.fixedExs c.confined c.valued = [2] ∧
    clInj.fixedExs noS noS = [] := by decide +kernel

def clInjI : Clause := mk [I, I, K] [1, 2] (.var 2) (.mem K (.var 2) (.inj I K (.var 1)))
theorem clInjI_no : c.clausePlainEx clInjI = false ∧ clInjI.fixedExs c.confined c.valued = [] := by decide +kernel

/-! ### A binder in the predicate (the binder binds the variable 2) -/

def clBind : Clause := mk [I, I] [1] (.var 1)
  (.or (.mem I (.var 1) i3) (.ex I (.and (.mem I (.var 1) (.var 2)) (.equals I (.var 2) i3))))
theorem clBind_ok : c.valued I = true ∧ c.clausePlainEx clBind = true ∧
    clBind.fixedExs c.confined c.valued = [1] ∧ clBind.fixedExs c.confined noS = [] := by decide +kernel

def clBindFree : Clause := mk [I, I] [1] (.var 1)
  (.or (.mem I (.var 1) i3) (.ex I (.mem I (.var 1) (.var 2))))
theorem clBindFree_no : c.clausePlainEx clBindFree = false ∧ clBindFree.fixedExs c.confined c.valued = [] := by
  decide +kernel

def clBindB : Clause := mk [I, K] [1] (.var 1)
  (.or (.mem K (.var 1) (.inj B K (.dv B (.bool true)))) (.ex B (.mem K (.var 1) (.inj B K (.var 2)))))
theorem clBindB_ok : c.clausePlainEx clBindB = true ∧ clBindB.fixedExs c.confined c.valued = [1] := by
  decide +kernel

/-! ### No existential variable -/

def clNone : Clause := mk [I] [] (.var 0) .top
def clPost : Clause := mk [I] [] (.var 0) (.mem I (.var 0) (.var 0))
theorem clNone_ok : c.clausePlainEx clNone = true ∧ c.clausePlainEx clPost = false := by decide +kernel
example : c.clausePlainEx clNone = true := Semantics.clausePlainEx_of_nil rfl rfl

end ClausePlainExTest

end KCore

/-- info: 'KCore.ClausePlainExTest.clInj_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ClausePlainExTest.clInj_ok
/-- info: 'KCore.Semantics.clausePlainEx_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Semantics.clausePlainEx_nil_iff
