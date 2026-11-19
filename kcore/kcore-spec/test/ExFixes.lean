/-
  `fixesBy`, `Cond.fixes` and `Clause.fixedExs` on cases, by `decide`, and `wellSortedAt_univ` at a
  clause without existential variables. Run from the package root: `lake env lean -j1 test/ExFixes.lean`.

  `Clause.fixedExs adm val cl` lists the existential variables of `cl` that its `post` equates with
  a term over admitted variables: the variables that are not existential, the ones fixed in an
  earlier round, and the other existential ones of a sort `adm` admits. Under `.ex s body` the
  bound variable is admitted where `adm s`, or where `val s` and the body fixes it. `noS` admits no
  sort, `allS` every sort, `isBool` Bool. The terms `gT`, `hT` are applications of symbols the
  examples never evaluate.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.ExFixesTest

open KCore

def noS : Srt → Bool := fun _ => false
def allS : Srt → Bool := fun _ => true
def isBool : Srt → Bool := fun s => s == Srt.bool
def gT (t : Term) : Term := .app 900 [t]
def hT (t : Term) : Term := .app 901 [t]
abbrev I := Srt.int
/-- A clause over the variables `vars`, the variable 0 not existential. -/
def mkc (vars : List Srt) (exs : List Nat) (post : Cond) : Clause :=
  { vars := vars, pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := exs, post := post }

/-! ### Without a binder and with no sort admitted (X = 0, Z = 1, W = 2) -/

-- fixed: Z = g(X), g(X) = Z, X = Z; Z = X ∨ Z ∈ g(X) (both alternatives asked)
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (.var 1) (gT (.var 0)))) = [1] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (gT (.var 0)) (.var 1))) = [1] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (.var 0) (.var 1))) = [1] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2]
    (.or (.equals I (.var 1) (.var 0)) (.mem I (.var 1) (gT (.var 0))))) = [1] := by decide
-- in a second round: W = g(Z) ∧ Z = X gives Z, then W
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2]
    (.and (.equals I (.var 2) (gT (.var 1))) (.equals I (.var 1) (.var 0)))) = [1, 2] := by decide
-- not fixed: Z = Z, Z = g(Z), each over the other, one alternative ⊤, Z = W
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (.var 1) (.var 1))) = [] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (.var 1) (gT (.var 1)))) = [] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2]
    (.and (.equals I (.var 2) (gT (.var 1))) (.equals I (.var 1) (gT (.var 2))))) = [] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.or (.equals I (.var 1) (.var 0)) .top)) = [] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2] (.equals I (.var 1) (.var 2))) = [] := by decide

/-! ### A term over an existential variable of an admitted sort (X = 0, B = 1 Bool, Z = 2) -/

def p5c : Clause := mkc [I, Srt.bool, I] [1, 2]
  (.and (.mem I (.var 2) (gT (.var 1))) (.mem I (.var 2) (hT (.var 1))))
def p3h : Clause := mkc [I, Srt.bool, I] [1, 2]
  (.or (.mem I (.var 2) (hT (.var 0))) (.mem I (.var 2) (gT (.var 1))))
example : Clause.fixedExs noS allS p5c = [] := by decide
example : Clause.fixedExs isBool noS p5c = [2] := by decide
example : Clause.fixedExs noS allS p3h = [] := by decide
example : Clause.fixedExs isBool noS p3h = [2] := by decide
/-- B of a sort not admitted: nothing. -/
example : Clause.fixedExs isBool noS (mkc [I, I, I] [1, 2]
    (.and (.mem I (.var 2) (gT (.var 1))) (.mem I (.var 2) (hT (.var 1))))) = [] := by decide
/-- An admitted sort does not make its own variable fixed by a term that holds it. -/
example : Clause.fixedExs isBool noS (mkc [I, Srt.bool] [1] (.equals Srt.bool (.var 1) (gT (.var 1)))) = [] := by decide
/-- Two variables of an admitted sort, each by a term over the other: both listed. -/
example : Clause.fixedExs isBool noS (mkc [I, Srt.bool, Srt.bool] [1, 2]
    (.and (.equals Srt.bool (.var 1) (gT (.var 2))) (.equals Srt.bool (.var 2) (gT (.var 1))))) = [1, 2] := by decide

/-! ### Under a binder (X = 0, Z = 1; the binders bind 2, 3) -/

def s1 : Cond := .or (.mem I (.var 1) (hT (.var 0)))
  (.ex I (.and (.mem I (.var 1) (.var 2)) (.equals I (.var 2) (gT (.var 0)))))
example : Clause.fixedExs noS allS (mkc [I, I] [1] s1) = [1] := by decide
/-- no sort has a value: the binder's variable is not admitted -/
example : Clause.fixedExs noS noS (mkc [I, I] [1] s1) = [] := by decide
/-- the bound variable is not read as a variable that is not existential -/
example : Clause.fixedExs noS allS (mkc [I, I] [1] (.ex I (.mem I (.var 1) (.var 2)))) = [] := by decide
/-- the bound variable fixed by a term over Z, Z by the bound variable: nothing -/
example : Clause.fixedExs noS allS (mkc [I, I] [1]
    (.ex I (.and (.mem I (.var 1) (.var 2)) (.equals I (.var 2) (gT (.var 1)))))) = [] := by decide
/-- two binders, the outer one fixed by a term over the inner one; the inner unfixed: nothing -/
example : Clause.fixedExs noS allS (mkc [I, I] [1]
    (.ex I (.ex I (.and (.mem I (.var 1) (.var 2))
      (.and (.equals I (.var 2) (gT (.var 3))) (.equals I (.var 3) (hT (.var 0)))))))) = [1] := by decide
example : Clause.fixedExs noS allS (mkc [I, I] [1]
    (.ex I (.ex I (.and (.mem I (.var 1) (.var 2)) (.equals I (.var 2) (gT (.var 3))))))) = [] := by decide
/-- a binder of an admitted sort, nothing fixing it -/
example : Clause.fixedExs isBool noS (mkc [I, I] [1] (.ex Srt.bool (.mem I (.var 1) (gT (.var 2))))) = [1] := by decide
example : Clause.fixedExs noS allS (mkc [I, I] [1] (.ex Srt.bool (.mem I (.var 1) (gT (.var 2))))) = [] := by decide
/-- the bound variable fixed in one alternative of its body only -/
example : Clause.fixedExs noS allS (mkc [I, I] [1]
    (.ex I (.and (.mem I (.var 1) (.var 2)) (.or (.equals I (.var 2) (gT (.var 0))) .top)))) = [] := by decide
/-- no arm for `\forall`, `\not`, `\implies` -/
example : Clause.fixedExs isBool allS (mkc [I, I] [1] (.all Srt.bool (.mem I (.var 1) (.var 0)))) = [] := by decide
example : Clause.fixedExs isBool allS (mkc [I, I] [1] (.not (.not (.mem I (.var 1) (.var 0))))) = [] := by decide
example : Clause.fixedExs isBool allS (mkc [I, I] [1] (.implies .top (.mem I (.var 1) (.var 0)))) = [] := by decide
/-- the bound variable fixed by a term over W = 2: W fixed in the first round, Z in the second;
W unfixed: nothing -/
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2]
    (.and (.ex I (.and (.mem I (.var 1) (.var 3)) (.equals I (.var 3) (gT (.var 2)))))
      (.equals I (.var 2) (.var 0)))) = [1, 2] := by decide
example : Clause.fixedExs noS allS (mkc [I, I, I] [1, 2]
    (.ex I (.and (.mem I (.var 1) (.var 3)) (.equals I (.var 3) (gT (.var 2)))))) = [] := by decide

/-- `Z ∈ true ∨ ∃B:S. (Z ∈ k(B) ∧ B = lp())`: with `val` true at S the binder's variable is fixed
by `B = lp()` and Z in both alternatives; with `val` false at S (S has no value) Z is not fixed. -/
def clV (S : Srt) : Clause :=
  { vars := [Srt.bool], pats := [], req := none, rhs := .var 0, ens := none, exs := [0],
    post := .or (.mem Srt.bool (.var 0) (.dv Srt.bool (.bool true)))
      (.ex S (.and (.mem Srt.bool (.var 0) (.app 900 [.var 1])) (.equals S (.var 1) (.app 901 [])))) }
example : Clause.fixedExs noS allS (clV 77) = [0] := by decide
example : Clause.fixedExs noS noS (clV 77) = [] := by decide

/-! ### Through an injection (X = 0, Z = 1, W = 2 of Int; K = 3 of KItem) -/

abbrev KI := Srt.kitem
def injT (t : Term) : Term := .inj I KI t
def mk4 (exs : List Nat) (post : Cond) : Clause := mkc [I, I, I, KI] exs post

-- inj(Z) = K and K = inj(Z): fixed; `\in` likewise
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (.var 1)) (.var 3))) = [1] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (.var 3) (injT (.var 1)))) = [1] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.mem KI (injT (.var 1)) (.var 3))) = [1] := by decide
-- inj(Z) = inj(X): fixed; inj(Z) = inj(Z), inj(Z) = inj(g(Z)), inj(Z) = inj(W): not
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (.var 1)) (injT (.var 0)))) = [1] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (.var 1)) (injT (.var 1)))) = [] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (.var 1)) (injT (gT (.var 1))))) = [] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (.var 1)) (injT (.var 2)))) = [] := by decide
-- two rounds through the arm: inj(W) = inj(g(Z)) ∧ inj(Z) = K
example : Clause.fixedExs noS allS (mk4 [1, 2] (.and (.equals KI (injT (.var 2)) (injT (gT (.var 1))))
    (.equals KI (injT (.var 1)) (.var 3)))) = [1, 2] := by decide
-- not read: a function of Z, an injection of an injection, an injection of g(Z), under `\not`
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (.app 902 [.var 1]) (.var 3))) = [] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (.inj KI KI (injT (.var 1))) (.var 3))) = [] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.equals KI (injT (gT (.var 1))) (.var 3))) = [] := by decide
example : Clause.fixedExs noS allS (mk4 [1, 2] (.not (.equals KI (injT (.var 1)) (.var 3)))) = [] := by decide
-- under a binder: ∃B:Int. (Z ∈ B ∧ inj(B) = K)
example : Clause.fixedExs noS allS (mk4 [1] (.ex I (.and (.mem I (.var 1) (.var 4))
    (.equals KI (injT (.var 4)) (.var 3))))) = [1] := by decide

/-! ### On a definition: the sorts `confined` admits and the sorts with a value -/

open GroundTerm
open KCore.Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- The `k` cell and the library, Int below KItem, no function. -/
def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }
/-- Int and Bool below KItem. -/
def base2 : Semantics := { base with lib := { sortsBelowKItem := [Srt.int, Srt.bool] } }

/-- `fl() => 3 #Or #Exists B:Int. (B #And {B #Equals 3})`: Z fixed under the binder of the
unconfined Int, which has a value; not where `val` admits no sort. -/
def clS : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .var 0, ens := none, exs := [0],
    post := .or (.mem Srt.int (.var 0) (.dv Srt.int (.int 3)))
      (.ex Srt.int (.and (.mem Srt.int (.var 0) (.var 1)) (.equals Srt.int (.var 1) (.dv Srt.int (.int 3))))) }
example : Clause.fixedExs base.confined base.valued clS = [0] ∧
    Clause.fixedExs base.confined noS clS = [] ∧ base.confined Srt.int = false := by decide +kernel

/-- `exs = [B:Bool, Z:KItem]`, `post := Z ∈ inj(B)`: Z fixed by a term over the confined B, which
nothing fixes; not where no sort is admitted. -/
def clC : Clause :=
  { vars := [Srt.bool, Srt.kitem], pats := [], req := none, rhs := .var 1, ens := some (.var 0), exs := [0, 1],
    post := .mem Srt.kitem (.var 1) (.inj Srt.bool Srt.kitem (.var 0)) }
example : Clause.fixedExs base2.confined base2.valued clC = [1] ∧
    Clause.fixedExs noS base2.valued clC = [] ∧
    base2.confined Srt.kitem = false ∧ base2.confined Srt.bool = true := by decide +kernel

/-- `h(K) => #Exists Z:Int. (Z #And {inj{Int,KItem}(Z) #Equals K})`: Z (of Int, not confined)
fixed through the injection. -/
def clH : Clause :=
  { vars := [Srt.kitem, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.kitem (.inj Srt.int Srt.kitem (.var 1)) (.var 0) }
example : Clause.fixedExs base2.confined base2.valued clH = [1] ∧
    base2.confined Srt.int = false := by decide +kernel

/-! ### `univ` and `wellSortedAt_univ` -/

/-- `univ` leaves out the existential variables. -/
example : clC.univ = [] := by decide
example : clH.univ = [0] := by decide

/-- A clause without existential variables: `univ` is every variable, and well sorted on it is well
sorted. -/
def clU : Clause := { vars := [I, Srt.bool], pats := [.var 0], req := none, rhs := .var 1, ens := none }
example : clU.univ = [0, 1] := by decide
theorem clU_wellSortedAt (c : Semantics) (σ : Subst) :
    c.WellSortedAt clU.vars clU.univ σ ↔ c.WellSorted clU.vars σ :=
  wellSortedAt_univ rfl

end KCore.ExFixesTest
