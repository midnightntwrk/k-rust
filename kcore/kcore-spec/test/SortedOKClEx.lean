/-
  What the value model reads of the clauses (`Semantics.sortedOKClEx`), against `sortedOKCl`.

  - The statements: `HypModelCore` holds `sortedOKClEx`; `sortedOKCl` gives it; where no clause has an
    existential variable the two are the same Bool, clause by clause and for the semantics.
  - `cH`, with the clause `h(K) => #Exists Z:Int. (Z #And {inj{Int,KItem}(Z) #Equals K})`
    (`vars = [K:KItem, Z:Int]`, `exs = [Z]`, `post := inj{Int,KItem}(Z) = K`): `sortedOKClEx` accepts
    it and `sortedOKCl` refuses it.
  - `cT`, the same function with the clause `h(K) => 0`: both accept it.
  - A clause with an existential variable that occurs in its pattern, and a clause without one
    whose right side's predicate is not `\top`: `clausePlainOpenEx` refuses both.

  Run from kcore-spec: `lake env lean test/SortedOKClEx.lean`.
-/
import KcoreSpec.OpenClauseConsistent
import KcoreSpec.ValueModelApp
import KcoreSpec.ModelFunctional
import KcoreSpec.ModelHasEx

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.SortedOKClExTest

open KCore Faithful Faithful.Model

/-! ## The statements -/

example (c : Semantics) (h : HypModelCore c) : c.sortedOKClEx = true := h.hyp.1
example (c : Semantics) (h : HypModelCore c) : c.sortedOKClEx = true := h.sound.1
example (c : Semantics) : HypFnModel c =
    (c.sortedOKClEx = true ∧ c.srReady = true ∧ NamesNumbered c ∧ FnDet c) := rfl
example (c : Semantics) : HypSoundModel c =
    (c.sortedOKClEx = true ∧ c.srReady = true ∧ NamesNumbered c ∧ genWf c = true ∧ patHooksApart c = true ∧
      collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧ OvlOK c) := rfl

example (c : Semantics) (cl : Clause) : c.clausePlainOpenEx cl =
    ((!cl.exs.isEmpty || cl.post.isTop) && c.clauseExOK cl &&
    (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false ||
      memHeld c (varOccsList cl.pats) cl.pre i)) := rfl
example (c : Semantics) : c.sortedOKClEx =
    (c.subsortsOK && c.fns.all (fun f => f.clauses.all fun cl =>
      c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpenEx cl) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain) := rfl

example (c : Semantics) : c.sortedOKCl = true → c.sortedOKClEx = true := Semantics.sortedOKClEx_of_sortedOKCl
example (c : Semantics) (cl : Clause) : cl.exs = [] → c.clausePlainOpenEx cl = c.clausePlainOpen cl :=
  Semantics.clausePlainOpenEx_eq_of_noExs
example (c : Semantics) : c.FnsNoExs → c.sortedOKClEx = c.sortedOKCl := Semantics.sortedOKClEx_eq_of_noExs
example (c : Semantics) : c.sortedOKCl = true → c.FnsNoExs := Semantics.fnsNoExs_of_sortedOKCl
example (c : Semantics) (cl : Clause) : c.clausePlainOpenEx cl = true →
    c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top) ∧
      (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false ||
      memHeld c (varOccsList cl.pats) cl.pre i) = true := Semantics.clausePlainOpenEx_parts

/-- The two bundles differ by `FnsNoExs` exactly: `sortedOKCl` is `sortedOKClEx` with no clause
holding an existential variable. -/
theorem sortedOKCl_iff (c : Semantics) : c.sortedOKCl = true ↔ c.sortedOKClEx = true ∧ c.FnsNoExs :=
  ⟨fun h => ⟨Semantics.sortedOKClEx_of_sortedOKCl h, Semantics.fnsNoExs_of_sortedOKCl h⟩,
    fun h => Semantics.sortedOKCl_of_ex_noExs h.1 h.2⟩

/-- What each clause is asked for the value model's function equations with existential variables,
from `HypModelCore`. -/
example {c : Semantics} (h : HypModelCore c) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top) := hypModelCore_clsFactsCe h

/-! The statements on the model's path without existential variables keep `FnsNoExs` as a premise. -/

example (c : Semantics) (h : HypModelCore c) (hs : FnSolves c) (hne : c.FnsNoExs) (hp : ClausePreDecided c)
    (hl : OpenLaws c) : stdI_T c (StepV c) ⊧ᴵP (Γ c ∪ Γstep c) := stdI_V_model_core h hs hne hp hl
example (c : Semantics) (h : HypModelCore c) (hs : FnSolves c) (hne : c.FnsNoExs) (hp : ClausePreDecided c) :
    SatFnsGoal c :=
  satFnsGoal_decided h hs hne hp
example := @consistent_ofCl
example := @vmModelCl

/-! ## Fixtures -/

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def base : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblh"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

def hS : Sym := nRegSyms + 4
def fnOf (cls : List Clause) : Fn := { label := hS, args := [Srt.kitem], result := Srt.int, clauses := cls }
def cOf (cls : List Clause) : Semantics := { base with fns := [fnOf cls] }

/-- `h(K) => #Exists Z:Int. (Z #And {inj{Int,KItem}(Z) #Equals K})`. -/
def clH : Clause :=
  { vars := [Srt.kitem, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := .equals Srt.kitem (.inj Srt.int Srt.kitem (.var 1)) (.var 0) }
/-- `h(K) => 0`. -/
def clT : Clause :=
  { vars := [Srt.kitem], pats := [.var 0], req := none, rhs := .dv Srt.int (.int 0), ens := none }
/-- `clH` with Z for its pattern: the existential variable occurs on the left. -/
def clLeft : Clause := { clH with vars := [Srt.kitem, Srt.kitem], pats := [.var 1] }
/-- `clH` with no variable bound by `\exists`: a right-side predicate that is not `\top`. -/
def clPost : Clause := { clH with exs := [] }

/-- A semantics with a clause that binds a variable by `\exists`: `sortedOKClEx` accepts it,
`sortedOKCl` does not, and the clause is the only difference (`clausePlainOpen`). -/
theorem cH_ex : (cOf [clH]).sortedOKClEx = true ∧ (cOf [clH]).sortedOKCl = false ∧
    (cOf [clH]).clausePlainOpen clH = false ∧ (cOf [clH]).clausePlainOpenEx clH = true ∧
    (cOf [clH]).clauseSortedOpen (fnOf [clH]) ((cOf [clH]).fns.map Fn.sig) clH = true := by decide +kernel

theorem cH_notNoExs : ¬ (cOf [clH]).FnsNoExs := fun h =>
  absurd (h (fnOf [clH]) (List.mem_singleton_self _) clH (List.mem_singleton_self _)) (by decide)

/-- Without existential variables the two agree. -/
theorem cT_same : (cOf [clT]).sortedOKClEx = true ∧ (cOf [clT]).sortedOKCl = true := by decide +kernel

/-- `clausePlainOpenEx` refuses an existential variable of the left side, and a right-side
predicate other than `\top` on a clause without existential variables. -/
theorem refused : (cOf [clLeft]).clausePlainOpenEx clLeft = false ∧ (cOf [clLeft]).sortedOKClEx = false ∧
    (cOf [clPost]).clausePlainOpenEx clPost = false ∧ (cOf [clPost]).sortedOKClEx = false := by decide +kernel

/-- info: 'KCore.Semantics.sortedOKClEx_eq_of_noExs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Semantics.sortedOKClEx_eq_of_noExs
/-- info: 'KCore.SortedOKClExTest.sortedOKCl_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortedOKCl_iff
/-- info: 'KCore.SortedOKClExTest.cH_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cH_ex
/-- info: 'KCore.consistent_ofCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.consistent_ofCl

end KCore.SortedOKClExTest
