/-
  `coreOKEx` admits CE-1's clause, kernel-checked: `f() => g(?Z:Int)` with `post := Z ∈ lp()`, beside
  `lp() => lp()` and `g(X:Int) => X` (in test/ExClauses.lean `g` is not declared, so that semantics is
  not well sorted). `coreOK` refuses the semantics (its clause binds `Z` by `\exists`) and `coreOKEx`
  accepts it; it reads confined sorts. With `f() => g(0)` in place of the clause, `coreOK` accepts it.
-/
import KcoreSpec.CoreOKEx
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.CoreOKExTest
open KCore GroundTerm
def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 2, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 3, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
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
def fC : Sym := nRegSyms + 4
def lpS : Sym := nRegSyms + 5
def gS : Sym := nRegSyms + 6
def clCf : Clause :=
  { vars := [Srt.int], pats := [], req := none, rhs := .app gS [.var 0], ens := none, exs := [0],
    post := .mem Srt.int (.var 0) (.app lpS []) }
def clLp : Clause := { vars := [], pats := [], req := none, rhs := .app lpS [], ens := none }
def fnCf : Fn := { label := fC, args := [], result := Srt.int, clauses := [clCf] }
def fnLp : Fn := { label := lpS, args := [], result := Srt.int, clauses := [clLp] }
def cCe : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp] }
def clG : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
def fnG : Fn := { label := gS, args := [Srt.int], result := Srt.int, clauses := [clG] }
def cCeG : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnCf, fnLp, fnG] }
def clPl : Clause := { vars := [], pats := [], req := none, rhs := .app gS [.dv Srt.int (.int 0)], ens := none }
def fnPl : Fn := { label := fC, args := [], result := Srt.int, clauses := [clPl] }
def cPl : Semantics :=
  { base with symNames := base.symNames ++ ["Lblf", "Lbllp", "Lblg"], fns := [fnPl, fnLp, fnG] }

theorem clCf_exs : clCf.exs ≠ [] := by decide

/-- **`coreOKEx` accepts CE-1's semantics.** -/
theorem cCeG_coreOKEx : cCeG.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

/-- `coreOK` does not: `clausesPlain` asks that no clause bind a variable by `\exists`. -/
theorem cCeG_clausesPlain : cCeG.clausesPlain = false := by decide +kernel

theorem cCeG_not_coreOK : cCeG.coreOK = false := by
  simp only [Semantics.coreOK, Semantics.sortedOK, cCeG_clausesPlain, Bool.and_false, Bool.false_and]

theorem cCeG_readsConfined : cCeG.readsConfined = true := by decide +kernel

/-- The same semantics with `f() => g(0)`: `coreOK` accepts it. -/
theorem cPl_coreOK : cPl.coreOK = true := by decide_cheap

/-- In test/ExClauses.lean's semantics, without `g`, the clause meets `clausesPlainEx` and is not
well sorted. -/
theorem cCe_clausesPlainEx : cCe.clausesPlainEx = true := by decide +kernel
theorem cCe_clauseSorted : cCe.clauseSorted fnCf (cCe.fns.map Fn.sig) clCf = false := by decide +kernel

end KCore.CoreOKExTest
