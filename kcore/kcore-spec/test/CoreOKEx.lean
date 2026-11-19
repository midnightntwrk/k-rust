/-
  `coreOKEx` admits a clause with an existential variable, kernel-checked: `f() => g(?Z:Int)` with `post := Z ∈ lp()`, beside
  `lp() => lp()` and `g(X:Int) => X` (in test/ExClauses.lean `g` is not declared, so that semantics is
  not well sorted). `coreOKEx` accepts the semantics, and so does `coreOK`, which is `coreOKEx`
  (`coreOK_iff_ex`): `Z` is fixed by the predicate `Z ∈ lp()`. It reads confined sorts. With
  `f() => g(0)` in place of the clause, `coreOK` accepts it as well.
  So in every model of `Γc` the clause has `ClauseExRead` (`clauseExRead_of_coreEx`) and every clause
  `ClauseOpenFactsQ`: the hypotheses of OpenClauseDenQ.lean's block hold of a clause with an
  existential variable.
  The value model's sortedness `sortedOKClEx`, which `HypModelCore` holds, accepts the semantics, and
  `sortedOKCl` does not: `consistent_ce` is stated over a sortedness this clause passes.
-/
import KcoreSpec.CoreOKEx
import KcoreSpec.CoreDecide
import KcoreSpec.ClauseExDenCEx
import KcoreSpec.ModelHasEx

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

/-- **`coreOKEx` accepts the semantics of `f() => g(?Z:Int)` with `post := Z ∈ lp()`.** -/
theorem cCeG_coreOKEx : cCeG.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap

/-- `clausesPlain` accepts the clause: its existential variable `Z` is fixed by the predicate. -/
theorem cCeG_clausesPlain : cCeG.clausesPlain = true := by decide +kernel

/-- So does `coreOK`: it is `coreOKEx`. -/
theorem cCeG_coreOK : cCeG.coreOK = true := Semantics.coreOK_iff_ex.mpr cCeG_coreOKEx

/-- `clausesPlain` and `clausesPlainEx` agree on the semantics, as `clausesPlain_iff_ex` says. -/
example : cCeG.clausesPlainEx = true := Semantics.clausesPlain_iff_ex.mp cCeG_clausesPlain

theorem cCeG_readsConfined : cCeG.readsConfined = true := by decide +kernel

/-- The same semantics with `f() => g(0)`: `coreOK` accepts it. -/
theorem cPl_coreOK : cPl.coreOK = true := by decide_cheap

/-- In test/ExClauses.lean's semantics, without `g`, the clause meets `clausesPlainEx` and is not
well sorted. -/
theorem cCe_clausesPlainEx : cCe.clausesPlainEx = true := by decide +kernel
theorem cCe_clauseSorted : cCe.clauseSorted fnCf (cCe.fns.map Fn.sig) clCf = false := by decide +kernel

theorem fnCf_mem : fnCf ∈ cCeG.allFns := List.mem_append_left _ (by simp [cCeG])

/-- **The reading of the clause `f() => g(?Z:Int)` holds in every model of `Γc`.** -/
theorem cCeG_clauseExRead {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hIc : I ⊧ᴵP Faithful.Γc cCeG) :
    Faithful.ClauseExRead cCeG I fnCf clCf :=
  Faithful.clauseExRead_of_coreEx cCeG_coreOKEx cCeG_readsConfined hIc fnCf fnCf_mem clCf (by simp [fnCf]) clCf_exs

theorem cCeG_factsQ : ∀ fn ∈ cCeG.allFns, ∀ cl ∈ fn.clauses,
    ∃ L, HeadsOK cCeG L ∧ Faithful.ClauseOpenFactsQ cCeG fn L cl :=
  Faithful.clauseOpenFactsQ_of_sortedOKEx (Semantics.coreOKEx_parts cCeG_coreOKEx).1

/-- **`HypModelCore`'s sortedness of the clauses, `sortedOKClEx`, accepts the semantics of
`f() => g(?Z:Int)` with `post := Z ∈ lp()`**; `sortedOKCl` refuses it. -/
theorem cCeG_sortedOKClEx : cCeG.sortedOKClEx = true ∧ cCeG.clausePlainOpenEx clCf = true ∧
    cCeG.sortedOKCl = false := by decide +kernel

example (hm : Faithful.Model.HypModelCore cCeG) : cCeG.sortedOKClEx = true := hm.hyp.1

example (hm : Faithful.Model.HypModelCore cCeG) (hp : ClausePreDecided cCeG)
    (hq : ClausePostDecided cCeG) (hl : OpenLaws cCeG) : Consistent cCeG :=
  Faithful.Model.consistent_ce cCeG hm hp hq hl

/-- info: 'KCore.CoreOKExTest.cCeG_sortedOKClEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cCeG_sortedOKClEx

end KCore.CoreOKExTest
