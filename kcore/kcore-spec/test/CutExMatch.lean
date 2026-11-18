/-
  A function-overloaded symbol or an open generator in the pattern of an `exMatch`, in hand-built
  semantics. No reader arm writes an `exMatch` whose pattern applies either symbol; a semantics
  holding one is refused by the conditions that refuse either symbol in any pattern:
  `ovlPatsOK` (through `overloadsOK`) and `condOK`'s context `patCtxNF` for the function-overloaded
  symbol, `patCtxAll` (hence `patCtxNF`, `condOK`, `ruleSorted`) for the open generator. Each
  refused rule has a control, the same rule with a pattern the deciders admit, so the refusal is the
  symbol's and not the scrutinee's, the bound or a binder's.
  The cut of such a pattern (`C[g(P̄)]` read as `∃V. C[V] ∧ V ∈ g(P̄)`, the membership in the
  `exMatch`'s body) leaves the binders under the symbol out of the pattern, and `Cond.bound` admits
  such a binder only at a confined sort: refused at the unconfined Gas, admitted at the confined A.
  Run from the package root: `lake env lean -j1 test/CutExMatch.lean`. Kernel-checked
  (`decide +kernel` on each decided condition; `coreOK` and `overloadsOK` are never decided whole).

  - `Ovl` (the signature of f2-examples/ovlfun.k, as test/OvlFun.lean's `Cap`): `capGas : Gas → Gas`
    overloads the total function `capN : N → N`, N < Gas. The rule `<k> run(G) => done(G) </k>`
    with `pre := ∃ G'. capGas(G') :=match G`.
  - `Open` (the signature of e2-open-mixed, as test/OpenGenSems.lean's `OpenMixed`):
    `and : A A → B` an open generator, A ::= x | y. The rule `<k> c(Z) => d(x) </k>` with
    `pre := ∃ X Y. and(X, Y) :=match Z`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.CutExMatch

open KCore

/-! ## A function-overloaded symbol in an `exMatch` pattern -/
namespace Ovl

def gasS : Srt := nRegSorts
def nS : Srt := nRegSorts + 1
def pgmS : Srt := nRegSorts + 2
def kl : Sym := nRegSyms + 5
def done : Sym := nRegSyms + 7
def inf : Sym := nRegSyms + 8
def run : Sym := nRegSyms + 9
def z : Sym := nRegSyms + 10
def capN : Sym := nRegSyms + 11
def capGas : Sym := nRegSyms + 12

/-- `<generatedTop>(<k>(kseq(inj{Pgm,KItem}(t), dotk)), C)`, C the variable 1. -/
def cfgX (t : Term) : Term :=
  .app topLabel [.app kl [.app kseq [.inj pgmS Srt.kitem t, .app dotk []]], .var 1]

/-- `capN : N → N`, total, `capN(z #as G0) = G0`. -/
def capNFn : Fn :=
  ⟨capN, [nS], nS, [{ vars := [nS], pats := [.as (.app z []) 0], req := none, rhs := .var 0, ens := none }], true⟩

/-- `<k> run(G) => done(G) </k>` with the predicate `pre`, G the variable 0 of Gas. -/
def ruleWith (pre : Cond) : Rule :=
  { vars := [gasS, Srt.counter], lhs := cfgX (.app run [.var 0]), req := none,
    rhs := cfgX (.app done [.var 0]), ens := none, prio := 50, pre := pre }

/-- `∃ G':Gas. capGas(G') :=match G`: the pattern applies the function-overloaded `capGas`. -/
def preOvl : Cond := .exMatch [gasS] gasS (.app capGas [.var 2]) (.var 0) .top
/-- Control: `∃ M:N. inj{N,Gas}(M) :=match G`. -/
def preInj : Cond := .exMatch [nS] gasS (.inj nS gasS (.var 2)) (.var 0) .top
/-- The cut of `preOvl`: `∃ G':Gas, V:Gas. V :=match G ∧ V ∈ capGas(G')`. -/
def preCut : Cond := .exMatch [gasS, gasS] gasS (.var 3) (.var 0) (.mem gasS (.var 3) (.app capGas [.var 2]))

def sem (r : Rule) : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool], ctors := [⟨kconfigValue, [Srt.k], Srt.kitem⟩] }
    sortNames := ["Gas", "N", "Pgm", "KCell", "KCellOpt"]
    symNames := ["LblisGas", "LblisN", "LblisPgm", "LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'",
      "LblnoKCell", "Lbldone", "Lblinf", "Lblrun", "Lblz", "LblcapN", "LblcapGas"]
    userSorts := [Srt.top, Srt.topFrag, gasS, nS, pgmS, pgmS + 1, pgmS + 2, Srt.counter, Srt.counterOpt]
    ctors :=
      [⟨topLabel, [pgmS + 1, Srt.counter], Srt.top⟩, ⟨topFragLabel, [pgmS + 2, Srt.counterOpt], Srt.topFrag⟩,
       ⟨kl, [Srt.k], pgmS + 1⟩, ⟨kl + 1, [], pgmS + 2⟩,
       ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩,
       ⟨done, [gasS], pgmS⟩, ⟨inf, [], gasS⟩, ⟨run, [gasS], pgmS⟩, ⟨z, [], nS⟩]
    fns := [capNFn]
    userSubsorts := [(nS, gasS), (pgmS + 1, pgmS + 2), (Srt.counter, Srt.counterOpt)]
    pgmSort := pgmS
    rules := [r]
    ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN]⟩] }

def cOvl : Semantics := sem (ruleWith preOvl)
def cInj : Semantics := sem (ruleWith preInj)
def cCut : Semantics := sem (ruleWith preCut)

/-- `capGas` is function-overloaded, and `ovlPatsOK` refuses it in the `exMatch` pattern; the
control and the cut apply it in no pattern. -/
theorem ovlPats :
    cOvl.fnOvlSyms = [capGas] ∧ cOvl.ovlPatsOK = false ∧ cInj.ovlPatsOK = true ∧ cCut.ovlPatsOK = true := by
  decide +kernel

/-- The pattern has its sort over `patCtxAll` (which holds the overloading symbols) and none over
`patCtxNF` (which leaves out the function-overloaded ones), so `condOK` refuses the predicate and
`ruleSorted` the rule; the control is sorted. -/
theorem sorted :
    sortOfTerm cOvl.patCtxAll [gasS, Srt.counter, gasS] (.app capGas [.var 2]) = some gasS ∧
    sortOfTerm cOvl.patCtxNF [gasS, Srt.counter, gasS] (.app capGas [.var 2]) = none ∧
    cOvl.condOK [gasS, Srt.counter] preOvl = false ∧
    cOvl.ruleSorted (ruleWith preOvl) = false ∧
    cInj.condOK [gasS, Srt.counter] preInj = true ∧ Cond.bound cInj 2 preInj = true ∧
    cInj.ruleSorted (ruleWith preInj) = true := by
  decide +kernel

/-- The cut: its pattern and its membership are sorted, but the binder G' is held by no
constructor of the pattern and Gas is not confined (its generator `capGas` overloads a function),
so `Cond.bound` refuses it, and with it `ruleSorted`. -/
theorem cut_bound :
    cCut.condOK [gasS, Srt.counter] preCut = true ∧ cCut.confined gasS = false ∧
    Cond.bound cCut 2 preCut = false ∧ cCut.ruleSorted (ruleWith preCut) = false := by
  decide +kernel

theorem sortedOK_ovl : cOvl.sortedOK = false := by decide +kernel

theorem overloadsOK_ovl : cOvl.overloadsOK = false := by
  have h := ovlPats.2.1
  simp [Semantics.overloadsOK, h]

theorem coreOK_ovl : cOvl.coreOK = false := by
  simp [Semantics.coreOK, sortedOK_ovl]

end Ovl

/-! ## An open generator in an `exMatch` pattern -/
namespace Open

def sA : Srt := nRegSorts + 2
def sB : Srt := nRegSorts + 3
def kS : Sym := nRegSyms + 4
def xS : Sym := nRegSyms + 6
def yS : Sym := nRegSyms + 7
def cS : Sym := nRegSyms + 8
def dS : Sym := nRegSyms + 9
def andS : Sym := nRegSyms + 10

def andP : ParamSig := { sig := ⟨andS, [sA, sA], sB⟩, raw := true }

/-- `<generatedTop>(<k>(kseq(t, dotk)), C)`, C the variable 1. -/
def cfgX (t : Term) : Term := .app topLabel [.app kS [.app kseq [t, .app dotk []]], .var 1]

/-- `<k> c(Z) => d(x) </k>` with the predicate `pre`, Z the variable 0 of B. -/
def ruleWith (pre : Cond) : Rule :=
  { vars := [sB, Srt.counter], lhs := cfgX (.app cS [.var 0]), req := none,
    rhs := cfgX (.app dS [.app xS []]), ens := none, prio := 50, pre := pre }

/-- `∃ X:A, Y:A. and(X, Y) :=match Z`: the pattern applies the open generator `and`. -/
def preOpen : Cond := .exMatch [sA, sA] sB (.app andS [.var 2, .var 3]) (.var 0) .top
/-- Control: `∃ W:B. W :=match Z`. -/
def preVar : Cond := .exMatch [sB] sB (.var 2) (.var 0) .top
/-- The cut of `preOpen`: `∃ X:A, Y:A, V:B. V :=match Z ∧ V ∈ and(X, Y)`. -/
def preCut : Cond := .exMatch [sA, sA, sB] sB (.var 4) (.var 0) (.mem sB (.var 4) (.app andS [.var 2, .var 3]))

def sem (r : Rule) : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "A", "B"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisA", "LblisB", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblx",
      "Lbly", "Lblc", "Lbld", "Lbland"]
    userSorts := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt, sA, sB]
    ctors :=
      [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
       ⟨kS, [Srt.k], nRegSorts⟩, ⟨kS + 1, [], nRegSorts + 1⟩,
       ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩,
       ⟨xS, [], sA⟩, ⟨yS, [], sA⟩, ⟨cS, [sB], Srt.kitem⟩, ⟨dS, [sA], Srt.kitem⟩]
    fns := []
    userSubsorts := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]
    pgmSort := Srt.k
    rules := [r]
    params := [andP] }

def cOpen : Semantics := sem (ruleWith preOpen)
def cVar : Semantics := sem (ruleWith preVar)
def cCut : Semantics := sem (ruleWith preCut)

/-- `patCtxAll` holds no open generator, so the pattern has no sort there nor over `patCtxNF`;
`condOK` refuses the predicate and `ruleSorted` the rule. `ovlPatsOK` does not refuse it: `and` is
no overloading symbol. The control is sorted. -/
theorem patCtx_refuses :
    (cOpen.patCtxAll.heads.all fun k => !cOpen.params.any fun p => p.raw && p.sig.name == k.name) = true ∧
    sortOfTerm cOpen.patCtxAll [sB, Srt.counter, sA, sA] (.app andS [.var 2, .var 3]) = none ∧
    sortOfTerm cOpen.patCtxNF [sB, Srt.counter, sA, sA] (.app andS [.var 2, .var 3]) = none ∧
    cOpen.condOK [sB, Srt.counter] preOpen = false ∧
    cOpen.ruleSorted (ruleWith preOpen) = false ∧ cOpen.ovlPatsOK = true ∧
    cVar.condOK [sB, Srt.counter] preVar = true ∧ Cond.bound cVar 2 preVar = true ∧
    cVar.ruleSorted (ruleWith preVar) = true := by
  decide +kernel

/-- The cut: the binders X and Y are held by no constructor of the pattern, and `Cond.bound`
admits them because A is confined; the rule is sorted. -/
theorem cut_bound :
    cCut.condOK [sB, Srt.counter] preCut = true ∧ cCut.confined sA = true ∧
    Cond.bound cCut 2 preCut = true ∧ cCut.ruleSorted (ruleWith preCut) = true := by
  decide +kernel

theorem sortedOK_open : cOpen.sortedOK = false := by decide +kernel

theorem coreOK_open : cOpen.coreOK = false := by
  simp [Semantics.coreOK, sortedOK_open]

end Open

#check @Ovl.ovlPats
#check @Ovl.sorted
#check @Ovl.cut_bound
#check @Ovl.overloadsOK_ovl
#check @Ovl.coreOK_ovl
#check @Open.patCtx_refuses
#check @Open.cut_bound
#check @Open.coreOK_open

/-- info: 'KCore.CutExMatch.Ovl.coreOK_ovl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ovl.coreOK_ovl
/-- info: 'KCore.CutExMatch.Open.coreOK_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Open.coreOK_open
/-- info: 'KCore.CutExMatch.Ovl.cut_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ovl.cut_bound

end KCore.CutExMatch
