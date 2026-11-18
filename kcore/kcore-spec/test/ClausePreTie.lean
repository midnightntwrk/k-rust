/-
  A clause with a predicate in its premise, in a model: the clause lemmas (KcoreSpec/OpenClause.lean,
  OpenClauseEval.lean, OpenClauseDen.lean) and what they ask of the model for the predicate
  (`PreRead`, KcoreSpec/ClausePreRead.lean; given by `preRead_of`, KcoreSpec/ClausePreTie.lean), on
  CN-4 §4.9's semantics: `u(X:Int) => X ensures X >Int 0`, and `g(X:Int)` with the clauses `gCl1`
  (`pre := ⌈u(X)⌉`, `rhs := 1`, priority 50) and `gCl2` (`rhs := 0`, priority 200), which negates
  `gCl1`'s exclusion `∃X'. ((⊤ ∧ X0 ∈ X') ∧ ⌈u(X')⌉)`.

  `coreOK` does not accept this semantics (`clausesPlain` asks `pre = \top`), so the facts the
  lemmas read of the semantics and of the model are hypotheses here; what is decided of the two
  clauses is kernel-checked (`decide +kernel`).
  Run from the package root: `lake env lean -j1 test/ClausePreTie.lean`.
-/
import KcoreSpec.ClausePreTie
import KcoreSpec.ClausePreCore
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ClausePreTieTest

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)
open Faithful HoldsShape

def iT (i : Int) : Term := .dv Srt.int (.int i)
def iv (i : Int) : GroundTerm := .dv Srt.int (.int i)

def U : Sym := nRegSyms + 4
def G : Sym := nRegSyms + 5
def uX : Term := .app U [.var 0]
def uCl : Clause := ⟨[Srt.int], [.var 0], none, .var 0, some (.app intGt [.var 0, iT 0]), 50, false, [], .top, .top⟩
def uFn : Fn := ⟨U, [Srt.int], Srt.int, [uCl], false⟩
def pre1 : Cond := .ceil Srt.int uX
def gCl1 : Clause := ⟨[Srt.int], [.var 0], none, iT 1, none, 50, false, [], pre1, .top⟩
def gCl2 : Clause := ⟨[Srt.int], [.var 0], none, iT 0, none, 200, false, [], .top, .top⟩
def gFn : Fn := ⟨G, [Srt.int], Srt.int, [gCl1, gCl2], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lblu", "Lblg"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [uFn, gFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

/-- What is decided of `gCl1`: its predicate is not `\top`, is well sorted, holds no binder, and
its binders (none) are bounded; its patterns have `g`'s argument sorts; it has no `requires`, no
open condition variable, and needs no witness. -/
theorem gCl1_facts :
    gCl1.pre ≠ .top ∧ c.condOK gCl1.vars gCl1.pre = true ∧ hasBinder gCl1.pre = false ∧
    Cond.bound c gCl1.vars.length gCl1.pre = true ∧
    sortsOfTerms c.patCtxNF gCl1.vars gCl1.pats = some gFn.args ∧ gCl1.req = none ∧
    gCl1.openCondVars = [] ∧ gCl1.needsWitness c = false ∧
    (!gCl1.reqOpen || gCl1.reqClosed ||
      gCl1.openCondVars.all fun i => (gCl1.vars[i]?.map c.confined).getD false) = true := by
  refine ⟨fun h => Cond.noConfusion (show Cond.ceil Srt.int uX = Cond.top from h), ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩ <;>
    decide +kernel

section
variable {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M}

/-- **`PreRead` of `gCl1`** in an interpretation with the constructors' facts where the elements
of well-sorted terms lie in their sorts (`preRead_of`). -/
theorem preRead_gCl1 (F : NodeFacts c I) (hT : TermsInSort c I) : PreRead c I gCl1 :=
  preRead_of F (fun h => by rw [gCl1_facts.2.2.1] at h; cases h) hT gCl1_facts.2.1 gCl1_facts.2.2.2.1

/-- **`gCl1`'s exclusion is empty where it fails** (`exclEmptyCl_ofCl` at a clause whose predicate
is not `\top`), in a model of `Γc c` with the context `coreOK` gives a semantics. -/
example (hI : I ⊧ᴵP Γc c) (hnn : NamesNumbered c) (hg : genWf c = true) (hsc : SortCtx c) [OvlOK c]
    (hph : patHooksApart c = true) (hcso : collSortsOK c = true) (hcs : collsOK c = true)
    (hph' : patHeadsOK c = true)
    (hcv : c.readsConfined = true → ∀ s, c.confined s = true → ∀ x, InS I (c.sortName s) x →
      ∃ v, c.sortOf v = some s ∧ elemOf c I v = x)
    (F : NodeFacts c I) (hT : TermsInSort c I) : ExclEmptyCl c I gFn gCl1 :=
  exclEmptyCl_ofCl hI hnn hg hsc hph hcso hcs hph' hcv (L := c.fns.map Fn.sig) gCl1_facts.2.2.2.2.1 gCl1_facts.2.1
    (fun _ => ⟨preRead_gCl1 F hT, gCl1_facts.2.2.2.2.2.2.2.1⟩) (fun t ht => by rw [gCl1_facts.2.2.2.2.2.1] at ht; cases ht)
    gCl1_facts.2.2.2.2.2.2.2.2
    (fun h => by rw [gCl1_facts.2.2.2.2.2.2.1] at h; cases h)
    (fun h => by rw [gCl1_facts.2.2.2.2.2.2.2.1] at h; cases h)

end

/-- info: 'KCore.HoldsShape.preRead_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms preRead_of
/-- info: 'KCore.Faithful.exclEmptyCl_ofCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exclEmptyCl_ofCl
/-- info: 'KCore.Faithful.clause_den4Cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms clause_den4Cl
/-- info: 'KCore.Faithful.eval_den4ClPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eval_den4ClPre
/-- info: 'KCore.Faithful.fails_den4ClPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fails_den4ClPre
/-- info: 'KCore.Faithful.holds_den4ClPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms holds_den4ClPre
/-- info: 'KCore.condKore_congrCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms condKore_congrCanon
/-- info: 'KCore.condOK_congrVars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms condOK_congrVars

end ClausePreTieTest

end KCore
