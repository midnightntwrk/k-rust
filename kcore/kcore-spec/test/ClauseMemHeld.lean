/-
  `Semantics.clausesPlain`'s conjunct on a clause's open condition variables (KcoreSpec/Tie.lean)
  at a variable held by a cut of the clause's premise predicate (`memHeld`).
  Run from the package root: `lake env lean -j1 test/ClauseMemHeld.lean`. Kernel-checked
  (`decide +kernel`).

  The semantics is the reader's for `f2-examples/ovlsub.kompile.kore` (`ovlsub.k`, as
  test/OvlHeldDefs.lean reads it: `capGas` overloads the constructor `capN`, N < Gas, Gas has the
  value `inf` outside N, and has no function), with the function `uncap : Gas -> Gas` of one clause
  added by hand: `uncap(V) = G` where `V ∈ capGas(G)`.
  - G is the clause's one open condition variable, of Gas, which is not confined (N has the
    constructor `s`). `capGas` is `ovlHeld` (its closure holds no function), so the cut holds G
    (`memHeld`); the conditions are not closed (V, a condition variable, is the pattern's), so the
    clause needs no witness. `clausesPlain` accepts the semantics; the conjunct without the
    `memHeld` disjunct refuses the clause.
  - With a function `fI : A -> Gas` among `capGas`'s overloads, `capGas` is `ovlHeld` at A := Bool
    (confined) and not at A := Int: there the cut does not hold G and `clausesPlain` refuses.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ClauseMemHeld

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def capN : Sym := 387
def capGas : Sym := 394
def gasS : Srt := 32

theorem names_ok : c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" ∧ c.sortName gasS = "Gas" ∧
    c.isCtor capN = true ∧ c.isOvl capGas = true ∧ c.fns = [] := by
  decide +kernel

/-- `uncap(V) = G` where `V ∈ capGas(G)`: V is the variable 0, the pattern; G the variable 1. -/
def clU : Clause :=
  { vars := [gasS, gasS], pats := [.var 0], req := none, rhs := .var 1, ens := none,
    pre := .mem gasS (.var 0) (.app capGas [.var 1]) }

def uncap : Sym := 5001
def fnU : Fn := { label := uncap, args := [gasS], result := gasS, clauses := [clU] }

/-- `c` with `uncap`. -/
noncomputable def cU : Semantics := { c with fns := c.fns ++ [fnU] }

/-- G is open, of a sort that is not confined, and held by the cut; the conditions are not closed
and the clause needs no witness. -/
theorem clU_held : clU.openCondVars = [1] ∧ clU.reqOpen = true ∧ clU.reqClosed = false ∧
    cU.confined gasS = false ∧ cU.ovlHeld capGas = true ∧ cU.holds capGas = true ∧
    memHeld cU (varOccsList clU.pats) clU.pre 1 = true ∧ clU.needsWitness cU = false := by
  decide +kernel

/-- **`clausesPlain` accepts the clause by its `memHeld` disjunct**: the conjunct without it is
false. -/
theorem clausesPlain_memHeld : cU.clausesPlain = true ∧ cU.clausesPlainEx = true ∧
    (!clU.reqOpen || clU.reqClosed ||
      clU.openCondVars.all fun i => (clU.vars[i]?.map cU.confined).getD false) = false := by
  decide +kernel

/-- A function `fI : A -> Gas` among `capGas`'s overloads, beside `uncap`. -/
def fI : Sym := 5000
noncomputable def cUF (A : Srt) : Semantics :=
  { c with ovls := [⟨⟨capGas, [gasS], gasS⟩, [capN, fI]⟩],
           fns := c.fns ++ [{ label := fI, args := [A], result := gasS, clauses := [] }, fnU] }

/-- **The function overload's argument sort decides**: at Bool (confined) `capGas` is `ovlHeld`,
the cut holds G and `clausesPlain` accepts; at Int (not confined) none of the three. -/
theorem clausesPlain_fnOvl : (cUF Srt.bool).ovlHeld capGas = true ∧
    memHeld (cUF Srt.bool) (varOccsList clU.pats) clU.pre 1 = true ∧ (cUF Srt.bool).clausesPlain = true ∧
    (cUF Srt.int).ovlHeld capGas = false ∧
    memHeld (cUF Srt.int) (varOccsList clU.pats) clU.pre 1 = false ∧ (cUF Srt.int).clausesPlain = false := by
  decide +kernel

/-- info: 'KCore.memHeld_clause_valuesCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.memHeld_clause_valuesCut
/-- info: 'KCore.heldBack_holdsCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.heldBack_holdsCl
/-- info: 'KCore.Faithful.exclEmptyCl_ofCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.exclEmptyCl_ofCl
/-- info: 'KCore.Faithful.neg_of_coreCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.neg_of_coreCl
/-- info: 'KCore.Faithful.neg_of_coreClEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.Faithful.neg_of_coreClEx

end ClauseMemHeld
