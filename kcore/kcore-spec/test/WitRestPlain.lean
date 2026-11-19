/-
  The conjuncts `rulesPlain` and `paramsPlain` of `sortedOK`, for the parts where no witness was
  found in the no-model form (a semantics meeting every other condition of `coreOK` and `FnHyp`,
  failing the conjunct, whose `Γ` has no model). Run from the package root:
  `lake env lean -j1 test/WitRestPlain.lean`.

  Kernel-checked here, for each: a semantics meeting every other leaf condition of `coreOK` (the
  other conjuncts of `sortedOK`, `faithCoreOK`, `predsApart`, `idsOK`, `overloadsOK`)
  and `FnHyp`, with the conjunct false. So neither part is implied by the others.
  - `rulesPlain`: `Rules.c` has the one rule
    `<k> X </k> <generatedCounter> N </generatedCounter> => <k> X </k> <generatedCounter> N </generatedCounter>
    ensures Z ==Int 0`, whose variable `Z` the left side does not bind, the right-hand side does
    not hold and no condition of the left side reads.
  - `paramsPlain`, its branch for a parameter that is no open generator: `Laws.c` has the
    parameter `p : N N → N`, no open generator, with the associativity attribute.

  Argued, not kernel-checked: `Γ` of each has a model.
  - `rulesPlain`, for every semantics, not for `Rules.c` alone: `Γ`'s parts other than `ΓRules`
    read no rule (`ΓFallback` reads the clauses' `Fails`), and every condition of `coreOK` and
    `FnHyp` reads the rules under a `∀` over them, so the semantics without its rules meets `coreOK`
    and `FnHyp` (for `Rules.c`, kernel-checked: `c0_core`), and its theory has a model. `ΓRules`'
    axioms are `φ ∧ ⌈right⌉ → •right` (`prioRuleK`, `sRewrites`), and no other item of `Γ` applies
    the symbol `•`: reading `•` as relating every two elements meets each axiom (where `⌈right⌉`
    holds, `right` has an element, so `•right` is everything). So `Γ` has a model whatever the
    rules, and dropping `rulesPlain` cannot remove one. With the step's closure (`Γstep`) reading
    `•` as the union of the rules' instances (x to y where some rule's left side with its premise
    holds x and its right side y, at one valuation) meets both. The conjunct is asked for
    soundness and completeness (which variables of a rule the values decide), not for a model.
  - `paramsPlain`'s branch for a parameter that is no open generator (`!k.assoc && !k.idem`):
    the law sentences are written of open generators only (`lawItemsK`), and no other item of `Γ`
    reads the attribute (`Laws.cons_same`; `paramVal` reads a parameter's `impl`, `raw` and signature only), so `Γ` is that of the
    semantics without the attribute, which meets `coreOK` (`Laws.c0_core`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.Faithful.WitRestPlain

open ML
open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-! ## `rulesPlain`: a variable of the `ensures` that nothing binds or holds -/

namespace Rules

/-- `<k> X </k> <generatedCounter> N </generatedCounter> => (the same) ensures Z ==Int 0`. -/
def rule : Rule :=
  { vars := [Srt.k, Srt.int, Srt.int]
    lhs := .app topLabel [.app (nRegSyms + 2) [.var 0], .app counterLabel [.var 1]]
    req := none
    rhs := .app topLabel [.app (nRegSyms + 2) [.var 0], .app counterLabel [.var 1]]
    ens := some (.app intEq [.var 2, .dv Srt.int (.int 0)])
    prio := 50 }

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [rule] }

/-- The semantics without its rule. -/
def c0 : Semantics := { c with rules := [] }

/-- The rule's open variable is in no condition of its left side, so it needs no witness. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_plain (by decide +kernel) (fun _ h => absurd h List.not_mem_nil),
    openLaws_of_plain fun _ h => absurd h List.not_mem_nil⟩

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `rulesPlain` holds, and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true ∧
    c.rules.all c.ruleSorted = true ∧ c.clausesPlain = true ∧ c.paramsPlain = true ∧
    c.faithCoreOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_rulesPlain : c.rulesPlain = false := by decide +kernel

/-- `Z` is the rule's one open variable, outside the right-hand side's held variables and the
conditions of the left side. -/
theorem open_z : rule.opens = [2] ∧ (heldOccs c rule.rhs).contains 2 = false ∧ rule.condVars = [] := by
  decide +kernel

theorem c0_core : c0.coreOK = true := by decide_cheap

/-- The parts of `Γ` other than the rules' are `c0`'s: the signature, constructors, collections
and functions read no rule. -/
theorem sig_same : (sigItems c).map (·.pat) = (sigItems c0).map (·.pat) := rfl
theorem cons_same : (consItemsK c).map (·.pat) = (consItemsK c0).map (·.pat) := by decide +kernel
theorem fn_same : (fnItems c).map (·.pat) = (fnItems c0).map (·.pat) := by decide +kernel
theorem coll_same : c.allColls.flatMap (collAxioms c) = c0.allColls.flatMap (collAxioms c0) := by decide +kernel

end Rules

/-! ## `paramsPlain`: a law attribute on a parameter that is no open generator -/

namespace Laws

/-- The own sort `N` and its constant `n`. -/
def N : Srt := nRegSorts + 2
def nL : Sym := nRegSyms + 5
/-- The parameter `p : N N → N`, no open generator, with the associativity attribute. -/
def pL : Sym := nRegSyms + 6
def pP : ParamSig := { sig := ⟨pL, [N, N], N⟩, assoc := true }

def cellCtorsN : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "N"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisN", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbln", "Lblp"]
    userSorts := cellSorts ++ [N]
    ctors := cellCtorsN ++ [⟨nL, [], N⟩]
    fns := []
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := []
    params := [pP] }

/-- The semantics without the attribute. -/
def c0 : Semantics := { c with params := [{ pP with assoc := false }] }

theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `paramsPlain` holds, and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true ∧
    c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.clausesPlain = true ∧
    c.faithCoreOK = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_paramsPlain : c.paramsPlain = false := by decide +kernel

theorem c0_core : c0.coreOK = true := by decide_cheap

/-- No law sentence is written for `p`, and the constructors' items are `c0`'s. -/
theorem laws_nil : lawItemsK c = [] := by decide +kernel
theorem cons_same : (consItemsK c).map (·.pat) = (consItemsK c0).map (·.pat) := by decide +kernel

end Laws

end KCore.Faithful.WitRestPlain
