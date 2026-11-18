/-
  A negated clause with a variable of a sort without a value that only the `ensures` holds, at
  `eval_den4_coreCl`. Run from the package root: `lake env lean test/OpenClauseFn.lean`.
  Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/opencl.kompile.kore` (`opencl.k`: Int, Bool, a sort
  S with the generators `a` and `c(Empty)`, Empty without a generator, the total predicate `isC`,
  the function `g(Int)` with `g(_) => 0 [owise]`), with `g`'s clauses written by hand (`c4`):
  - `clG0`, `g(0) => 1 ensures isC(c(Y:Empty))`: Y is of Empty, which no constructor has as its
    result, and neither the patterns nor the conditions hold it;
  - the text's `g(_) => 0 [owise]` (`clO`), of a larger priority, which negates `clG0`.
  `c4` is `coreOK` (`clauseSorted` asks of Y only that it occur in the clause), and `sortedOKCl`. No clause of `c4` has `needsWitness`, so `neg_of_coreCl`'s
  hypotheses on the conditions hold with nothing assumed. At `g(1)`, `clG0` fails (its pattern is
  `0`) and the `[owise]` clause decides `0`: in every model of `Γc c4`, `g(1)` denotes `0`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace OpenClauseFnTest

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the clauses name. -/
example : c.symName 389 = "Lblg" ∧ c.symName 390 = "LblisC" ∧ c.symName 387 = "Lblc" ∧
    c.sortName 33 = "Empty" := by
  decide +kernel

noncomputable def gText : List Clause := (c.fns.map (·.clauses)).getD 0 []

/-- `g(0) => 1 ensures isC(c(Y:Empty))` -/
def clG0 : Clause :=
  { vars := [33], pats := [.dv Srt.int (.int 0)], req := none, rhs := .dv Srt.int (.int 1),
    ens := some (.app 390 [.app 387 [.var 0]]) }

/-- `g` with the clauses `clG0` and the text's `[owise]` clause. -/
noncomputable def gF4 : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := clG0 :: gText }

/-- The text with `g`'s clauses `clG0` and the `[owise]` clause. -/
noncomputable abbrev c4 : Semantics := { c with fns := gF4 :: c.fns.drop 1 }

theorem hfn4 : c4.lookupFn 389 = some gF4 := by rfl

/-- The `[owise]` clause of `g`. -/
noncomputable def clO : Clause := gText.getD 0 { vars := [], pats := [], req := none, rhs := .var 0, ens := none }

theorem gF4_clauses : gF4.clauses = [clG0, clO] := by rfl

/-- `g` is the text's first function, with one clause, `g(_) => 0` at priority 200; `clG0` is of a
smaller priority and not `aside`. -/
theorem shapeO : (c.fns.map (·.label)).getD 0 0 = 389 ∧ gText.length = 1 ∧ clO.vars = [Srt.int] ∧
    clO.prio = 200 ∧ clG0.prio < clO.prio ∧ clG0.aside = false := by
  decide +kernel

theorem clO_pats : clO.pats = [.var 0] := by rfl
theorem clO_req : clO.req = none := by rfl
theorem clO_rhs : clO.rhs = .dv Srt.int (.int 0) := by rfl
theorem clO_ens : clO.ens = none := by rfl
theorem clO_pre : clO.pre = .top := by rfl

/-- Empty is the result of no constructor and not `valued`; `clG0`'s variable is outside its
patterns and conditions, so `rightValued` fails; `sortedOK` and `coreOK` hold at `c4`. -/
theorem shape : c4.ctorSigs.all (·.result != 33) = true ∧ c4.valued 33 = false ∧ clG0.leftVars = [] ∧
    c4.rightValued = false ∧ c4.sortedOK = true ∧ c4.coreOK = true := by
  decide_cheap

/-- What `eval_den4_coreCl` asks of `c4`, decided, and no clause of `c4` needs a witness. -/
theorem decided : c4.sortedOKCl = true ∧ c4.srReady = true ∧ c4.ovls = [] ∧
    c4.subsorts.all (fun p => p.1 != p.2) = true ∧ c4.faithCoreOK = true ∧ Faithful.patHooksApart c4 = true ∧
    (∀ fn ∈ c4.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c4 = false) := by
  decide_cheap

/-- `coreOK`'s conjuncts other than `sortedOK` hold at `c4`. -/
example : c4.faithCoreOK = true ∧ c4.hooksApart = true ∧ c4.predsApart = true ∧ c4.idsOK = true ∧
    c4.overloadsOK = true := by
  decide_cheap

instance ovl4 : OvlOK c4 := OvlOK.of_nil decided.2.2.1 decided.2.2.2.1

theorem one_int : c4.sortOf (.dv Srt.int (.int 1)) = some Srt.int := by decide +kernel

/-- **`g(1)` evaluates to `0`**: `clG0` fails (its pattern `0` does not denote `1`), and the
`[owise]` clause decides. -/
theorem eval4 : Eval c4 389 [.dv Srt.int (.int 1)] (some (.dv Srt.int (.int 0))) := by
  have hO : clO ∈ gF4.clauses := by rw [gF4_clauses]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrhs : clO.rhs = .dv Srt.int (.int 0) := clO_rhs
  refine Eval.clause (σ := [(0, .dv Srt.int (.int 1))]) hfn4 hO (fun i s hs => ?_) ?_
    (fun t ht => by rw [clO_req] at ht; cases ht) (Clause.holds_preTop clO_pre _) (fun cl' hcl' _ hlt => ?_)
    (by rfl) ?_ (fun t ht => by rw [clO_ens] at ht; cases ht) (Clause.holds_postTop (by rfl) _)
  · rw [shapeO.2.2.1] at hs
    cases i with
    | zero => cases hs; exact ⟨_, rfl, one_int⟩
    | succ i => simp at hs
  · rw [clO_pats]; exact .cons (.var rfl) .nil
  · rw [gF4_clauses] at hcl'
    rcases List.mem_cons.mp hcl' with rfl | hcl'
    · exact Fails.intro fun σ _ hpv => by
        cases hpv with
        | cons h _ => cases h
    · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _)
  · rw [hrhs]; exact .dv

/-- **`eval_den4_coreCl` at `c4`**: in every model of `Γc c4`, `g(1)` denotes `0`, nothing
assumed (no clause needs a witness). -/
example {M : Type} [Inhabited M] {I : ML.Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Faithful.Γc c4)
    (e : ML.Valuation M) (m : M) :
    (KoreAML.den (Faithful.symApp c4 389 (GroundTerm.koreList c4 [.dv Srt.int (.int 1)]))).interpret I e m ↔
      Faithful.Res c4 I e (some (.dv Srt.int (.int 0))) m :=
  Faithful.eval_den4_coreCl hI decided.1 decided.2.1 decided.2.2.2.2.1 decided.2.2.2.2.2.1
    (fun fn hfn cl hcl hw => absurd hw (by rw [decided.2.2.2.2.2.2 fn hfn cl hcl]; decide))
    (Faithful.preRead_of_allTop (Faithful.clauseOpenFacts_of_sortedOKCl (hpreTop := by decide +kernel) decided.1))
    eval4 hfn4 (by decide +kernel) e m

/-- info: 'KCore.Faithful.eval_den4_coreCl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Faithful.eval_den4_coreCl

end OpenClauseFnTest
