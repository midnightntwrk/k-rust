/-
  A clause with a variable of a sort without a value that only the `ensures` holds, at
  `stepDecided_of_coreCl`. Run from the package root: `lake env lean test/RightHeldStep.lean`.
  Kernel-checked (`decide +kernel`).

  The semantics is the reader's for `f2-examples/opencl.kompile.kore` (`opencl.k`: Int, Bool, a sort
  S with the generators `a` and `c(Empty)`, Empty without a generator, the total predicate `isC`,
  `f()` without an equation (a parameter of the semantics) and the function `g(Int)`
  (`g(_) => 0 [owise]`), the rule `<k> go => g(f()) </k>`), with `f` made a function whose clauses
  are written by hand (`c3`):
  - `clYE`, `f() => 0 ensures isC(c(Y:Empty))`: Y is of Empty, which no constructor has as its
    result, and neither the patterns nor the conditions hold it (`rightValued` fails);
  - `clOne`, `f() => 1`, at the same priority.
  `c3` is `coreOK` (`clauseSorted` asks of Y only that it occur in the clause), and `sortedOKCl`. Its functions terminate (`fnTerminates3`: `f()` is `1`), so every
  configuration of `c3` is `StepDecided` (`stepDecided_of_coreCl`), at the rule that reads `f`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace RightHeldStepTest

definition_of defn from "f2-examples/opencl.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the clauses name. -/
example : c.symName 391 = "Lblf" ∧ c.symName 390 = "LblisC" ∧ c.symName 387 = "Lblc" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-- `f() => 0 ensures isC(c(Y:Empty))` -/
def clYE : Clause :=
  { vars := [33], pats := [], req := none, rhs := .dv Srt.int (.int 0),
    ens := some (.app 390 [.app 387 [.var 0]]) }
/-- `f() => 1` -/
def clOne : Clause := { vars := [], pats := [], req := none, rhs := .dv Srt.int (.int 1), ens := none }

/-- `f` with the clauses `clYE` and `clOne`. -/
def fF : Fn := { label := 391, args := [], result := Srt.int, clauses := [clYE, clOne] }

/-- In the text `f` is a parameter. -/
example : c.params.map (·.sig.name) = [391] ∧ c.fns.map (·.label) = [389, 390] := by decide +kernel

/-- `c` with `f` a function of the clauses `clYE` and `clOne`. -/
noncomputable def c3 : Semantics := { c with fns := c.fns ++ [fF], params := c.params.filter (·.sig.name != 391) }

/-- `c3` has one rule (`go => g(f())`), and `f` is no parameter of it. -/
example : c3.rules.length = 1 ∧ c3.isParam 391 = false := by decide +kernel

/-- Empty is the result of no constructor and not `valued`; `clYE`'s variable is outside its
patterns and conditions, so `rightValued` fails; `sortedOK` and `coreOK` hold at `c3`. -/
theorem shape : c3.ctorSigs.all (·.result != 33) = true ∧ c3.valued 33 = false ∧ clYE.leftVars = [] ∧
    c3.rightValued = false ∧ c3.sortedOK = true ∧ c3.coreOK = true := by
  decide_cheap

/-- What `stepDecided_of_coreCl` asks of `c3`, decided. -/
theorem decided : c3.sortedOKCl = true ∧ c3.srReady = true ∧ c3.ovls = [] ∧
    c3.subsorts.all (fun p => p.1 != p.2) = true := by
  decide +kernel

/-- `coreOK`'s conjuncts other than `sortedOK` hold at `c3`. -/
example : c3.faithCoreOK = true ∧ c3.hooksApart = true ∧ c3.predsApart = true ∧ c3.idsOK = true ∧
    c3.overloadsOK = true := by
  decide_cheap

theorem ovl3 : OvlOK c3 := OvlOK.of_nil decided.2.2.1 decided.2.2.2

/-- `c3`'s rules bind their variables in their left sides. -/
theorem rulesBind3 : ∀ r ∈ c3.rules, binds r.vars.length (varOccs r.lhs) = true := by
  decide +kernel

/-- Each function of `c3` is the one `lookupFn` finds under its label. -/
theorem lookup3 {fn : Fn} (hfn : fn ∈ c3.fns) : c3.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl decided.1 decided.2.1 (OvlOK.ovlCase ovl3)).nodupFns (List.mem_append_left _ hfn)

/-- The text's functions (`g`, `isC`): each clause's patterns bind its variables, it has no
`requires` and no `ensures`, and its right side is a literal. -/
theorem textFns : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true ∧
    cl.req = none ∧ cl.ens = none ∧ (match cl.rhs with | .dv _ _ => true | _ => false) = true := by
  decide +kernel

theorem sortsOf_nil3 {vs : List GroundTerm} (h : c3.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- **The functions of `c3` terminate**: `g` and `isC` by `eval_result` (each clause applies or
fails); `f()` is `1` by `clOne`, `clYE` being of the same priority. -/
theorem fnTerminates3 : FnTerminates c3 := by
  intro fn hfn vs hvs
  rcases List.mem_append.mp (show fn ∈ c.fns ++ [fF] from hfn) with hfn' | hfn'
  · refine eval_result (lookup3 hfn)
      (Semantics.sortedOK_plainCl_of_noExs shape.2.2.2.2.1 (Semantics.fnsNoExs_of_all (by decide +kernel)) fn (List.mem_append_left _ hfn))
      (fun cl hcl => (textFns fn hfn' cl hcl).1)
      (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(textFns fn hfn' cl hcl).2.1] at ht; cases ht), true,
        Clause.holds_preTop
          (Semantics.allFns_preTop (by decide +kernel : c3.clausesPreTop = true) fn (List.mem_append_left _ hfn) cl hcl) σ⟩)
      (fun cl hcl _ _ => ?_)
      (fun cl hcl _ _ t ht => by rw [(textFns fn hfn' cl hcl).2.2.1] at ht; cases ht)
    have h4 := (textFns fn hfn' cl hcl).2.2.2
    cases hr : cl.rhs with
    | dv s l => exact ⟨_, .dv⟩
    | _ => rw [hr] at h4; cases h4
  · rw [List.mem_singleton] at hfn'
    subst hfn'
    rw [sortsOf_nil3 hvs]
    exact ⟨_, Eval.clause (cl := clOne) (σ := []) (lookup3 hfn) (List.Mem.tail _ (List.Mem.head _))
      (fun i s h => by simp [clOne] at h) .nil (fun t h => by cases h) .top
      (fun cl' h _ hlt => by
        simp only [fF, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [clYE, clOne] at hlt)
      rfl .dv (fun t h => by cases h) .top⟩

/-- **`stepDecided_of_coreCl` at `c3`**: every configuration of `c3` is `StepDecided`. -/
example (x : GroundTerm) : StepDecided c3 x :=
  Faithful.stepDecided_of_coreCl decided.1 rulesBind3 (Semantics.rulesTop_of_isTop (by decide +kernel)) decided.2.1 ovl3 fnTerminates3 x

/-- **`stepDecided_of_fnHypCl` at `c3`.** -/
example (hf : FnHyp c3) (x : Config c3) : StepDecided c3 x.val :=
  stepDecided_of_fnHypCl decided.1 rulesBind3 (Semantics.rulesTop_of_isTop (by decide +kernel)) decided.2.1 (OvlOK.of_nil decided.2.2.1 decided.2.2.2) hf x

/-- `sortedOKCl_of_sortedOK_noExs` at the text's semantics. -/
example : c.sortedOKCl = true :=
  Semantics.sortedOKCl_of_sortedOK_noExs (Semantics.coreOK_parts (by decide_cheap)).1 (Semantics.fnsNoExs_of_all (by decide +kernel))

end RightHeldStepTest
