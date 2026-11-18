/-
  kore.k's theory with its step's closure has a model at `HookParams.none`
  (`KK.consistent : Consistent (defn.sem.withHooks HookParams.none)`), by `consistent_of`.

  Its hypotheses at `c₀`: `coreOK` (`coreOK_withHooks_defn`); `FnDet` (`KK.fnDet`); `FnSolves`
  (`KK.fnSolves`) by `fnSolves_of_parts_lookup`, each function being the one `lookupFn` finds under
  its label, every clause without existential variables (`sortedOK`) and with the right side's
  predicate `\top` (one kernel decision), `PrioDecided` (`KK.prioDecided`) and `CoDefined`
  (`KK.coDefined`); `ClausePreDecided`, every clause's predicate being `\top`; and `OpenLaws`, the
  definition having no parameter symbol.
-/
import User.PrioDecided
import User.CoDefined

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-- Every clause of kore.k has the predicates `\top`, on its left side and on its right side. -/
theorem tops : (c₀.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop && cl.post.isTop) = true := by
  decide +kernel

/-- **Evaluation solves kore.k's equations at `HookParams.none`** (`FnSolves`). -/
theorem fnSolves : FnSolves c₀ :=
  fnSolves_of_parts_lookup (fun _ h => CoDef.lookup_self h) fnDet
    (fun fn hfn cl hcl => ⟨Semantics.fnsNoExs_of_sortedOK hsorted _ hfn _ hcl,
      Cond.eq_top_of_isTop (Bool.and_eq_true _ _ ▸ List.all_eq_true.mp (List.all_eq_true.mp tops fn hfn) cl hcl).2⟩)
    prioDecided coDefined

/-- Every clause's predicate `pre` has a truth value: it is `\top`. -/
theorem clausePreDecided : ClausePreDecided c₀ :=
  clausePreDecided_of_isTop (by
    refine List.all_eq_true.mpr fun f hf => List.all_eq_true.mpr fun cl hcl => ?_
    exact (Bool.and_eq_true _ _ ▸ List.all_eq_true.mp (List.all_eq_true.mp tops f hf) cl hcl).1)

/-- kore.k declares no parameter symbol, so no open generator has a law to meet. -/
theorem openLaws : OpenLaws c₀ := fun k hk => by rw [Prio.hparams] at hk; cases hk

/-- **kore.k's theory with its step's closure has a model at `HookParams.none`** (`Consistent`). -/
theorem consistent : Consistent (defn.sem.withHooks HookParams.none) :=
  consistent_of c₀ hcore fnDet fnSolves clausePreDecided openLaws

open Lean in
#eval show CoreM Unit from do
  for n in [``consistent, ``fnSolves] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KK
