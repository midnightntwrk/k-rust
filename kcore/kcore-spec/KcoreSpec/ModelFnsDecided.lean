/-
  KCore. The value model satisfies the functions' equations where each clause's predicate has a
  truth value wherever its patterns match (`ClausePreDecided`).

  `AtT.satFnsGoal_decided`: `satFnsGoalPre` under `HypModelCore`, whose `sortedOKCl` gives each
  clause's predicate well sorted, and `ClausePreDecided`. `clausePreDecided_of_fnHyp`: `FnHyp` gives
  the hypothesis.
-/
import KcoreSpec.ModelFnsPre
import KcoreSpec.ClausePreFn
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore

open ML Faithful

open Faithful.Model in
/-- **`ClausePreDecided` under `FnHyp`**, for a semantics that `coreOK` accepts: every function has
a result at arguments of its sorts (`FnHyp`'s first conjunct), so each clause's predicate has a
truth value at each σ well sorted on its patterns and conditions. -/
theorem clausePreDecided_of_fnHyp {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) : ClausePreDecided c :=
  clausePreDecided_of_terminates (hypSound_of_core h) hf.1

namespace Faithful

namespace Model

variable {c : Semantics}

/-- Each clause's predicate is well sorted over the clause's variables, under `HypModelCore`. -/
theorem HypModelCore.preOK (h : HypModelCore c) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.pre = true := fun fn hfn cl hcl =>
  Semantics.clauseSortedOpen_preOK ((Semantics.sortedOKCl_parts h.hyp.1).2.1 fn hfn cl hcl).1

/-- **The value model at any transition satisfies the functions' equations**, under `HypModelCore`
and `ClausePreDecided`: each clause's equation with its predicate in the premise
(`AtT.satFnsGoalPre`). -/
theorem AtT.satFnsGoal_decided {T : GroundTerm → GroundTerm → Prop} (h : HypModelCore c)
    (hp : ClausePreDecided c) : stdI_T c T ⊧ᴵP ΓFns c :=
  AtT.satFnsGoalPre h h.preOK fun fn hfn cl hcl σ ws hσ hpv _ => hp fn hfn cl hcl σ ws (hσ.at _) hpv

/-- `AtT.satFnsGoal_decided` in the value model. -/
theorem satFnsGoal_decided (h : HypModelCore c) (hp : ClausePreDecided c) : SatFnsGoal c :=
  AtT.satFnsGoal_decided (T := StepM c) h hp

end Model

end Faithful

end KCore
