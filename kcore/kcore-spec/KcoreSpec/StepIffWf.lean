/-
  KCore, checked layer: the executable step is the step relation, for every well-formed definition.

  `step_iff` is `step_iff_of` (StepIff.lean) with two of its conditions on the core, `srReady` and
  `matchReady`, derived from `wf` (NamesApart.lean). Subject reduction (SubjectReduction.lean)
  likewise holds under `wf` alone (`rhs_sorted_wf`, `step_of_apply_wf`, `Eval.sorted_wf`), and
  so does the soundness of the listed successors (`successorsN_sound_wf`).
-/
import KcoreSpec.StepIff
import KcoreSpec.NamesApart

set_option autoImplicit false

namespace KCore.Exec

open KCore

/-- The executable step lists exactly the `Step` successors of a well-formed definition, for some
fuel, when it has no overloading symbol (the executable matcher reads none) and no clause
`aside` (`asideFree`). Coherence (`CoherentAll`) is needed for the `→` direction: `Eval` relates the result of every
clause that applies under every σ that applies, the executable evaluation takes one, and coherence
makes it the one derived. -/
theorem step_iff (d : Definition) (hwf : wf d = true) (hok : d.sem.ok = true) (hno : d.sem.ovls = [])
    (hco : CoherentAll d.sem) (x y : Config d.sem) (hna : d.sem.asideFree = true := by decide +kernel) :
    Step d.sem x y ↔ ∃ n, (successorsN d.sem n x.val).any (same · y.val) = true :=
  step_iff_of d hok (NamesApart.srReady_of_wf hwf) (NamesApart.matchReady_of_wf hwf hno) hco x y hna

/-- Every successor the executable step lists, at any fuel, is a step (under `wf` and `ok`, without
overloading symbols). -/
theorem successorsN_sound_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) (hno : d.sem.ovls = []) {n : Nat} {x : Config d.sem}
    {y : GroundTerm} (hy : y ∈ successorsN d.sem n x.val) :
    ∃ r ∈ d.sem.rules, ∃ σ, d.sem.WellSorted r.vars σ ∧ PatVal d.sem σ r.lhs x.val ∧
      (∀ t, r.req = some t → EvalTerm d.sem σ t (some (bool true))) ∧
      EvalTerm d.sem σ r.rhs (some y) ∧
      (∀ t, r.ens = some t → EvalTerm d.sem σ t (some (bool true))) ∧ d.sem.sortOf y = some topCellSort ∧
      (∀ r' ∈ d.sem.rules, r'.prio < r.prio → NotApplies d.sem r' x.val) :=
  successorsN_sound hok (NamesApart.srReady_of_wf hwf) (NamesApart.matchReady_of_wf hwf hno) hy

end KCore.Exec

namespace KCore

/-- Subject reduction under `wf` and `ok`: a rule's right-hand side evaluated under a well-sorted σ
is, when defined, a configuration. -/
theorem rhs_sorted_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) {r : Rule} (hr : r ∈ d.sem.rules)
    {σ : Subst} (hσ : d.sem.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm d.sem σ r.rhs (some v)) : d.sem.sortOf v = some topCellSort :=
  rhs_sorted hok (NamesApart.srReady_of_wf hwf) (NamesApart.ovlCase_of_wf hwf) hr hσ he

/-- No rule application is lost to sorts, under `wf` and `ok`. -/
theorem step_of_apply_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) {r : Rule} (hr : r ∈ d.sem.rules)
    {x : Config d.sem} {σ : Subst} (hσ : d.sem.WellSorted r.vars σ)
    (hm : PatVal d.sem σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm d.sem σ t (some (bool true)))
    {v : GroundTerm} (he : EvalTerm d.sem σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm d.sem σ t (some (bool true)))
    (hprio : ∀ r' ∈ d.sem.rules, r'.prio < r.prio → NotApplies d.sem r' x.val) :
    Step d.sem x ⟨v, rhs_sorted_wf hwf hok hr hσ he⟩ :=
  let ⟨_, hp, hq, _⟩ := Semantics.ok_rule hok hr
  Step.rule_top r hr σ hp hq hσ hm hreq he hens hprio

/-- A function at arguments of its argument sorts, when defined, has a value of its result sort,
under `wf` and `ok`. -/
theorem Eval.sorted_wf {d : Definition} (hwf : wf d = true) (hok : d.sem.ok = true) {f : Sym}
    {vs : List GroundTerm} {v : GroundTerm} (h : Eval d.sem f vs (some v)) {fn : Fn}
    (hfn : d.sem.lookupFn f = some fn) (hvs : d.sem.sortsOf vs = some fn.args) :
    d.sem.sortOf v = some fn.result :=
  Eval.sorted_of hok (NamesApart.srReady_of_wf hwf) (NamesApart.ovlCase_of_wf hwf) h hfn hvs

end KCore
