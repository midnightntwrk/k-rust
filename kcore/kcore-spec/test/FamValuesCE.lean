/-
  `famEx_values`'s and `famOpen_values`'s statements with `coreOKEx` for `coreOK`
  (`famEx_values_ce`, `famOpen_values_ce`), and the forms over the per-rule facts they are
  instances of. `coreOK` gives `coreOKEx`, so each gives the statement over `coreOK` with no other
  hypothesis.
-/
import KcoreSpec.FamValuesCE

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KCore.FamValuesCETest
open KCore ML Faithful Faithful.Model

/-! ## The statements -/

example : ∀ (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)),
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y := @famEx_values_ce

example : ∀ (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys),
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) := @famOpen_values_ce

example (c : Semantics) {H : Sym → Bool} (h : c.coreOKEx = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)) :
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y :=
  famEx_values_heldCEx c h hf hrules hbk x y r σ hs hy

example (c : Semantics) (h : c.coreOKEx = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (hs : c.ruleSorted r = true) (σ : Subst)
    (hu : Unblocked c r σ x.val) (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys) :
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) :=
  famOpen_values_ppCEx c h hf x r hr hs σ hu hcf ys hys

/-! ## Over `coreOK`: the statements of `famEx_values` and `famOpen_values` -/

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (x y : Config c)
    (r : Rule) (σ : Subst) (hs : ∃ y₀, StepBy c r σ x y₀)
    (hy : Γc c ⊧ (den c y.val ⇒ famEx c r σ)),
    ∃ σ', (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y :=
  fun c h hf => famEx_values_ce c (Semantics.coreOKEx_of_coreOK h) hf

example : ∀ (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (x : Config c) (r : Rule) (hr : r ∈ c.rules) (σ : Subst) (hu : Unblocked c r σ x.val)
    (hcf : ∀ i ∈ r.opens, (r.vars[i]?.map c.confined).getD false = true)
    (ys : List GroundTerm)
    (hys : ∀ y : Config c, (∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y) →
      y.val ∈ ys),
    Γc c ⊧ (famOpen c r σ ⇒ KoreAML.disjList (ys.map (den c))) :=
  fun c h hf => famOpen_values_ce c (Semantics.coreOKEx_of_coreOK h) hf

/-- info: 'KCore.famEx_values_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famEx_values_ce
/-- info: 'KCore.famOpen_values_ce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famOpen_values_ce

end KCore.FamValuesCETest
