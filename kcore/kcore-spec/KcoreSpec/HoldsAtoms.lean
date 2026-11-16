/-
  KCore. The atomic cases of a condition's reading in the value model at a transition T: `ceil`,
  `equals` and `mem`, each as `holds_atT` gives it (HoldsModel.lean), so that each case has the one
  proof there.
-/
import KcoreSpec.HoldsModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

/-- **The atoms of a condition in the value model at T**: for `ceil`, `equals` and `mem`, at a
valuation that reads the atom's variables as their values under σ, an element of a numbered
predicate sort is in the atom exactly where the truth value `Holds` gives is `true` (`HoldsT`). -/
theorem holds_atoms {c : Semantics} {T : GroundTerm → GroundTerm → Prop} (h : HypModelCore c) :
    (∀ s t, HoldsT c T (.ceil s t)) ∧ (∀ s t u, HoldsT c T (.equals s t u)) ∧
      (∀ s t u, HoldsT c T (.mem s t u)) :=
  ⟨fun s t => holds_atT h (.ceil s t), fun s t u => holds_atT h (.equals s t u),
   fun s t u => holds_atT h (.mem s t u)⟩

end Model

end Faithful

end KCore
