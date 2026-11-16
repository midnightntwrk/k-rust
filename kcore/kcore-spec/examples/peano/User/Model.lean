/-
  Peano's theory with the step's closure has a model: its semantics meets `HypModel`, so the value
  model satisfies it (ModelHas.lean). The decidable facts are kernel decisions; `Hyp` is
  `FaithfulWitness.hyp`.
-/
import User.Faithful
import KcoreSpec.ModelHas

set_option autoImplicit false
set_option maxRecDepth 1000000
-- the conditions decided in the kernel enumerate `hookSigs` (`itesApart` compares every pair of the
-- semantics' symbols, the interpreted ones among them), as in KcoreSpec/ModelHas.lean
set_option maxHeartbeats 1000000

namespace Peano.ModelWitness

open KCore KCore.Faithful KCore.Faithful.Model Peano

theorem hypSound : HypSound c :=
  ⟨FaithfulWitness.okAll, srReady, FaithfulWitness.namesNumbered, FaithfulWitness.genWf_ok,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    OvlOK.of_nil (by decide +kernel) (by decide +kernel)⟩

theorem hypModel : HypModel c :=
  ⟨FaithfulWitness.hyp, hypSound, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- Peano's `Γ` with the step's closure has a model. -/
theorem has_model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  Model.has_model hypModel

end Peano.ModelWitness
