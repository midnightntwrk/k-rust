/-
  KCore. `Γ` with the step's closure has a model under `HypModelCore` (`has_model_core`; under
  `HypModel`, `has_model`): the value model
  satisfies the signature, the constructors, the domains, the collections, the functions, the
  rules and the step's closure (ModelSig.lean, ModelCons.lean, ModelDomains.lean, ModelColls.lean,
  ModelFns.lean, OpenModel.lean, OpenConsistent.lean).

  The two regression cores that `Γ`'s repairs made consistent meet `HypModel`
  (ModelUndefRhsWitness.lean, ModelJunkWitness.lean); two others do not, by design: two symbols
  with one name are what `namesApartK` rejects (ModelNamesWitness.lean), a constructor listed twice
  is what `ctorsOnce` rejects (ModelDupCtorWitness.lean), and a function named like a constructor
  is what `fnsApart` rejects (ModelFnCtorWitness.lean).
-/
import KcoreSpec.ModelFns
import KcoreSpec.ModelUndefRhsWitness
import KcoreSpec.ModelJunkWitness
import KcoreSpec.ModelNamesWitness
import KcoreSpec.ModelDupCtorWitness
import KcoreSpec.ModelFnCtorWitness
import KcoreSpec.OpenConsistent
import KcoreSpec.ExStepT

set_option autoImplicit false
-- the witnesses' conditions decided in the kernel enumerate `hookSigs` (`itesApart` compares every
-- pair of a semantics' symbols, the interpreted ones among them)
set_option maxHeartbeats 1000000

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **`Γ` has a model, from `HypModelCore` and the goals that remain.** -/
theorem has_model_of_hyp (h : HypModelCore c) (h2 : SatConsGoal c) (h5 : SatFnsGoal c) (h6 : SatRulesGoal c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ c :=
  has_model_of c (satSigGoal h) h2 (satDomainsGoal h) (satCollsGoal h) h5 h6 (satFallbackGoal h)

/-- **`Γ` with the step's closure has a model, from `HypModelCore` and the goals that remain.** -/
theorem has_model_step_of_hyp (h : HypModelCore c) (h2 : SatConsGoal c) (h5 : SatFnsGoal c)
    (h6 : SatRulesGoal c) (h7 : SatStepGoal c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  has_model_step_of c (satSigGoal h) h2 (satDomainsGoal h) (satCollsGoal h) h5 h6 h7 (satFallbackGoal h)

/-- **`Γ` with the step's closure has a model** under `HypModelCore`: the value model. Of the
rules it reads `ruleSorted` and `rulePlainEx` (`satRulesGoal_StepM`, `satStepGoal_StepM`), so it is
stated for rules with `\top` predicates. -/
theorem has_model_core (h : HypModelCore c) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hl : OpenLaws c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  has_model_step_of c (satSigGoal h) (satConsGoal h hl) (satDomainsGoal h) (satCollsGoal h) (satFnsGoal h)
    (satRulesGoal_StepM h (h.ruleFactsEx_of_top htop))
    (satStepGoal_StepM h (h.ruleFactsEx_of_top htop)) (satFallbackGoal h)

/-- `HypModel` gives `HypModelCore`: its functions' coherence gives `FnDet`
(`fnDet_of_coherent`), and with their termination `FnSolves` (`fnSolves_of_total`). -/
theorem HypModel.core (h : HypModel c) : HypModelCore c :=
  have hd := fnDet_of_coherent (CoherentAll_of h.hyp.core) (Semantics.fnsNoExs_of_sortedOK h.sound.core.1)
  HypModel.core_of h hd (fnSolves_of_total h.sound.core hd h.hyp.core.2.2.1)

/-- **`Γ` with the step's closure has a model** under `HypModel`: `has_model_core`. -/
theorem has_model (h : HypModel c) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hl : OpenLaws c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  has_model_core h.core htop hl

end Model

namespace UndefRhsWitness

theorem hypModel : Model.HypModel c :=
  ⟨hyp, hypSound, by decide +kernel, by decide +kernel, idsOK, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem has_model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  Model.has_model hypModel (Semantics.rulesTop_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

end UndefRhsWitness

namespace JunkWitness

theorem hypModel : Model.HypModel c :=
  ⟨hyp, ⟨okAll, srReady, namesNumbered, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, inferInstance⟩, by decide +kernel, by decide +kernel, idsOK, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem has_model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  Model.has_model hypModel (Semantics.rulesTop_of_isTop (by decide +kernel)) (openLaws_of_plain (by decide +kernel))

end JunkWitness

namespace NamesWitness

/-- The core with two symbols of one name is outside `HypModel`. -/
theorem not_hypModel : ¬ Model.HypModel c := fun h => absurd h.names (by decide +kernel)

end NamesWitness

end Faithful

end KCore
