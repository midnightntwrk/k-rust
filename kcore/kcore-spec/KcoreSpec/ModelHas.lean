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
import KcoreSpec.ModelChoiceHeld

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

/-- **The value model at its own step satisfies `Γ` with the step's closure** under
`HypModelCore`: of the rules it reads `ruleSorted` and `rulePlainHeldH` (`satRulesGoal_held`,
`satStepGoal_held`), which `HypModelCore` gives (`HypModelCore.ruleFactsHeld`). -/
theorem stdI_V_model_core (h : HypModelCore c) (hne : c.FnsNoExs) (hp : ClausePreDecided c) (hl : OpenLaws c) :
    stdI_T c (StepV c) ⊧ᴵP (Γ c ∪ Γstep c) := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal h φ hφ
    · exact AtT.satConsGoal h hl φ hφ
    · exact AtT.satDomainsGoal h φ hφ
    · exact AtT.satCollsGoal h φ hφ
    · exact AtT.satFnsGoal_decided h hne hp φ hφ
    · exact satRulesGoal_held h h.ruleFactsHeld (StepV c) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
        (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩) φ hφ
    · exact AtT.satFallbackGoal h φ hφ
  · exact satStepGoal_held h h.ruleFactsHeld (StepV c) (fun _ _ _ _ hT => hT) φ hφ

/-- **`Γ` with the step's closure has a model** under `HypModelCore`: the value model at its own
step (`stdI_V_model_core`), where no clause has an existential variable (`FnsNoExs`) and each
clause's predicate has a truth value wherever its patterns match (`ClausePreDecided`). The rules' predicates are not read. -/
theorem has_model_core (h : HypModelCore c) (hne : c.FnsNoExs) (hp : ClausePreDecided c)
    (_htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hl : OpenLaws c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  ⟨Elem, inferInstance, stdI_T c (StepV c), stdI_V_model_core h hne hp hl⟩

/-- `HypModel` gives `HypModelCore`: its functions' coherence gives `FnDet`
(`fnDet_of_coherent`), and with their termination `FnSolves` (`fnSolves_of_total`). -/
theorem HypModel.core (h : HypModel c) : HypModelCore c :=
  have hd := fnDet_of_coherent (CoherentAll_of h.hyp.core)
  HypModel.core_of h hd (fnSolves_of_total h.sound.core hd h.hyp.core.2.2.1
    fun fn hfn cl hcl hne vs σ hdec =>
      (h.hyp.2.2.2.2.2.1 fn hfn cl hcl).2 hne fn.label fn vs σ
        (lookupFn_of_sound h.sound.core (List.mem_append_left _ hfn)) hcl hdec)

/-- **`Γ` with the step's closure has a model** under `HypModel`: `has_model_core`. -/
theorem has_model (h : HypModel c) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hl : OpenLaws c) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Γ c ∪ Γstep c) :=
  has_model_core h.core (Semantics.fnsNoExs_of_sortedOK h.hyp.core.1) (clausePreDecided_of_terminates h.sound.core h.hyp.core.2.2.1) htop hl

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
