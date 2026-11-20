/-
  A function of a text with no equation, on K 7.1.337 kompile's own text
  (`f2-examples/e5-fn-noeq.kompile.kore`, the text the fixture e5-fn-noeq's kompile.txt hashes,
  BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory relative to
  the tree): `syntax Int ::= f(Int) [function]`, no rule of `f`, and the rule `go(X) => done(f(X))`
  applying it. The text declares `symbol Lblf{}(SortInt{}) : SortInt{} [function{}()]` (not total,
  so no `functional` axiom of it) and states no equation of it.

  The reader reads `f` as a parameter symbol no hook implements (`impl = none`, `raw = false`;
  `kcore sem-fields` of the text): its value at an argument list is the interpretation's
  (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at the point `f(0)` (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is `0`
  (`undetermined_of_paramOK`, KcoreSpec/ParamSchema.lean). The pair of models: under
  `HookParams.none` the application is ⊥ in every model of Γ, under `constH 0` it is `0` in every
  model, and both theories have models (`FnHyp` holds under every H: the text has no function with
  an equation that owes a fact the deciders name, `fnHyp`). `0` is only a value of the result sort:
  the text states no sentence of the symbol's graph, so no value is entailed and neither is ⊥.

  Run from the package root: `lake env lean -j1 test/ParamE5FnNoeq.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE5FnNoeq

open KCore ML Faithful ParamSchema

definition_of defn from "f2-examples/e5-fn-noeq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The deciders name no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`f(0)` is not determined by the text**: over all H, Γ entails neither that it has no value
nor that it is `0`. -/
theorem f_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblf").sig.name [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblf").sig.name [int 0] ≡
        den (c.withHooks H) (int 0))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end KCore.ParamE5FnNoeq

/-- info: 'KCore.ParamE5FnNoeq.f_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamE5FnNoeq.f_undetermined
