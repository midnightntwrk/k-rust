/-
  RANGEMAP's three parameters on the fixture e6-param-rangemap's kompiled text
  (`f2-examples/e6-param-rangemap.kompile.kore`, the text whose sha256 the fixture's kompile.txt
  records, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory
  relative to the tree): `choice` (domains.md 682), `keys_list` (634) and `values` (652), each
  applied once by a rule of the text (`go(1, X)`, `go(2, X)`, `go(3, X)`). The reader reads each as
  a parameter symbol no hook implements (`impl = none`, `raw = false`; the fixture's params.txt):
  its value at an argument list is the interpretation's (`paramVal`), and Γ holds its graph
  (`ΓDomains`), ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undetermined_const`, KcoreSpec/ParamSchema.lean). The pair of
  models: under `HookParams.none` the application is ⊥ in every model of Γ, under `constH v` it is
  `v` in every model, and both theories have models (`sound_hyp`; `FnHyp` holds under every H, the
  text having no function: `fnHyp_of_fns_nil`).
  The points: `choice` and `values` at the map `[0, 3) ↦ 7`, `keys_list` at the same map; the values
  are `7` as a KItem (`choice`) and the list holding it (`keys_list`, `values`). Whatever value the
  prose would name there, none is entailed: the text leaves the chosen key and the lists' order open
  (domains.md 634, 652, 682), and Γ holds the interpretation's value.

  Run from the package root: `lake env lean -j1 test/ParamRangeMap.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamRangeMap

open KCore ML Faithful ParamSchema

/-! ## The text -/

definition_of defn from "f2-examples/e6-param-rangemap.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem fns_nil : c.fns = [] := by decide +kernel

theorem readsConfined_c : c.readsConfined = false := by decide +kernel

/-- With no function, `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_of_fns_nil c noRaw fns_nil readsConfined_c H

/-! ## The three parameters -/

/-- The map `[0, 3) ↦ 7`. -/
def m7 : GroundTerm := rmV [(rangeT 0 3, kint 7)]
/-- The list holding `7`. -/
def l7 : GroundTerm := .list Srt.list [kint 7]

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def choiceK : ParamSig := (paramOf "LblRangeMap'Coln'choice").getD default
noncomputable def keysListK : ParamSig :=
  (paramOf "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").getD default
noncomputable def valuesK : ParamSig :=
  (paramOf "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").getD default

/-- Each is a parameter of the text, looked up by its number, no hook implements it, and `m7` is a
value of its argument sort and `7` (as a KItem) or `l7` a value of its result sort. -/
theorem params_ok :
    (paramOf "LblRangeMap'Coln'choice").isSome = true ∧
    (paramOf "Lblkeys'Unds'list'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").isSome = true ∧
    (paramOf "Lblvalues'LParUndsRParUnds'RANGEMAP'Unds'List'Unds'RangeMap").isSome = true ∧
    c.lookupParam choiceK.sig.name = some choiceK ∧ c.lookupParam keysListK.sig.name = some keysListK ∧
    c.lookupParam valuesK.sig.name = some valuesK ∧
    choiceK.impl = none ∧ keysListK.impl = none ∧ valuesK.impl = none ∧
    c.sortsOf [m7] = some choiceK.sig.args ∧ c.sortsOf [m7] = some keysListK.sig.args ∧
    c.sortsOf [m7] = some valuesK.sig.args ∧
    c.sortOf (kint 7) = some choiceK.sig.result ∧ c.sortOf l7 = some keysListK.sig.result ∧
    c.sortOf l7 = some valuesK.sig.result := by
  decide +kernel

/-- **`choice(M)` is not determined by the text**: over all H, Γ entails neither that `choice` at
`[0, 3) ↦ 7` has no value nor that it is `7`. -/
theorem choice_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) choiceK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) choiceK.sig.name [m7] ≡ den (c.withHooks H) (kint 7))) :=
  param_undetermined_const c coreOK noRaw params_ok.2.2.2.1 params_ok.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`keys_list(M)` is not determined by the text**: over all H, Γ entails neither that it has no
value at `[0, 3) ↦ 7` nor that it is the list of `7`. -/
theorem keysList_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) keysListK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) keysListK.sig.name [m7] ≡ den (c.withHooks H) l7)) :=
  param_undetermined_const c coreOK noRaw params_ok.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`values(M)` is not determined by the text**: over all H, Γ entails neither that it has no
value at `[0, 3) ↦ 7` nor that it is the list of `7`. -/
theorem values_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) valuesK.sig.name [m7] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) valuesK.sig.name [m7] ≡ den (c.withHooks H) l7)) :=
  param_undetermined_const c coreOK noRaw params_ok.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (fnHyp _) (fnHyp _)

end KCore.ParamRangeMap

/-- info: 'KCore.ParamRangeMap.choice_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.choice_undetermined
/-- info: 'KCore.ParamRangeMap.keysList_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.keysList_undetermined
/-- info: 'KCore.ParamRangeMap.values_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRangeMap.values_undetermined
