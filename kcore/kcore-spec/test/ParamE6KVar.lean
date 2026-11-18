/-
  KVAR's hooked function String2KVar (substitution.md, hook STRING.string2token) on the construct
  fixture e6-param-kvar (`f2-examples/e6-param-kvar.kompile.kore`, the text its fixture's kompile.txt
  hashes, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's directory relative
  to the tree). The reader reads it as a parameter symbol no hook implements (`impl = none`,
  `raw = false`; the fixture's params.txt), from String to the definition's own token sort KVar:
  its value at an argument list is the interpretation's (`paramVal`), and Γ holds its graph.

  The text declares String2KVar `total` (its `functional` axiom), and the `[total]` function
  freshKVar applies it: `freshKVar(I) => String2KVar("_" +String Int2String(I))`. So the statements
  of this text are about the interpretations total on String2KVar (`ParamsTotal c totalParams`,
  `totalParams = [String2KVar]`): under one that gives it no value somewhere, such as
  `HookParams.none`, freshKVar's totality is owed and the deciders do not confirm it
  (`total_needs_param`). Under a total one the deciders name no fact (`fnHyp`).

  The `param_undetermined` shape with two values (`param_undetermined_two`,
  KcoreSpec/ParamSchema.lean; DONE-0 C2, row `parameter`; C7 form (c)): over the interpretations
  total on String2KVar, Γ entails neither that `String2KVar("a")` is the KVar `x` nor that it is the
  KVar `y`. The pair of models: under `constH x` the application is `x` in every model of Γ, under
  `constH y` it is `y`, the two values are distinct elements, and both theories have models
  (`sound_hyp`). Whatever token the K prose would name there, none is entailed: the text states
  that the symbol has a value and no sentence of its graph.

  Run from the package root: `lake env lean -j1 test/ParamE6KVar.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamE6KVar

open KCore ML Faithful ParamSchema

definition_of defn from "f2-examples/e6-param-kvar.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The name of String2KVar. -/
def s2kName : String := "LblString2KVar'LParUndsRParUnds'KVAR-COMMON'Unds'KVar'Unds'String"

/-- The String `"a"`. -/
def strA : GroundTerm := .dv Srt.string (.tok "a")
/-- The KVar `x`: a token of String2KVar's result sort. -/
noncomputable def kvarX : GroundTerm := .dv (paramNamed c s2kName).sig.result (.tok "x")
/-- The KVar `y`. -/
noncomputable def kvarY : GroundTerm := .dv (paramNamed c s2kName).sig.result (.tok "y")

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The parameters the text declares total: String2KVar alone. -/
theorem totalParams_eq : defn.totalParams = [(paramNamed c s2kName).sig.name] := by decide +kernel

/-- The rank the text's function (`freshKVar`) is decided at. -/
def callOrder : List Nat := [386]

/-- With String2KVar not taken total, freshKVar's totality is named: `FnHyp` is not decided under
an interpretation that is not total on it. -/
theorem total_needs_param : c.totalObligationsRP callOrder [] = [386] := by decide +kernel

/-- Under every interpretation total on String2KVar the deciders name no fact: `FnHyp`. -/
theorem fnHyp (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : FnHyp (c.withHooks H) :=
  fnHyp_decided_total c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := callOrder) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hH

/-- **`String2KVar("a")` is not determined by the text**: over the interpretations total on the
parameters the text declares total, Γ entails neither that it is the KVar `x` nor that it is the
KVar `y`. -/
theorem string2KVar_undetermined :
    ¬ (∀ H : HookParams, ParamsTotal c defn.totalParams H → Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c s2kName).sig.name [strA] ≡ den (c.withHooks H) kvarX)) ∧
    ¬ (∀ H : HookParams, ParamsTotal c defn.totalParams H → Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c s2kName).sig.name [strA] ≡ den (c.withHooks H) kvarY)) :=
  undetermined_two_of_paramOK c coreOK noRaw defn.totalParams fnHyp (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end KCore.ParamE6KVar

/-- info: 'KCore.ParamE6KVar.string2KVar_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamE6KVar.string2KVar_undetermined
