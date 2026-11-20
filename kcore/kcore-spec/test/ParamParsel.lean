/-
  The instances of a sort-parametric function that a rule applies and of which the text states no
  equation, on two construct fixtures' kompiled texts (each the text its fixture's kompile.txt
  hashes):

  - `f2-examples/parsel.kompile.kore` (fixture parsel): `syntax {S} S ::= sel(Bool, S, S)
    [function]`, whose two rules become equations of the instance `Lblsel{SortK{}}`, while the rule
    `go(I) => go(sel(I >Int 0, I -Int 1, 0))` applies the instance `Lblsel{SortInt{}}`, of which the
    text states no equation and no totality.
  - `f2-examples/parsel-tot.kompile.kore` (fixture parsel-tot): `syntax {S} S ::= idp(S) [function,
    total]`, whose rule becomes an equation of the instance `Lblidp{SortK{}}`, while the rule
    `go(I) => go(idp(I -Int 1))` applies the instance `Lblidp{SortInt{}}`, of which the text states
    no equation; its `functional` axiom, quantified over the sort variable, states that every
    instance has a value.

  The reader reads each of the two instances as a parameter symbol no hook implements
  (`impl = none`, `raw = false`; `kcore sem-fields` of the text): its value at an argument list is
  the interpretation's (`paramVal`), and Γ holds its graph. A sentence of the instance at K says
  nothing of the instance at Int: they are two symbols of the text.

  `sel{Int}`, the `param_undetermined` shape (DONE-0 C2, row `parameter`; C7 form (c)): over all
  interpretations H, Γ entails neither that `sel{Int}(true, 0, 0)` has no value nor that it is `0`
  (`param_undetermined_const`, KcoreSpec/ParamSchema.lean). The pair of models: under
  `HookParams.none` the application is ⊥ in every model of Γ, under `constH 0` it is `0` in every
  model, and both theories have models (`sound_hyp`; `FnHyp` holds under every H, the text's
  function owing no fact: `Sel.fnHyp`). The point is the rule's own application at `I = 1`, and `0`
  the value the K rule `sel(true, A, _) => A` gives at every sort; it is not entailed.

  `idp{Int}`, the shape with two values (`param_undetermined_two`): the text states that the
  instance has a value, so an interpretation giving it none is no model of the text, and the
  statements are about the interpretations total on it (`ParamsTotal c totalParams`,
  `totalParams = [idp{Int}]`: `Idp.totalParams_eq`). Over those, Γ entails neither that `idp{Int}(0)`
  is `0` nor that it is `1`. The pair of models: under `constH 0` the application is `0` in every
  model of Γ, under `constH 1` it is `1`, the two values are distinct elements, and both theories
  have models (`sound_hyp`; `Idp.fnHyp`). The point is the rule's own application at `I = 1`, and
  `0` the value the K rule `idp(X) => X` gives at every sort; it is not entailed.

  Run from the package root: `lake env lean -j1 test/ParamParsel.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamParsel

open KCore ML Faithful ParamSchema

/-! ## parsel: `sel{Int}` -/

namespace Sel

definition_of defn from "f2-examples/parsel.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text declares no parameter total. -/
theorem totalParams_eq : defn.totalParams = [] := by decide +kernel

/-- The rank the text's function (`sel{K}`) is decided at. -/
def callOrder : List Nat := [385]

/-- The text's function owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := callOrder) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- **`sel{Int}(true, 0, 0)` is not determined by the text**: over all H, Γ entails neither that it
has no value nor that it is `0`. -/
theorem selInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblsel{Int}").sig.name [bool true, int 0, int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblsel{Int}").sig.name [bool true, int 0, int 0] ≡
        den (c.withHooks H) (int 0))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end Sel

/-! ## parsel-tot: `idp{Int}`, declared total -/

namespace Idp

definition_of defn from "f2-examples/parsel-tot.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The parameters the text declares total: `idp{Int}` alone. -/
theorem totalParams_eq : defn.totalParams = [(paramNamed c "Lblidp{Int}").sig.name] := by decide +kernel

/-- The rank the text's function (`idp{K}`) is decided at. -/
def callOrder : List Nat := [385]

/-- Under every interpretation total on `idp{Int}` the deciders name no fact: `FnHyp`. -/
theorem fnHyp (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : FnHyp (c.withHooks H) :=
  fnHyp_decided_total c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := callOrder) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hH

/-- **`idp{Int}(0)` is not determined by the text**: over the interpretations total on the
parameters the text declares total, Γ entails neither that it is `0` nor that it is `1`. -/
theorem idpInt_undetermined :
    ¬ (∀ H : HookParams, ParamsTotal c defn.totalParams H → Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblidp{Int}").sig.name [int 0] ≡ den (c.withHooks H) (int 0))) ∧
    ¬ (∀ H : HookParams, ParamsTotal c defn.totalParams H → Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblidp{Int}").sig.name [int 0] ≡ den (c.withHooks H) (int 1))) :=
  undetermined_two_of_paramOK c coreOK noRaw defn.totalParams fnHyp (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Idp

end KCore.ParamParsel

/-- info: 'KCore.ParamParsel.Sel.selInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamParsel.Sel.selInt_undetermined
/-- info: 'KCore.ParamParsel.Idp.idpInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamParsel.Idp.idpInt_undetermined
