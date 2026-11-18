/-
  The K-level parameter symbols on three construct fixtures' kompiled texts (each the text its
  kompile.txt hashes, BUILTIN/ restored as K's builtin directory and FIXTURE/ as the fixture's
  directory relative to the tree):

  - `f2-examples/e3-param-cases.kompile.kore` (fixture e3-param-cases): `syntax {S} S ::= pick(Bool,
    S, S)` and `syntax {P} Bool ::= isZeroOf(P, Int)`, whose rules become equations of the instances
    `Lblpick{SortK{}}` and `LblisZeroOf{SortK{}}`, while the rule `a(X) => b(isZeroOf(a(X), pick(true,
    X, 0)))` applies the instances `Lblpick{SortInt{}}` and `LblisZeroOf{SortExp{}}`, of which the
    text states no equation.
  - `f2-examples/e1-param-two-sort.kompile.kore` (fixture e1-param-two-sort): `syntax {S, T} Bool ::=
    same(S, T)`, a symbol with two sort parameters, whose rule becomes an equation of the instance
    `Lblsame{SortK{}, SortK{}}`, while the rule `a(X) => b(same(X, a(X)))` applies the instance
    `Lblsame{SortInt{}, SortExp{}}`, of which the text states no equation.
  - `f2-examples/e8-hook-namespaces.kompile.kore` (fixture e8-hook-namespaces, `--hook-namespaces
    FOO`): `hooked-symbol Lblfh{}(SortInt{}) : SortInt{}` with `hook{}("FOO.bar")`, a hook no
    registry entry names, and no equation (the text declares it and applies it nowhere).

  The reader reads each of the four as a parameter symbol no hook implements (`impl = none`,
  `raw = false`; `kcore sem-fields` of the text): its value at an argument list is the
  interpretation's (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`param_undetermined_const`, KcoreSpec/ParamSchema.lean). The pair of
  models: under `HookParams.none` the application is ⊥ in every model of Γ, under `constH v` it is
  `v` in every model, and both theories have models (`sound_hyp`; `FnHyp` holds under every H, each text's functions owing no
  fact: `fnHyp`). The points: `pick{Int}` at `(true, 0, 0)` with `0`, `isZeroOf{Exp}` at `(a(0), 0)`
  with `true`, `same{Int, Exp}` at `(0, a(0))` with `true`, `fh` at `0` with `0`. For the three
  instances the value is the one the K rule of the symbol gives at every sort; `fh` has no rule, and
  `0` there is only a value of its result sort. None is entailed: the text states no sentence of
  these symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamKLevel.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamKLevel

open KCore ML Faithful ParamSchema

/-! ## e3-param-cases: `pick{Int}` and `isZeroOf{Exp}` -/

namespace E3Cases

definition_of defn from "f2-examples/e3-param-cases.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The rank the text's two functions (`pick{K}`, `isZeroOf{K}`) are decided at. -/
def callOrder : List Nat := [387, 388]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (c.withHooks H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- The functions owe no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def pickK : ParamSig := (paramOf "Lblpick{Int}").getD default
noncomputable def isZeroOfK : ParamSig := (paramOf "LblisZeroOf{Exp}").getD default

/-- The constructor `a : Int → Exp`. -/
noncomputable def aSym : Sym := ((c.ctors.find? fun ct => c.symName ct.name == "Lbla").map (·.name)).getD 0

/-- `a(0)`, a value of sort Exp. -/
noncomputable def a0 : GroundTerm := .ctor aSym [int 0]

/-- Each is a parameter of the text, looked up by its number, no hook implements it, the points'
arguments are values of its argument sorts and the given values of its result sort. -/
theorem params_ok :
    (paramOf "Lblpick{Int}").isSome = true ∧ (paramOf "LblisZeroOf{Exp}").isSome = true ∧
    c.lookupParam pickK.sig.name = some pickK ∧ c.lookupParam isZeroOfK.sig.name = some isZeroOfK ∧
    pickK.impl = none ∧ isZeroOfK.impl = none ∧
    c.sortsOf [bool true, int 0, int 0] = some pickK.sig.args ∧
    c.sortsOf [a0, int 0] = some isZeroOfK.sig.args ∧
    c.sortOf (int 0) = some pickK.sig.result ∧ c.sortOf (bool true) = some isZeroOfK.sig.result := by
  decide +kernel

/-- **`pick{Int}(true, 0, 0)` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `0`. -/
theorem pickInt_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) pickK.sig.name [bool true, int 0, int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) pickK.sig.name [bool true, int 0, int 0] ≡ den (c.withHooks H) (int 0))) :=
  param_undetermined_const c coreOK noRaw params_ok.2.2.1 params_ok.2.2.2.2.1 params_ok.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.1 (fnHyp _) (fnHyp _)

/-- **`isZeroOf{Exp}(a(0), 0)` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `true`. -/
theorem isZeroOfExp_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) isZeroOfK.sig.name [a0, int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) isZeroOfK.sig.name [a0, int 0] ≡ den (c.withHooks H) (bool true))) :=
  param_undetermined_const c coreOK noRaw params_ok.2.2.2.1 params_ok.2.2.2.2.2.1 params_ok.2.2.2.2.2.2.2.1
    params_ok.2.2.2.2.2.2.2.2.2 (fnHyp _) (fnHyp _)

end E3Cases

/-! ## e1-param-two-sort: `same{Int, Exp}`, an instance of a symbol with two sort parameters -/

namespace E1TwoSort

definition_of defn from "f2-examples/e1-param-two-sort.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's function (`same{K, K}`) owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- The constructor `a : Int → Exp`. -/
noncomputable def aSym : Sym := ((c.ctors.find? fun ct => c.symName ct.name == "Lbla").map (·.name)).getD 0

/-- `a(0)`, a value of sort Exp. -/
noncomputable def a0 : GroundTerm := .ctor aSym [int 0]

/-- **`same{Int, Exp}(0, a(0))` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `true`. -/
theorem sameIntExp_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblsame{Int,Exp}").sig.name [int 0, a0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblsame{Int,Exp}").sig.name [int 0, a0] ≡
        den (c.withHooks H) (bool true))) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end E1TwoSort

/-! ## e8-hook-namespaces: `fh`, hooked to `FOO.bar` -/

namespace E8HookNs

definition_of defn from "f2-examples/e8-hook-namespaces.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The rank the text's function (`f`) is decided at. -/
def callOrder : List Nat := [397]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (c.withHooks H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- The function owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- The parameter of the symbol named `n`: its signature as the reader has it. -/
noncomputable def paramOf (n : String) : Option ParamSig := c.params.find? fun k => c.symName k.sig.name == n

noncomputable def fhK : ParamSig := (paramOf "Lblfh").getD default

/-- `fh` is a parameter of the text, looked up by its number, no hook implements it, `0` is a value
of its argument sort and of its result sort. -/
theorem params_ok :
    (paramOf "Lblfh").isSome = true ∧ c.lookupParam fhK.sig.name = some fhK ∧ fhK.impl = none ∧
    c.sortsOf [int 0] = some fhK.sig.args ∧ c.sortOf (int 0) = some fhK.sig.result := by
  decide +kernel

/-- **`fh(0)` is not determined by the text**: over all H, Γ entails neither that it has no value
nor that it is `0`. -/
theorem fh_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧ (paramApp (c.withHooks H) fhK.sig.name [int 0] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) fhK.sig.name [int 0] ≡ den (c.withHooks H) (int 0))) :=
  param_undetermined_const c coreOK noRaw params_ok.2.1 params_ok.2.2.1 params_ok.2.2.2.1
    params_ok.2.2.2.2 (fnHyp _) (fnHyp _)

end E8HookNs

end KCore.ParamKLevel

/-- info: 'KCore.ParamKLevel.E3Cases.pickInt_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E3Cases.pickInt_undetermined
/-- info: 'KCore.ParamKLevel.E3Cases.isZeroOfExp_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E3Cases.isZeroOfExp_undetermined
/-- info: 'KCore.ParamKLevel.E1TwoSort.sameIntExp_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E1TwoSort.sameIntExp_undetermined
/-- info: 'KCore.ParamKLevel.E8HookNs.fh_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamKLevel.E8HookNs.fh_undetermined
