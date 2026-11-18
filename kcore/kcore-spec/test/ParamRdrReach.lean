/-
  Three functions of a text with no equation, on K 7.1.337 kompile's own texts
  (`f2-examples/NAME.kompile.kore`, each the text its fixture's kompile.txt hashes, BUILTIN/ restored
  as K's builtin directory and FIXTURE/ as the fixture's directory relative to the tree):

  - `rdr-ite-two` (`syntax {S1, S2} S2 ::= cast(S1) [function, symbol(ite)]`, `rule f(X) =>
    cast(X)`): f's equation applies `Lblite{SortFoo{}, SortFoo{}}`, the instance at Foo, Foo of the
    text's own two-sort function, of which the text states no equation.
  - `rdr-ite-own` (`syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite)]`, K-EQUAL not imported,
    `rule f(X) => pick(false, X, b)`): f's equation applies `Lblite{SortFoo{}}`, the instance at Foo of
    the text's own one-sort function, of which the text states no equation.
  - `rdr-proj-norule` (`pe(K) [function, symbol(project:Exp)]`, no rule): the text declares
    `Lblproject'Coln'Exp` and states no equation of it.

  The reader reads each as a parameter symbol no hook implements (`impl = none`, `raw = false`;
  `kcore sem-fields` of the text): its value at an argument list is the interpretation's
  (`paramVal`), and Γ holds its graph, ⊥ where the interpretation gives none.

  The `param_undetermined` shape at a point of each (DONE-0 C2, row `parameter`; C7 form (c)): over
  all interpretations H, Γ entails neither that the application has no value nor that it is a given
  value of its result sort (`undetermined_of_paramOK`, KcoreSpec/ParamSchema.lean: under
  `HookParams.none` the application is ⊥ in every model of Γ, under `constH v` it is `v`, and both
  theories have models). `FnHyp` holds under every H: the one function of each ite text (`f`, not
  declared total) and the text without a function owe no fact the deciders name (`fnHyp_decided`).
  The points: `ite{Foo, Foo}` at `(a)` with `a`, `ite{Foo}` at `(false, a, b)` with `b` (the value f's
  equation would give if the symbol were K's ite), `project:Exp` at the empty K with `a(0)`. None is
  entailed: the text states no sentence of these symbols' graphs.

  Run from the package root: `lake env lean -j1 test/ParamRdrReach.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.ParamRdrReach

open KCore ML Faithful ParamSchema

/-- The symbol named `n`, by number. -/
def symRR (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0

/-- The empty K. -/
def kDotRR : GroundTerm := .ctor dotk []

/-! ## rdr-ite-two: `ite{Foo, Foo}`, an instance of the text's own two-sort function -/

namespace IteTwo

definition_of defn from "f2-examples/rdr-ite-two.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's function `f` owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- The constant `a` of sort Foo. -/
noncomputable def aV : GroundTerm := .ctor (symRR c "Lbla") []

/-- **`ite{Foo, Foo}(a)` is not determined by the text**: over all H, Γ entails neither that it has
no value nor that it is `a`. -/
theorem ite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblite{Foo,Foo}").sig.name [aV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblite{Foo,Foo}").sig.name [aV] ≡ den (c.withHooks H) aV)) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end IteTwo

/-! ## rdr-ite-own: `ite{Foo}`, an instance of the text's own one-sort function -/

namespace IteOwn

definition_of defn from "f2-examples/rdr-ite-own.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The text's function `f` owes no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- The constants `a` and `b` of sort Foo. -/
noncomputable def aV : GroundTerm := .ctor (symRR c "Lbla") []
noncomputable def bV : GroundTerm := .ctor (symRR c "Lblb") []

/-- **`ite{Foo}(false, a, b)` is not determined by the text**: over all H, Γ entails neither that
it has no value nor that it is `b`. -/
theorem ite_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblite{Foo}").sig.name [bool false, aV, bV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblite{Foo}").sig.name [bool false, aV, bV] ≡
        den (c.withHooks H) bV)) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end IteOwn

/-! ## rdr-proj-norule: `project:Exp`, a function of the text with no equation -/

namespace ProjNorule

definition_of defn from "f2-examples/rdr-proj-norule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The deciders name no fact, so `FnHyp` holds under every interpretation. -/
theorem fnHyp (H : HookParams) : FnHyp (c.withHooks H) :=
  fnHyp_decided c coreOK noRaw (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (ord := []) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

/-- `a(0)`, a value of sort Exp. -/
noncomputable def a0 : GroundTerm := .ctor (symRR c "Lbla") [int 0]

/-- **`project:Exp(.K)` is not determined by the text**: over all H, Γ entails neither that it has
no value nor that it is `a(0)`. -/
theorem proj_undetermined :
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblproject'Coln'Exp").sig.name [kDotRR] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (c.withHooks H) ⊧
      (paramApp (c.withHooks H) (paramNamed c "Lblproject'Coln'Exp").sig.name [kDotRR] ≡
        den (c.withHooks H) a0)) :=
  undetermined_of_paramOK c coreOK noRaw fnHyp (by decide +kernel)

end ProjNorule

end KCore.ParamRdrReach

/-- info: 'KCore.ParamRdrReach.IteTwo.ite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRdrReach.IteTwo.ite_undetermined
/-- info: 'KCore.ParamRdrReach.IteOwn.ite_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRdrReach.IteOwn.ite_undetermined
/-- info: 'KCore.ParamRdrReach.ProjNorule.proj_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.ParamRdrReach.ProjNorule.proj_undetermined
