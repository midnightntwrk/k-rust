/-
  Names `iteIdx` lists (a code beginning `Lblite{`) on construct fixtures' kompiled texts,
  decided on the names' codes (NameCodes.lean).
  Run from the package root: `lake env lean test/IteNamesCodes.lean`.
  - rdr-ite-two-eq: the instance `Lblite{Foo,Foo}` of the text's own `Lblite{S1,S2}`, at two sorts,
    with an equation, is a function of the reading. Its code is listed by `iteIdx`, and `iteSort?`
    gives it no sort, so `namesNumbered` holds and its decision on codes (`namesNumberedC`) gives it.
  - rdr-ite-own: the instance `Lblite{Foo}` of the text's own `Lblite{S}`, at one sort, without an
    equation, is a parameter of the reading without an implementation; `namesNumbered` and
    `itesApart` from their decisions on codes.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KCore.Faithful.Model

namespace IteNamesCodesTest

namespace TwoEq

definition_of defn from "f2-examples/rdr-ite-two-eq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem fn_named : c.allFns.any (fun fn => c.symName fn.label == "Lblite{Foo,Foo}") = true := by
  decide +kernel

theorem namesNumbered : Faithful.namesNumbered c = true :=
  namesNumbered_of_codes rfl rfl (by decide +kernel)

end TwoEq

namespace Own

definition_of defn from "f2-examples/rdr-ite-own.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem param_named :
    c.params.any (fun k => c.symName k.sig.name == "Lblite{Foo}" && k.impl.isNone) = true := by
  decide +kernel

theorem namesNumbered : Faithful.namesNumbered c = true :=
  namesNumbered_of_codes rfl rfl (by decide +kernel)

theorem itesApart : Faithful.Model.itesApart c = true :=
  itesApart_of_codes rfl rfl rfl (by decide +kernel)

end Own

end IteNamesCodesTest

#check @IteNamesCodesTest.TwoEq.namesNumbered
#check @IteNamesCodesTest.Own.param_named
#check @IteNamesCodesTest.Own.itesApart
#print axioms IteNamesCodesTest.TwoEq.namesNumbered
#print axioms IteNamesCodesTest.Own.param_named
#print axioms IteNamesCodesTest.Own.itesApart
