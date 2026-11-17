/-
  Cons-Fun and Cons-Inj at uncovered arguments (`KoreAML.Cons.funUncItem`, `injUncItem`,
  Kore/Gamma.lean), which no item list writes yet: each is entailed by the text's item
  (`funUncItem_of_funItem`, `injUncItem_of_injItem`, FaithfulNeg.lean), and both are kernel-checked
  at the value model of a semantics `coreOK` accepts. Run from the package root:
  `lake env lean -j1 test/OvlUncItems.lean`.

  The semantics is the reader's for `f2-examples/ovlsub.kompile.kore` (`ovlsub.k`): `capGas : Gas →
  Gas` overloads the constructor `capN : N → N`, N < Gas. Its overload's argument sorts are `[N]`
  (`ovlArgsOf`), so the uncovered guard of `capGas`'s argument x says x is no `inj{N,Gas}` of an
  element of N. `c` has no function of its own, so `FnHyp` holds by its empty lists and the value
  model `stdI c` satisfies `funItem` and `injItem` of every generator (`sat_funItem`,
  `sat_injItem`); the two instances below are the uncovered items at `capGas` in that model.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore Faithful Faithful.Model

namespace OvlUncItems

definition_of defn from "f2-examples/ovlsub.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def capN : Sym := 387
def capGas : Sym := 394
def gasS : Srt := 32
def nS : Srt := 33

/-- `capGas`'s signature, at Gas. -/
def capSig : CtorSig := ⟨capGas, [gasS], gasS⟩

theorem names_ok : c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" ∧ c.sortName gasS = "Gas" ∧
    c.sortName nS = "N" ∧ c.ovls = [⟨capSig, [capN]⟩] ∧ c.fns = [] := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

theorem sortedOK : c.sortedOK = true := by decide_cheap

/-- `c` has no function of its own: `FnHyp` holds. -/
theorem fnHyp : FnHyp c :=
  ⟨fun _ h => absurd h (by rw [names_ok.2.2.2.2.2]; exact List.not_mem_nil),
   fun _ h => absurd h (by rw [names_ok.2.2.2.2.2]; exact List.not_mem_nil),
   fun _ h => absurd h (by rw [names_ok.2.2.2.2.2]; exact List.not_mem_nil),
   fun _ h => absurd h (by rw [names_ok.2.2.2.2.2]; exact List.not_mem_nil),
   openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain (by decide +kernel)⟩

theorem hyp : HypModelCore c := hypModel_of_fnHyp coreOK fnHyp

theorem gas_cons : gasS ∈ consSorts c := by decide +kernel

/-- `capGas` is a generator of Gas, among the overloading symbols' signatures. -/
theorem capGas_gen : Gen.ctor capSig ∈ c.gens gasS := by
  have h : capSig ∈ c.ovlSigs.filter (·.result == gasS) := by decide +kernel
  unfold Semantics.gens
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨capSig, h, rfl⟩)))

/-- The overload's argument sorts: `capGas`'s one argument is covered where it lies in N. -/
theorem capGas_covs : Faithful.ovlArgsOf c (.ctor capSig) = some [["N"]] ∧
    (Gen.toK c (.ctor capSig)).argSorts = ["Gas"] := by
  decide +kernel

/-- **Cons-Fun at uncovered arguments**, at `capGas` in the value model. -/
theorem capGas_funUnc :
    stdI c ⊧ᴵ (KoreAML.Cons.funUncItem (c.sortName gasS) (Gen.toK c (.ctor capSig)) [["N"]]).pat :=
  funUncItem_of_funItem _ (sat_funItem hyp gas_cons capGas_gen)

/-- **Cons-Inj at uncovered arguments**, at `capGas` in the value model. -/
theorem capGas_injUnc :
    stdI c ⊧ᴵ (KoreAML.Cons.injUncItem (c.sortName gasS) (Gen.toK c (.ctor capSig)) [["N"]]).pat :=
  injUncItem_of_injItem _ (sat_injItem hyp gas_cons capGas_gen)

/-- info: 'OvlUncItems.names_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms names_ok
/-- info: 'OvlUncItems.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK
/-- info: 'OvlUncItems.sortedOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sortedOK
/-- info: 'OvlUncItems.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp
/-- info: 'OvlUncItems.hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hyp
/-- info: 'OvlUncItems.gas_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gas_cons
/-- info: 'OvlUncItems.capGas_gen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms capGas_gen
/-- info: 'OvlUncItems.capGas_covs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capGas_covs
/-- info: 'OvlUncItems.capGas_funUnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capGas_funUnc
/-- info: 'OvlUncItems.capGas_injUnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capGas_injUnc

end OvlUncItems
