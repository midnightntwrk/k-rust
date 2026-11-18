/-
  The parameter symbol `ite` at Int on the text of the fixture e6-ite-int
  (`f2-examples/e6ite.kompile.kore`: STRING, INT and K-EQUAL imported, one rule
  `go => res(#if 1 <Int 2 #then 3 #else 4 #fi)`), for every interpretation H. Nothing here reads
  `Parse.parse` or `emit`. Run from the package root: `lake env lean -j1 test/IteIntParam.lean`.

  - `userAxioms_eq`, `ite_int_sentences`: the module's axioms applying `ite` at Int (the head
    `Lblite{SortInt{}}`) are two, 172 (the fixture's rule, whose right side kompile writes
    `Lblite{SortInt{}}(true, 3, 4)`) and 237 (`findChar`'s equation, domains.md 1891).
  - `params_ite`: the reading's one parameter symbol is `ite{Int}` (`Parse.iteName "Int"`), of
    arguments Bool, Int, Int and result Int, implemented by the registry's `kIte`.
  - `ite_int_in_gamma`: it is one of Γ's symbols (`kernelSyms`) and Γ applies it at the head
    `Lblite{SortInt{}}` (`gammaHasHead`), for every H.
  - `findChar_heads_in_gamma`: every head 237 applies, with its sort arguments, is one of Γ's, for
    every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.IteIntParam

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6ite.kompile.kore"
definition_of defn from "f2-examples/e6ite.kompile.kore"
user_axioms U from "f2-examples/e6ite.kompile.kore" module "E6-ITE-INT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

kernel_rfl kernelSyms_withHooks : ∀ (c : Semantics) (H : HookParams), kernelSyms (c.withHooks H) = kernelSyms c
kernel_rfl gammaHeads_withHooks : ∀ (c : Semantics) (H : HookParams), gammaHeads (c.withHooks H) = gammaHeads c

/-- The head at which the text applies `ite` at Int. -/
def iteIntHead : String × List Kore.KSort := ("Lblite", [KoreAML.srt "Int"])

/-- The axiom applies `ite` at Int. -/
def appliesIteInt (ad : AxiomDecl) : Bool := (appHeadsOf ad.ax.pattern).any (fun h => decide (h = iteIntHead))

theorem userAxioms_eq : kore.axiomDecls.filter (·.module == "E6-ITE-INT") = U.all := by kernel_rfl

theorem ite_int_sentences : (U.all.filter appliesIteInt).map (·.index) = [172, 237] := by
  decide +kernel

/-- **The reading's parameter symbols**: one, `ite{Int}`, `Bool × Int × Int → Int`, implemented by
`kIte`. -/
theorem params_ite :
    (c.params.map fun k => (c.symName k.sig.name, k.sig.args, k.sig.result, k.impl)) =
      [(Parse.iteName "Int", [Srt.bool, Srt.int, Srt.int], Srt.int, some kIte)] := by
  decide +kernel

theorem ite_int_in_gamma_c :
    (kernelSyms c).any (fun k => c.symName k.name == Parse.iteName "Int") = true ∧
    gammaHasHead c iteIntHead = true := by
  decide +kernel

/-- **Γ holds `ite{Int}`**, for every H: a symbol of Γ under the name `ite{Int}`, applied at the
head `Lblite{SortInt{}}`. -/
theorem ite_int_in_gamma (H : HookParams) :
    (kernelSyms (cH H)).any (fun k => (cH H).symName k.name == Parse.iteName "Int") = true ∧
    gammaHasHead (cH H) iteIntHead = true := by
  rw [kernelSyms_withHooks]
  unfold gammaHasHead
  rw [gammaHeads_withHooks]
  exact ite_int_in_gamma_c

theorem findChar_heads_in_gamma_c : (appHeadsOf U.ax237.ax.pattern).all (gammaHasHead c) = true := by
  decide +kernel

/-- Every head `findChar`'s equation (237, domains.md 1891) applies is one of Γ's, for every H. -/
theorem findChar_heads_in_gamma (H : HookParams) :
    (appHeadsOf U.ax237.ax.pattern).all (gammaHasHead (cH H)) = true := by
  unfold gammaHasHead
  rw [gammaHeads_withHooks]
  exact findChar_heads_in_gamma_c

end KCore.IteIntParam

/-- info: 'KCore.IteIntParam.ite_int_sentences' depends on axioms: [propext] -/
#guard_msgs in #print axioms KCore.IteIntParam.ite_int_sentences
#print axioms KCore.IteIntParam.params_ite
#print axioms KCore.IteIntParam.ite_int_in_gamma
#print axioms KCore.IteIntParam.findChar_heads_in_gamma
