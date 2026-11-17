/-
  The `functional` sentences of interpreted hooked symbols on `f2-examples/ens.kompile.kore`,
  entailed at values (`EntailsAtValues`, direction Ev) for every interpretation H, from the
  library's one statement (`LibEv.functional_ev`, KcoreSpec/LibEvFun.lean).
  Run from the package root: `lake env lean test/LibFunEns.lean`.

  - `funIdx`: the 47 sentences `\exists{R}(Val:s, \equals{s, R}(Val:s, f(K0:s0, …)))` whose symbol
    `f` is an interpreted hooked symbol (`hookSigs`) that is not partial: the 46 the text declares
    with a `hook` attribute, and `freshInt`'s (81), which the registry interprets.
  - `fun_checked`: each of them is `LibEv.funPatR k` for the signature `k` of `hookSigs` with its
    symbol's name, over the one sort variable `R`, and `k` is not in `partialHooks` (one kernel
    decision over the list).
  - `fun_entailed`: each is entailed at values, for every H.

  Not among them: 99, the sentence of `ite`, which the text states once over a sort variable
  (`axiom{R, SortSort}`, `Lblite{SortSort}(K0:SortBool{}, K1:SortSort, K2:SortSort)`): it is not of
  the form `funPatR k`, whose sorts are the registry's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibFunEns

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/ens.kompile.kore"
definition_of defn from "f2-examples/ens.kompile.kore"
user_axioms U from "f2-examples/ens.kompile.kore" module "ENS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide +kernel
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- The indices of the sentences. -/
def funIdx : List Nat :=
  [19, 20, 21, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 56, 64, 65, 66, 67, 68,
   69, 70, 71, 72, 74, 76, 77, 81, 83, 100, 101, 102, 105, 106, 107, 110, 111, 112]

/-- The sentences, in text order. -/
noncomputable def funText : List AxiomDecl := U.all.filter fun ad => funIdx.contains ad.index

theorem funText_length : funText.length = 47 := by decide +kernel

/-- The name of the symbol a sentence of the form `\exists{R}(Val, \equals{s, R}(Val, f(…)))`
applies. -/
def headOf : Kore.Pattern → Option String
  | .exist _ _ (.equals _ _ _ (.app h _ _)) => some h.ident.name
  | _ => none

/-- The signature of the interpreted symbol with the name of the sentence's symbol. -/
def sigOf (ad : AxiomDecl) : Option KCore.CtorSig :=
  (headOf ad.ax.pattern).bind fun n => hookSigs.find? fun k => regSymNames.getD k.name "" == n

/-- The sentence is the `functional` sentence of a symbol of `hookSigs` that is not partial, over
the one sort variable `R`. -/
def funOK (ad : AxiomDecl) : Bool :=
  match sigOf ad with
  | some k => decide (ad.ax.pattern = LibEv.funPatR k) && decide (ad.ax.sortVars = [Rv]) && LibEv.funReg k &&
      !partialHooks.contains k.name
  | none => false

theorem fun_checked : funText.all funOK = true := by decide +kernel

/-- None of the 47 reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem fun_trS : funText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **Ev for the `functional` sentences of the interpreted symbols**: each of the 47 holds in
every model of Γ at every valuation sending its variables to values, for every H. -/
theorem fun_entailed (H : HookParams) : ∀ ad ∈ funText, EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  rw [of_decide_eq_true (List.all_eq_true.mp fun_trS ad had)]
  have hok := List.all_eq_true.mp fun_checked ad had
  unfold funOK at hok
  cases hsig : sigOf ad with
  | none => rw [hsig] at hok; cases hok
  | some k =>
    rw [hsig] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨hp, hsv⟩, hreg⟩, hpar⟩ := hok
    obtain ⟨n, -, hfind⟩ := Option.bind_eq_some_iff.mp hsig
    exact LibEv.functional_ev (coreOKH H) (shapesOKH H) (List.mem_of_find?_eq_some hfind) (Or.inl hpar) hreg ad hp
      hsv

end KCore.LibFunEns

#check @KCore.LibEv.functional_ev
#check @KCore.LibEv.subst_of_atValues
/-- info: 'KCore.LibFunEns.fun_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibFunEns.fun_entailed
