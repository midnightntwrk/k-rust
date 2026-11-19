/-
  The clause read from a `symbol-overload` axiom of a function, tied to the axiom with
  `KcoreSpec/TieOvlMem.lean`, on the literals `kore` and `defn` of two construct fixtures. Nothing
  here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieOvlMem.lean`.

  `Fn`, `f2-examples/e5-ovl-fn-fn.kompile.kore` (fixture e5-ovl-fn-fn): `negExp : Exp → Exp` a
  function overloading the function `negInt : Int → Int`. Sentence 124 is
  `negExp(inj{Int, Exp}(K0)) = inj{Int, Exp}(negInt(K0))`; Γ's item 0 is
  `X0 ∈ inj{Int, Exp}(V0) → negExp(X0) = inj{Int, Exp}(negInt(V0)) ∧ ⊤`.
  `Ct`, `f2-examples/e5-ovl-fn-fn-ctor.kompile.kore` (fixture e5-ovl-fn-fn-ctor): `sExp : Exp → Exp`
  a function overloading the constructor `sN : N → N`. Sentence 130 is
  `sExp(inj{N, Exp}(K0)) = inj{N, Exp}(sN(K0))`; Γ's item 0 binds the argument the same way.

  In each: the text's form of item 0 is the sentence up to the names of the variables (`same0`),
  and is not the item (`differs0`); the injection's Cons-Fun is an item of Γ (`injFun`), so the
  argument is one element of Exp in a model of Γ (`argOne`). Γ entails the sentence, for every H
  (`s124_entailed`, `s130_entailed`), and the sentence gives the item in a model with the
  constructors' facts and that Cons-Fun (`s124_from_text`, `s130_from_text`; `s124_iff`, `s130_iff`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieOvlMemTest

open KCore ML Faithful KoreAML

#check @TieOvlMem.ovlMem_entailed
#check @TieOvlMem.ovlMem_from_text
#check @TieOvlMem.ovlMem_iff
#check @TieOvlMem.argOne_inj

/-- A model of Γ satisfies each of Γ's equations. -/
theorem fnItem_sat {c : Semantics} {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (c.withHooks H)) {j : Nat} {a : Kore.Axiom} (ha : (TiePair.fnAxioms c)[j]? = some a) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
  have hg := TiePair.gammaPats_at ha
  obtain ⟨it, hit, he⟩ : ∃ it ∈ fnItems c, it.pat = (trAxiom [] [] ⟨0, "kernel", a⟩).pat := by
    unfold TiePair.gammaPats at hg
    rw [List.getElem?_map] at hg
    cases h : (fnItems c)[j]? with
    | none => rw [h] at hg; cases hg
    | some it => rw [h] at hg; exact ⟨it, List.mem_of_getElem? h, Option.some.inj hg⟩
  rw [← he]
  exact hI _ (TiePair.mem_Γ_fns (Or.inl ⟨it, by rw [TiePair.fnItems_withHooks]; exact hit, rfl⟩))

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- A model of Γ satisfies each of Γ's constructor items. -/
theorem consItem_sat {c : Semantics} {H : HookParams} {M : Type} {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (c.withHooks H)) {φ : P} (h : (consItemsK c).any (·.pat == φ) = true) : I ⊧ᴵ φ := by
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- The variable `VarV0` of the sort named `s`, the clause's variable under the injection. -/
def v0 (s : String) : Kore.EVar := ⟨⟨⟨"VarV0"⟩⟩, .ctor ⟨⟨s⟩⟩ []⟩

/-! ## e5-ovl-fn-fn -/

namespace Fn

kore_term kore from "f2-examples/e5-ovl-fn-fn.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fn-fn.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn.kompile.kore" module "E5-OVL-FN-FN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- A model of Γ has the constructors' facts. -/
theorem nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H)
    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)

/-- Γ's axiom of item 0, the clause of `negExp` read from the overload axiom. -/
noncomputable def ax0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax0_at : (TiePair.fnAxioms c)[0]? = some ax0 := by decide +kernel
noncomputable def item0 : P := (trAxiom [] [] ⟨0, "kernel", ax0⟩).pat
/-- The text's form of item 0: the injection at the argument of `negExp`. -/
noncomputable def text0 : P := (TieOvlMem.textItem ax0).getD .bottom
kernel_rfl text0_eq : TieOvlMem.textItem ax0 = some text0
theorem ok0 : TieOvlMem.okB c ax0 = true := by decide +kernel
theorem inj0 : TieOvlMem.injB ax0 "Exp" "Int" (v0 "SortInt") = true := by decide +kernel
/-- **Sentence 124 is the text's form of item 0** up to the names of the variables (kernel), and
is not the item. -/
theorem same0 : TieAlpha.acEqB text0 (trS U.ax124).pat = true := by decide +kernel
theorem differs0 : item0 ≠ (trS U.ax124).pat := by decide +kernel

/-- Cons-Fun of `inj{Int, Exp}` is an item of Γ. -/
theorem injFun : (consItemsK c).any (·.pat == (Cons.funItem "Exp" (.inj "Int")).pat) = true := by
  decide +kernel

/-- The argument `inj{Int, Exp}(V0)` is one element of Exp in a model of that item. -/
theorem argOne {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "Int")).pat) : TieOvlMem.ArgOne I ax0 :=
  TieOvlMem.argOne_inj hD hf inj0

/-- **E for sentence 124**: Γ entails it, for every H. -/
theorem s124_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax124).pat := by
  intro M _ I hI
  exact (TieAlpha.acEqB_sat same0).mp (TieOvlMem.ovlMem_entailed (nodeFacts H hI) text0_eq
    ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne (defOK hI) (consItem_sat hI injFun))
    (fnItem_sat hI ax0_at))

/-- **Sentence 124 gives Γ's item 0** in a model with the constructors' facts and Cons-Fun of the
injection, for every H. -/
theorem s124_from_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "Int")).pat)
    (h : I ⊧ᴵ (trS U.ax124).pat) : I ⊧ᴵ item0 :=
  TieOvlMem.ovlMem_from_text N text0_eq ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne N.defOK hf)
    ((TieAlpha.acEqB_sat same0).mpr h)

/-- **Sentence 124 and Γ's item 0 hold in the same models** among those with the constructors'
facts and Cons-Fun of the injection, for every H. -/
theorem s124_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "Int")).pat) :
    (I ⊧ᴵ (trS U.ax124).pat) ↔ (I ⊧ᴵ item0) :=
  (TieAlpha.acEqB_sat same0).symm.trans
    (TieOvlMem.ovlMem_iff N text0_eq ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne N.defOK hf))

end Fn

/-! ## e5-ovl-fn-fn-ctor -/

namespace Ct

kore_term kore from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore" module "E5-OVL-FN-FN-CTOR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- A model of Γ has the constructors' facts. -/
theorem nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H)
    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)

/-- Γ's axiom of item 0, the clause of `sExp` read from the overload axiom. -/
noncomputable def ax0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax0_at : (TiePair.fnAxioms c)[0]? = some ax0 := by decide +kernel
noncomputable def item0 : P := (trAxiom [] [] ⟨0, "kernel", ax0⟩).pat
/-- The text's form of item 0: the injection at the argument of `sExp`. -/
noncomputable def text0 : P := (TieOvlMem.textItem ax0).getD .bottom
kernel_rfl text0_eq : TieOvlMem.textItem ax0 = some text0
theorem ok0 : TieOvlMem.okB c ax0 = true := by decide +kernel
theorem inj0 : TieOvlMem.injB ax0 "Exp" "N" (v0 "SortN") = true := by decide +kernel
/-- **Sentence 130 is the text's form of item 0** up to the names of the variables (kernel), and
is not the item. -/
theorem same0 : TieAlpha.acEqB text0 (trS U.ax130).pat = true := by decide +kernel
theorem differs0 : item0 ≠ (trS U.ax130).pat := by decide +kernel

/-- Cons-Fun of `inj{N, Exp}` is an item of Γ. -/
theorem injFun : (consItemsK c).any (·.pat == (Cons.funItem "Exp" (.inj "N")).pat) = true := by
  decide +kernel

/-- The argument `inj{N, Exp}(V0)` is one element of Exp in a model of that item. -/
theorem argOne {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "N")).pat) : TieOvlMem.ArgOne I ax0 :=
  TieOvlMem.argOne_inj hD hf inj0

/-- **E for sentence 130**: Γ entails it, for every H. -/
theorem s130_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax130).pat := by
  intro M _ I hI
  exact (TieAlpha.acEqB_sat same0).mp (TieOvlMem.ovlMem_entailed (nodeFacts H hI) text0_eq
    ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne (defOK hI) (consItem_sat hI injFun))
    (fnItem_sat hI ax0_at))

/-- **Sentence 130 gives Γ's item 0** in a model with the constructors' facts and Cons-Fun of the
injection, for every H. -/
theorem s130_from_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "N")).pat)
    (h : I ⊧ᴵ (trS U.ax130).pat) : I ⊧ᴵ item0 :=
  TieOvlMem.ovlMem_from_text N text0_eq ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne N.defOK hf)
    ((TieAlpha.acEqB_sat same0).mpr h)

/-- **Sentence 130 and Γ's item 0 hold in the same models** among those with the constructors'
facts and Cons-Fun of the injection, for every H. -/
theorem s130_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hf : I ⊧ᴵ (Cons.funItem "Exp" (.inj "N")).pat) :
    (I ⊧ᴵ (trS U.ax130).pat) ↔ (I ⊧ᴵ item0) :=
  (TieAlpha.acEqB_sat same0).symm.trans
    (TieOvlMem.ovlMem_iff N text0_eq ((TieOvlMem.okB_withHooks c H _).trans ok0) (argOne N.defOK hf))

end Ct

#print axioms Fn.s124_iff
#print axioms Ct.s130_iff
#print axioms Fn.s124_entailed
#print axioms Fn.s124_from_text
#print axioms Ct.s130_entailed
#print axioms Ct.s130_from_text

end KCore.TieOvlMemTest
