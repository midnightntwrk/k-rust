/-
  The function equations of two construct fixtures whose `requires` Γ reads through a cut, tied to
  the text's sentences with `KcoreSpec/TieCutEq.lean`, on the literals `kore` and `defn`. Nothing
  here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieCutEq.lean`.

  `ReqAndApp`, `f2-examples/mleqreqandapp.kompile.kore` (fixture e3-ml-eq-req-and-under-app):
  `g(X, Y) => 1 requires f(X #And Y) ==Int 0`, `g(_, _) => 0 [owise]`. Γ reads the `requires` as
  `f(X) ==Int 0` with the membership `X ∈ Y` in the clause's predicate (`andUnderAppCut`).
  - Sentence 212 (the first equation; Γ's item 1): the text's form of the item is the sentence up
    to the names of the variables (`same1`), and is not the item (`differs1`). The sentence gives
    the item in every model of definedness (`s212_from_text`); Γ entails the sentence, for every H
    (`s212_entailed`).
  - Sentence 213 (the `[owise]` equation; Γ's item 2), whose premise negates the first equation's:
    Γ entails the sentence, for every H, reading definedness only (`s213_entailed`); the sentence
    gives the item in a model with the constructors' facts (`s213_from_text`), since under the
    negation it is the text's premise that must be inside Γ's.

  `ReqNot`, `f2-examples/mleqreqnot.kompile.kore` (fixture e3-ml-eq-req-not):
  `f(X) => 1 requires #Not(X >Int 0)`, `f(_) => 0 [owise]`. Γ reads the `requires` as no term and
  the predicate `X >Int 0 = false` (`notAsCondition`).
  - Sentences 209 and 210 (Γ's items 0 and 1): each holds in the same models as its item among the
    models with the constructors' facts in which every element of Bool is `true` or `false`
    (`s209_iff`, `s210_iff`; `boolClosed` is a hypothesis). The definition reads no confined sort
    (`readsConfined_c`), so its theory does not state that closure; in a model of Γ with it the
    sentences hold (`s209_entailed`, `s210_entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieCutEqTest

open KCore ML Faithful KoreAML

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

/-! ## `andUnderAppCut`: e3-ml-eq-req-and-under-app -/

namespace ReqAndApp

kore_term kore from "f2-examples/mleqreqandapp.kompile.kore"
definition_of defn from "f2-examples/mleqreqandapp.kompile.kore"
user_axioms U from "f2-examples/mleqreqandapp.kompile.kore" module "E3-ML-EQ-REQ-AND-UNDER-APP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
/-- The definition reads no confined sort: its theory is Γ, without the closure of Bool. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- A model of Γ has the constructors' facts. -/
theorem nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H)
    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)

/-- Γ's axiom of item 1, the equation `g(X, Y) => 1 requires f(X) ==Int 0` with `X ∈ Y`. -/
noncomputable def ax1 : Kore.Axiom := ((TiePair.fnAxioms c)[1]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax1_at : (TiePair.fnAxioms c)[1]? = some ax1 := by decide +kernel
noncomputable def item1 : P := (trAxiom [] [] ⟨0, "kernel", ax1⟩).pat
/-- The text's form of item 1: the conjunction `X #And Y` at the argument of `f`. -/
noncomputable def text1 : P := (TieCutEq.textItem (.andApp [0, 0]) .own ax1).getD .bottom
kernel_rfl text1_eq : TieCutEq.textItem (.andApp [0, 0]) .own ax1 = some text1
theorem shape1 : TieCutEq.shapeOK (.andApp [0, 0]) .own ax1 = true := by decide +kernel
theorem facts1 : TieCutEq.factsOK c (.andApp [0, 0]) .own ax1 = true := by decide +kernel
/-- **Sentence 212 is the text's form of item 1** up to the names of the variables (kernel), and
is not the item. -/
theorem same1 : TieAlpha.acEqB text1 (trS U.ax212).pat = true := by decide +kernel
theorem differs1 : item1 ≠ (trS U.ax212).pat := by decide +kernel

/-- **Sentence 212 gives Γ's item 1** in every model of definedness. -/
theorem s212_from_text {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax212).pat) : I ⊧ᴵ item1 :=
  TieCutEq.cutEq_from_text_pure hD text1_eq shape1 ((TieAlpha.acEqB_sat same1).mpr h)

/-- **E for sentence 212**: Γ entails it, for every H. -/
theorem s212_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax212).pat := by
  intro M _ I hI
  exact (TieAlpha.acEqB_sat same1).mp (TieCutEq.cutEq_entailed (k := .andApp [0, 0]) (nodeFacts H hI)
    (sortOf_true H) (fun h => nomatch h) text1_eq shape1 ((TieCutEq.factsOK_withHooks c H _ _ _).trans facts1)
    (fnItem_sat hI ax1_at))

/-- Γ's axiom of item 2, the `[owise]` equation under the negation of item 1's premise. -/
noncomputable def ax2 : Kore.Axiom := ((TiePair.fnAxioms c)[2]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax2_at : (TiePair.fnAxioms c)[2]? = some ax2 := by decide +kernel
noncomputable def item2 : P := (trAxiom [] [] ⟨0, "kernel", ax2⟩).pat
/-- The text's form of item 2: the cut premise is the first competitor's, under its two binders. -/
noncomputable def text2 : P := (TieCutEq.textItem (.andApp [0, 0]) (.under 0 2) ax2).getD .bottom
kernel_rfl text2_eq : TieCutEq.textItem (.andApp [0, 0]) (.under 0 2) ax2 = some text2
theorem shape2 : TieCutEq.shapeOK (.andApp [0, 0]) (.under 0 2) ax2 = true := by decide +kernel
theorem facts2 : TieCutEq.factsOK c (.andApp [0, 0]) (.under 0 2) ax2 = true := by decide +kernel
/-- **Sentence 213 is the text's form of item 2** up to the names of the variables, free and bound
(kernel), and is not the item. -/
theorem same2 : TieAlpha.acEqB text2 (trS U.ax213).pat = true := by decide +kernel
theorem differs2 : item2 ≠ (trS U.ax213).pat := by decide +kernel

/-- **E for sentence 213**: Γ entails it, for every H; of the model only definedness is read. -/
theorem s213_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax213).pat := by
  intro M _ I hI
  exact (TieAlpha.acEqB_sat same2).mp
    (TieCutEq.cutEq_entailed_pure (defOK hI) text2_eq shape2 (fnItem_sat hI ax2_at))

/-- **Sentence 213 gives Γ's item 2** in a model with the constructors' facts, for every H. -/
theorem s213_from_text (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (h : I ⊧ᴵ (trS U.ax213).pat) : I ⊧ᴵ item2 :=
  TieCutEq.cutEq_from_text (k := .andApp [0, 0]) N (sortOf_true H) (fun h => nomatch h) text2_eq shape2
    ((TieCutEq.factsOK_withHooks c H _ _ _).trans facts2) ((TieAlpha.acEqB_sat same2).mpr h)

end ReqAndApp

/-! ## `notAsCondition`: e3-ml-eq-req-not -/

namespace ReqNot

kore_term kore from "f2-examples/mleqreqnot.kompile.kore"
definition_of defn from "f2-examples/mleqreqnot.kompile.kore"
user_axioms U from "f2-examples/mleqreqnot.kompile.kore" module "E3-ML-EQ-REQ-NOT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
/-- The definition reads no confined sort: its theory is Γ, without the closure of Bool. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem sortOf_true (H : HookParams) : (cH H).sortOf (KCore.bool true) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel
theorem sortOf_false (H : HookParams) : (cH H).sortOf (KCore.bool false) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel

/-- A model of Γ has the constructors' facts. -/
theorem nodeFacts (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : HoldsShape.NodeFacts (cH H) I :=
  HoldsShape.nodeFacts_of_core (coreOKH H)
    (by rw [Γc_plain ((Semantics.readsConfined_withHooks c H).trans readsConfined_c)]; exact hI)

/-- Γ's axiom of item 0, the equation `f(X) => 1` with the predicate `X >Int 0 = false`. -/
noncomputable def ax0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax0_at : (TiePair.fnAxioms c)[0]? = some ax0 := by decide +kernel
noncomputable def item0 : P := (trAxiom [] [] ⟨0, "kernel", ax0⟩).pat
/-- The text's form of item 0: the `requires` `\not{SortBool{}}(X >Int 0)`. -/
noncomputable def text0 : P := (TieCutEq.textItem .notCond .own ax0).getD .bottom
kernel_rfl text0_eq : TieCutEq.textItem .notCond .own ax0 = some text0
theorem shape0 : TieCutEq.shapeOK .notCond .own ax0 = true := by decide +kernel
theorem facts0 : TieCutEq.factsOK c .notCond .own ax0 = true := by decide +kernel
/-- **Sentence 209 is the text's form of item 0** up to the names of the variables (kernel), and
is not the item. -/
theorem same0 : TieAlpha.acEqB text0 (trS U.ax209).pat = true := by decide +kernel
theorem differs0 : item0 ≠ (trS U.ax209).pat := by decide +kernel

/-- **Sentence 209 and Γ's item 0 hold in the same models** among those with the constructors'
facts in which every element of Bool is `true` or `false`, for every H. -/
theorem s209_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hcl : I ⊧ᴵ boolClosed (cH H)) :
    (I ⊧ᴵ (trS U.ax209).pat) ↔ (I ⊧ᴵ item0) :=
  (TieAlpha.acEqB_sat same0).symm.trans (TieCutEq.cutEq_iff N (sortOf_true H)
    (fun _ => ⟨sortOf_false H, hcl⟩) text0_eq shape0 ((TieCutEq.factsOK_withHooks c H _ _ _).trans facts0))

/-- Sentence 209 holds in a model of Γ in which Bool is closed, for every H. -/
theorem s209_entailed (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) : I ⊧ᴵ (trS U.ax209).pat :=
  (s209_iff H (nodeFacts H hI) hcl).mpr (fnItem_sat hI ax0_at)

/-- Γ's axiom of item 1, the `[owise]` equation under the negation of item 0's premise. -/
noncomputable def ax1 : Kore.Axiom := ((TiePair.fnAxioms c)[1]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax1_at : (TiePair.fnAxioms c)[1]? = some ax1 := by decide +kernel
noncomputable def item1 : P := (trAxiom [] [] ⟨0, "kernel", ax1⟩).pat
/-- The text's form of item 1: the cut premise is the first competitor's, under its binder. -/
noncomputable def text1 : P := (TieCutEq.textItem .notCond (.under 0 1) ax1).getD .bottom
kernel_rfl text1_eq : TieCutEq.textItem .notCond (.under 0 1) ax1 = some text1
theorem shape1 : TieCutEq.shapeOK .notCond (.under 0 1) ax1 = true := by decide +kernel
theorem facts1 : TieCutEq.factsOK c .notCond (.under 0 1) ax1 = true := by decide +kernel
/-- **Sentence 210 is the text's form of item 1** up to the names of the variables, free and bound
(kernel), and is not the item. -/
theorem same1 : TieAlpha.acEqB text1 (trS U.ax210).pat = true := by decide +kernel
theorem differs1 : item1 ≠ (trS U.ax210).pat := by decide +kernel

/-- **Sentence 210 and Γ's item 1 hold in the same models** among those with the constructors'
facts in which every element of Bool is `true` or `false`, for every H. -/
theorem s210_iff (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (N : HoldsShape.NodeFacts (cH H) I) (hcl : I ⊧ᴵ boolClosed (cH H)) :
    (I ⊧ᴵ (trS U.ax210).pat) ↔ (I ⊧ᴵ item1) :=
  (TieAlpha.acEqB_sat same1).symm.trans (TieCutEq.cutEq_iff N (sortOf_true H)
    (fun _ => ⟨sortOf_false H, hcl⟩) text1_eq shape1 ((TieCutEq.factsOK_withHooks c H _ _ _).trans facts1))

/-- Sentence 210 holds in a model of Γ in which Bool is closed, for every H. -/
theorem s210_entailed (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (hcl : I ⊧ᴵ boolClosed (cH H)) : I ⊧ᴵ (trS U.ax210).pat :=
  (s210_iff H (nodeFacts H hI) hcl).mpr (fnItem_sat hI ax1_at)

end ReqNot

end KCore.TieCutEqTest

#check @KCore.TieCutEq.cutEq_from_text_pure
#check @KCore.TieCutEq.cutEq_entailed_pure
#check @KCore.TieCutEq.cutEq_from_text
#check @KCore.TieCutEq.cutEq_entailed
#check @KCore.TieCutEq.cutEq_iff
#check @KCore.TieCutEqTest.ReqAndApp.s212_from_text
#check @KCore.TieCutEqTest.ReqAndApp.s212_entailed
#check @KCore.TieCutEqTest.ReqAndApp.s213_entailed
#check @KCore.TieCutEqTest.ReqAndApp.s213_from_text
#check @KCore.TieCutEqTest.ReqNot.s209_iff
#check @KCore.TieCutEqTest.ReqNot.s209_entailed
#check @KCore.TieCutEqTest.ReqNot.s210_iff
#check @KCore.TieCutEqTest.ReqNot.s210_entailed
#print axioms KCore.TieCutEq.cutEq_from_text_pure
#print axioms KCore.TieCutEq.cutEq_entailed_pure
#print axioms KCore.TieCutEq.cutEq_iff
#print axioms KCore.TieCutEqTest.ReqAndApp.s212_from_text
#print axioms KCore.TieCutEqTest.ReqAndApp.s212_entailed
#print axioms KCore.TieCutEqTest.ReqAndApp.s213_entailed
#print axioms KCore.TieCutEqTest.ReqAndApp.s213_from_text
#print axioms KCore.TieCutEqTest.ReqNot.s209_iff
#print axioms KCore.TieCutEqTest.ReqNot.s209_entailed
#print axioms KCore.TieCutEqTest.ReqNot.s210_iff
#print axioms KCore.TieCutEqTest.ReqNot.s210_entailed
