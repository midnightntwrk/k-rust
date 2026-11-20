/-
  The function equation of construct fixture e5-ovl-fun-clause whose argument pattern Γ reads
  through the cut of an application, tied to the text's sentence with `KcoreSpec/TieEqArgCut.lean`,
  on the literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the
  package root: `lake env lean -j1 test/TieE5OvlFunClauseCut.lean`.

  `f2-examples/e5-ovl-fun-clause.kompile.kore`: `uncap(cap(G)) => G`, `cap` at Gas the symbol
  `capGas`, which overloads the function `capN`. The text writes the argument's membership
  `X0 ∈ capGas(G)`; Γ writes `X0 ∈ V` with the membership `V ∈ capGas(G)` as the premise's last
  conjunct (`Parse.ovlCutList`).
  - Sentence 156 (the equation; Γ's item 1): the text's form of the item is the sentence up to the
    names of the variables (`same1`), and is not the item (`differs1`).
  - The sentence gives the item in every model of definedness (`s156_from_text`); as an
    entailment, from the sentence with definedness and nothing else (`s156_from_text_texts`,
    `s156_item`: the statement of the tie's `fns_from_text` at the index it leaves out).
  - Γ entails the sentence, for every H (`s156_entailed`; over `Γc`, `s156_entailed_c`), reading
    of the model definedness, `⌈_⌉` and that Gas is a sort; in a model of Γ the two hold together
    (`s156_tie`).
  Neither direction reads a fact about `capGas`: the cut is the whole argument pattern, so the
  element of `capGas(G)` in V's place is X0's. What Γ holds of `capGas` (its value at the
  arguments `capN` covers, its sentences at the others) is not read.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunClauseCut

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-clause.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-clause.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-clause.kompile.kore" module "E5-OVL-FUN-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- Gas, the sort of `capGas` and of the argument of `uncap`. -/
def gas : Srt := 32

theorem gas_name : c.sortName gas = "Gas" := by decide +kernel
theorem gas_numbered (H : HookParams) : gas < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : gas < nRegSorts + c.sortNames.length)

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

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

/-- Γ's axiom of item 1, the equation `uncap(X0) = G` under `X0 ∈ V` and `V ∈ capGas(G)`. -/
noncomputable def ax1 : Kore.Axiom := ((TiePair.fnAxioms c)[1]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax1_at : (TiePair.fnAxioms c)[1]? = some ax1 := by decide +kernel
noncomputable def item1 : P := (trAxiom [] [] ⟨0, "kernel", ax1⟩).pat
/-- `item1` is the pattern of Γ's item 1, in `fnItems`'s order. -/
theorem item1_at : (TiePair.gammaPats c)[1]? = some item1 := TiePair.gammaPats_at ax1_at

/-- The parts of item 1: the argument's membership is the first operand of the second operand of
the premise's first conjunct, and the variable is the whole of its pattern. -/
noncomputable def pt : TieEqArgCut.Parts := ((TieEqArgCut.partsOf [1, 0] [] ax1)).getD
  ⟨KoreAML.R, .top KoreAML.R, KoreAML.R, [], KoreAML.R, KoreAML.R, ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .hole, KoreAML.R,
    ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .top KoreAML.R⟩
kernel_rfl parts1 : TieEqArgCut.partsOf [1, 0] [] ax1 = some pt

/-- The text's form of item 1: `capGas(G)` in the variable's place, and no membership of it. -/
noncomputable def text1 : P := TieEqArgCut.textItemOf ax1 pt
theorem sub1 : TieEqArgCut.subOK ax1 pt = true := by decide +kernel
theorem fresh1 : TieEqArgCut.freshOK ax1 pt = true := by decide +kernel
theorem top1 : TieEqArgCut.topOK pt = true := by decide +kernel
/-- **Sentence 156 is the text's form of item 1** up to the names of the variables (kernel), and
is not the item. -/
theorem same1 : TieAlpha.acEqB text1 (trS U.ax156).pat = true := by decide +kernel
theorem differs1 : item1 ≠ (trS U.ax156).pat := by decide +kernel

theorem sortGas_tr : trSort (tableOf ax1.sortVars ax1.pattern) pt.S = sym (.sort "SortGas") := by decide +kernel

/-- **Sentence 156 gives Γ's item 1** in every model of definedness. -/
theorem s156_from_text {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax156).pat) : I ⊧ᴵ item1 :=
  TieEqArgCut.argCut_from_text hD parts1 sub1 ((TieAlpha.acEqB_sat same1).mpr h)

/-- **Γ's item 1 is a consequence of sentence 156**, with definedness and no other premise. -/
theorem s156_from_text_texts : TiePair.Texts [(trS U.ax156).pat] ⊧ item1 := by
  intro M _ I hI
  exact s156_from_text (defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)) (hI _ (Or.inl (List.mem_singleton_self _)))

/-- **The item of `fnItems` at index 1 is a consequence of sentence 156**, for every H. -/
theorem s156_item (H : HookParams) : ∀ it : Item, (fnItems (cH H))[1]? = some it →
    TiePair.Texts [(trS U.ax156).pat] ⊧ it.pat := by
  intro it hj
  rw [TiePair.fnItems_withHooks] at hj
  have hg : (TiePair.gammaPats c)[1]? = some it.pat := by
    unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
  rw [Option.some.inj (hg.symm.trans item1_at)]
  intro M _ I hI
  exact s156_from_text_texts hI

/-- **The tie of sentence 156**: in a model of Γ, the sentence and Γ's item 1 hold together, for
every H. -/
theorem s156_tie (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : (I ⊧ᴵ (trS U.ax156).pat) ↔ (I ⊧ᴵ item1) := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σG, hσG1, hσG2⟩ := TieRhs.sortSing_sig hD hSig (gas_numbered H)
  rw [show (cH H).sortName gas = "Gas" from gas_name] at hσG1
  have hG : ∀ (e : Valuation M) a, (trSort (tableOf ax1.sortVars ax1.pattern) pt.S).interpret I e a ↔ a = σG :=
    fun e a => by rw [sortGas_tr]; exact hσG1 a
  exact (TieAlpha.acEqB_sat same1).symm.trans (TieEqArgCut.argCut_iff_top hD hc parts1 sub1 fresh1 top1 hG hσG2)

/-- **E for sentence 156**: Γ entails it, for every H. -/
theorem s156_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax156).pat := by
  intro M _ I hI
  exact (s156_tie H hI).mpr (fnItem_sat hI ax1_at)

/-- **Over `Γc`**, the theory the statements are about: a model of `Γc` is one of Γ. -/
theorem s156_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax156).pat := by
  intro M _ I hI
  exact s156_entailed H (fun φ hφ => hI φ (Or.inl hφ))

/-- The variable is of Gas, and the application cut is `capGas` at a variable of Gas. -/
theorem parts1_cut : pt.S = KoreAML.srt "Gas" ∧ pt.Sx = KoreAML.srt "Gas" ∧
    pt.φ = .app ⟨⟨"LblcapGas"⟩⟩ [] [.var (.evar ⟨⟨⟨"VarV0"⟩⟩, KoreAML.srt "Gas"⟩)] := by
  decide +kernel

end KCore.TieE5OvlFunClauseCut

#check @KCore.TieE5OvlFunClauseCut.parts1
#check @KCore.TieE5OvlFunClauseCut.parts1_cut
#check @KCore.TieE5OvlFunClauseCut.same1
#check @KCore.TieE5OvlFunClauseCut.differs1
#check @KCore.TieE5OvlFunClauseCut.item1_at
#check @KCore.TieE5OvlFunClauseCut.s156_from_text
#check @KCore.TieE5OvlFunClauseCut.s156_from_text_texts
#check @KCore.TieE5OvlFunClauseCut.s156_item
#check @KCore.TieE5OvlFunClauseCut.s156_tie
#check @KCore.TieE5OvlFunClauseCut.s156_entailed
#check @KCore.TieE5OvlFunClauseCut.s156_entailed_c
#print axioms KCore.TieE5OvlFunClauseCut.s156_from_text
#print axioms KCore.TieE5OvlFunClauseCut.s156_from_text_texts
#print axioms KCore.TieE5OvlFunClauseCut.s156_item
#print axioms KCore.TieE5OvlFunClauseCut.s156_tie
#print axioms KCore.TieE5OvlFunClauseCut.s156_entailed
#print axioms KCore.TieE5OvlFunClauseCut.s156_entailed_c
