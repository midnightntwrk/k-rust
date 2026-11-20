/-
  The function equation of a construct fixture whose argument pattern Γ reads through the cut of an
  application, tied to the text's sentence with `KcoreSpec/TieEqArgCut.lean`, on the literals
  `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieEqArgCut.lean`.

  `f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore` (fixture e8-llvm-e2-open-mixed-clause):
  `first(X & _) => X`, `&` declared `functional` and no constructor, an open generator of the
  definition (`params_raw`). The text writes the argument's membership `X0 ∈ and(X, _Gen0)`; Γ
  writes `X0 ∈ V` with the membership `V ∈ and(X, _Gen0)` as the premise's last conjunct
  (`Parse.ovlCutList`).
  - Sentence 100 (the equation; Γ's item 0): the text's form of the item is the sentence up to the
    names of the variables (`same0`), and is not the item (`differs0`). The sentence gives the
    item in every model of definedness (`s100_from_text`); Γ entails the sentence, for every H
    (`s100_entailed`), reading of the model definedness, `⌈_⌉` and that B is a sort; in a model of
    Γ the two hold together (`s100_tie`). Neither direction reads a fact about `and`: the cut is
    the whole argument pattern, so the element of `and(X, _Gen0)` in V's place is X0's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieEqArgCutTest

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
definition_of defn from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore"
user_axioms U from "f2-examples/e8-llvm-e2-open-mixed-clause.kompile.kore" module "E2-OPEN-MIXED-CLAUSE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- B, the sort of `and` and of the argument of `first`. -/
def b : Srt := 32

theorem b_name : c.sortName b = "B" := by decide +kernel
theorem b_numbered (H : HookParams) : b < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : b < nRegSorts + c.sortNames.length)

/-- **The definition's one open generator is `and`**, of two arguments of A, of B. -/
theorem params_raw : (c.params.filter (·.raw)).map (fun k => (c.symName k.sig.name, k.sig.args.map c.sortName,
    c.sortName k.sig.result)) = [("Lbland", ["A", "A"], "B")] := by decide +kernel

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

/-- Γ's axiom of item 0, the equation `first(X0) = X` under `X0 ∈ V` and `V ∈ and(X, _Gen0)`. -/
noncomputable def ax0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
theorem ax0_at : (TiePair.fnAxioms c)[0]? = some ax0 := by decide +kernel
noncomputable def item0 : P := (trAxiom [] [] ⟨0, "kernel", ax0⟩).pat

/-- The parts of item 0: the argument's membership is the first operand of the second operand of
the premise's first conjunct, and the variable is the whole of its pattern. -/
noncomputable def pt : TieEqArgCut.Parts := ((TieEqArgCut.partsOf [1, 0] [] ax0)).getD
  ⟨KoreAML.R, .top KoreAML.R, KoreAML.R, [], KoreAML.R, KoreAML.R, ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .hole, KoreAML.R,
    ⟨⟨⟨""⟩⟩, KoreAML.R⟩, .top KoreAML.R⟩
kernel_rfl parts0 : TieEqArgCut.partsOf [1, 0] [] ax0 = some pt
/-- The variable is of B, and the application cut is `and` at two variables of A. -/
theorem parts0_cut : pt.S = KoreAML.srt "B" ∧ pt.Sx = KoreAML.srt "B" ∧
    pt.φ = .app ⟨⟨"Lbland"⟩⟩ [] [.var (.evar ⟨⟨⟨"VarV0"⟩⟩, KoreAML.srt "A"⟩), .var (.evar ⟨⟨⟨"VarV1"⟩⟩, KoreAML.srt "A"⟩)] := by
  decide +kernel

/-- The text's form of item 0: `and(X, _Gen0)` in the variable's place, and no membership of it. -/
noncomputable def text0 : P := TieEqArgCut.textItemOf ax0 pt
theorem sub0 : TieEqArgCut.subOK ax0 pt = true := by decide +kernel
theorem fresh0 : TieEqArgCut.freshOK ax0 pt = true := by decide +kernel
theorem top0 : TieEqArgCut.topOK pt = true := by decide +kernel
/-- **Sentence 100 is the text's form of item 0** up to the names of the variables (kernel), and
is not the item. -/
theorem same0 : TieAlpha.acEqB text0 (trS U.ax100).pat = true := by decide +kernel
theorem differs0 : item0 ≠ (trS U.ax100).pat := by decide +kernel

theorem sortB_tr : trSort (tableOf ax0.sortVars ax0.pattern) pt.S = sym (.sort "SortB") := by decide +kernel

/-- **Sentence 100 gives Γ's item 0** in every model of definedness. -/
theorem s100_from_text {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I)
    (h : I ⊧ᴵ (trS U.ax100).pat) : I ⊧ᴵ item0 :=
  TieEqArgCut.argCut_from_text hD parts0 sub0 ((TieAlpha.acEqB_sat same0).mpr h)

/-- **The tie of sentence 100**: in a model of Γ, the sentence and Γ's item 0 hold together, for
every H. -/
theorem s100_tie (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : (I ⊧ᴵ (trS U.ax100).pat) ↔ (I ⊧ᴵ item0) := by
  have hD := defOK hI
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ hφ => sat_sig hI hφ
  have hc : I ⊧ᴵ ceilDefItem.pat := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩))
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σB, hσB1, hσB2⟩ := TieRhs.sortSing_sig hD hSig (b_numbered H)
  rw [show (cH H).sortName b = "B" from b_name] at hσB1
  have hB : ∀ (e : Valuation M) a, (trSort (tableOf ax0.sortVars ax0.pattern) pt.S).interpret I e a ↔ a = σB :=
    fun e a => by rw [sortB_tr]; exact hσB1 a
  exact (TieAlpha.acEqB_sat same0).symm.trans (TieEqArgCut.argCut_iff_top hD hc parts0 sub0 fresh0 top0 hB hσB2)

/-- **E for sentence 100**: Γ entails it, for every H. -/
theorem s100_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax100).pat := by
  intro M _ I hI
  exact (s100_tie H hI).mpr (fnItem_sat hI ax0_at)

end KCore.TieEqArgCutTest

#check @KCore.TieEqArgCut.argCut_from_text
#check @KCore.TieEqArgCut.argCut_entailed
#check @KCore.TieEqArgCut.argCut_entailed_top
#check @KCore.TieEqArgCut.argCut_iff
#check @KCore.TieEqArgCut.argCut_iff_top
#check @KCore.TieEqArgCutTest.params_raw
#check @KCore.TieEqArgCutTest.parts0
#check @KCore.TieEqArgCutTest.parts0_cut
#check @KCore.TieEqArgCutTest.same0
#check @KCore.TieEqArgCutTest.differs0
#check @KCore.TieEqArgCutTest.s100_from_text
#check @KCore.TieEqArgCutTest.s100_tie
#check @KCore.TieEqArgCutTest.s100_entailed
#print axioms KCore.TieEqArgCutTest.s100_from_text
#print axioms KCore.TieEqArgCutTest.s100_tie
#print axioms KCore.TieEqArgCutTest.s100_entailed
