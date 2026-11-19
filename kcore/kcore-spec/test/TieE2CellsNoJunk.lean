/-
  Part NoJunk of the tie (C14) on `f2-examples/e2-cells.kompile.kore`, test/TieE2Cells.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsNoJunk.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2Cells

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells.kompile.kore"
definition_of defn from "f2-examples/e2-cells.kompile.kore"
user_axioms U from "f2-examples/e2-cells.kompile.kore" module "E2-CELLS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## No junk -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj262 : (trS U.ax262).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj272 : (trS U.ax272).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj275 : (trS U.ax275).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax262, U.ax272, U.ax275], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · rw [nj262]; exact orTopBot_valid hD rfl
  · rw [nj272]; exact orTopBot_valid hD rfl
  · rw [nj275]; exact orTopBot_valid hD rfl

/-- The text's alias names, written out. -/
def aliasLit : List String := ["weakExistsFinally", "weakAlwaysFinally", "allPathGlobally"]

theorem aliasLit_eq : kore.aliasNames = aliasLit := by decide +kernel

/-- The no-junk sentences that are Γ's constructor items, each with the sort whose no-junk item
over `Semantics.gens` it is. -/
noncomputable def njEq : List (AxiomDecl × Srt) :=
  [(U.ax263, 45), (U.ax264, 46), (U.ax265, 59), (U.ax266, 19), (U.ax267, 20), (U.ax268, 17),
   (U.ax269, 18), (U.ax270, 50), (U.ax271, 58), (U.ax273, 33), (U.ax274, 34), (U.ax277, 60),
   (U.ax278, 53), (U.ax279, 43), (U.ax280, 52), (U.ax281, 44), (U.ax282, 54), (U.ax284, 41),
   (U.ax285, 55), (U.ax286, 42), (U.ax287, 57), (U.ax288, 56), (U.ax290, 35), (U.ax291, 36),
   (U.ax293, 38), (U.ax294, 30), (U.ax295, 32), (U.ax296, 31), (U.ax297, 51), (U.ax298, 48),
   (U.ax300, 39), (U.ax301, 47), (U.ax302, 40), (U.ax303, 61), (U.ax304, 49)]

/-- The sentence `p.1` translates (with the alias names written out) to the no-junk item of the sort
`p.2` over `Semantics.gens`, and `p.2` is a constructor sort with generators. -/
noncomputable def njEqB (p : AxiomDecl × Srt) : Bool :=
  decide ((trAxiom kore.symbolDecls aliasLit p.1).pat =
      (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat) &&
    decide (p.2 ∈ consSorts c) && !(c.gens p.2).isEmpty

theorem njEq_all : njEq.all njEqB = true := by decide +kernel

/-- A sentence `njEqB` holds of is Γ's no-junk item of its sort, an item of `consItemsK c`
(`tnjItem_any_of_eq`). -/
theorem njEq_any {l : List (AxiomDecl × Srt)} (h : l.all njEqB = true) :
    ∀ ad ∈ l.map (·.1), (consItemsK c).any (·.pat == (trS ad).pat) = true := by
  intro ad had
  obtain ⟨⟨ad', N⟩, hm, rfl⟩ := List.mem_map.mp had
  have hb := List.all_eq_true.mp h _ hm
  simp only [njEqB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
  obtain ⟨⟨he, hN⟩, hg⟩ := hb
  rw [← aliasLit_eq] at he
  exact tnjItem_any_of_eq hN hg he

/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items, its sort's no-junk item (`njEq_any`). -/
theorem nojunk_items : ∀ ad ∈ [U.ax263, U.ax264, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269, U.ax270, U.ax271, U.ax273,
      U.ax274, U.ax277, U.ax278, U.ax279, U.ax280, U.ax281, U.ax282, U.ax284, U.ax285, U.ax286,
      U.ax287, U.ax288, U.ax290, U.ax291, U.ax293, U.ax294, U.ax295, U.ax296, U.ax297, U.ax298,
      U.ax300, U.ax301, U.ax302, U.ax303, U.ax304],
    (consItemsK c).any (·.pat == (trS ad).pat) = true :=
  njEq_any njEq_all

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax263, U.ax264, U.ax265, U.ax266, U.ax267, U.ax268, U.ax269, U.ax270, U.ax271, U.ax273,
      U.ax274, U.ax277, U.ax278, U.ax279, U.ax280, U.ax281, U.ax282, U.ax284, U.ax285, U.ax286,
      U.ax287, U.ax288, U.ax290, U.ax291, U.ax293, U.ax294, U.ax295, U.ax296, U.ax297, U.ax298,
      U.ax300, U.ax301, U.ax302, U.ax303, U.ax304],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax276).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (276)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax276).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- OptCell, a sort with generators. -/
def optcell : Srt := 37

theorem optcell_name : c.sortName optcell = "OptCell" := by decide +kernel

/-- OptCell's generators in the order the text's no-junk sentence (292) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def optcellTextGens : List KoreAML.Gen :=
  match (c.gens optcell).map (Gen.toK c) with
  | [g0, g1] => [g1, g0]
  | gs => gs

/-- OptCell's no-junk sentence (292) is the item over OptCell's generators in the text's order. -/
theorem nojunk_optcell_order : (trS U.ax292).pat = (KoreAML.Cons.noJunkItem (c.sortName optcell) optcellTextGens).pat := by
  decide +kernel
theorem nojunk_optcell_members : optcellTextGens.isPerm ((c.gens optcell).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for OptCell's no junk (292)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_optcell_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax292).pat := by
  intro M _ I hI
  rw [nojunk_optcell_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens optcell).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_optcell_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := optcell)
    (show optcell ∈ consSorts c by decide +kernel) (show (c.gens optcell).isEmpty = false by decide +kernel), rfl⟩)

end KCore.TieE2Cells

#check @KCore.TieE2Cells.nojunk_trivial_entailed
#check @KCore.TieE2Cells.nojunk_items_entailed
#check @KCore.TieE2Cells.nojunk_kitem_entailed
#check @KCore.TieE2Cells.nojunk_optcell_order
#check @KCore.TieE2Cells.nojunk_optcell_members
#check @KCore.TieE2Cells.nojunk_optcell_entailed
#print axioms KCore.TieE2Cells.nojunk_trivial_entailed
#print axioms KCore.TieE2Cells.nojunk_items_entailed
#print axioms KCore.TieE2Cells.nojunk_kitem_entailed
#print axioms KCore.TieE2Cells.nojunk_optcell_order
#print axioms KCore.TieE2Cells.nojunk_optcell_members
#print axioms KCore.TieE2Cells.nojunk_optcell_entailed
