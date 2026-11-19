/-
  Part NoJunk of the tie (C14) on `f2-examples/e2-cells-stream.kompile.kore`, test/TieE2CellsStream.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e2-cells-stream --split`; run from the package root:
  `lake env lean -j1 test/TieE2CellsStreamNoJunk.lean`.

  Measured alone (LEAN_NUM_THREADS=1, `lake env lean -j1`, a 12G memory scope): 64 s, peak
  8.1 GiB.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE2CellsStream

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e2-cells-stream.kompile.kore"
definition_of defn from "f2-examples/e2-cells-stream.kompile.kore"
user_axioms U from "f2-examples/e2-cells-stream.kompile.kore" module "E2-CELLS-STREAM"
user_axioms PreludeKseq from "f2-examples/e2-cells-stream.kompile.kore" module "KSEQ"

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

theorem nj2757 : (trS U.ax2757).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj2759 : (trS U.ax2759).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj2770 : (trS U.ax2770).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj2773 : (trS U.ax2773).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel
theorem nj2778 : (trS U.ax2778).pat = orTopBot (sym (.sort "SortString")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax2757, U.ax2759, U.ax2770, U.ax2773, U.ax2778], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl | rfl
  · rw [nj2757]; exact orTopBot_valid hD rfl
  · rw [nj2759]; exact orTopBot_valid hD rfl
  · rw [nj2770]; exact orTopBot_valid hD rfl
  · rw [nj2773]; exact orTopBot_valid hD rfl
  · rw [nj2778]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax2758, U.ax2760, U.ax2761, U.ax2762, U.ax2763, U.ax2765, U.ax2768, U.ax2769, U.ax2771,
      U.ax2772, U.ax2775, U.ax2776, U.ax2779, U.ax2780, U.ax2781],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax2758, U.ax2760, U.ax2761, U.ax2762, U.ax2763, U.ax2765, U.ax2768, U.ax2769, U.ax2771,
      U.ax2772, U.ax2775, U.ax2776, U.ax2779, U.ax2780, U.ax2781],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax2774).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (2774)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax2774).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- IOError, a sort with generators. -/
def ioerror : Srt := 12

theorem ioerror_name : c.sortName ioerror = "IOError" := by decide +kernel

/-- IOError's generators in the order the text's no-junk sentence (2764) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def ioerrorTextGens : List KoreAML.Gen :=
  ([2, 3, 52, 53, 51, 4, 41, 5, 6, 7, 57, 65, 58, 8, 43, 9, 10, 11, 12, 66, 67, 40, 13, 14, 15, 60,
    16, 68, 17, 18, 44, 19, 54, 56, 55, 20, 59, 21, 22, 23, 24, 25, 46, 26, 27, 61, 28, 29, 42, 30,
    31, 0, 49, 69, 32, 50, 33, 47, 45, 34, 35, 62, 48, 36, 37, 64, 63, 39, 38, 70, 1] : List Nat).filterMap
    (((c.gens ioerror).map (Gen.toK c))[·]?)

/-- IOError's no-junk sentence (2764) is the item over IOError's generators in the text's order. -/
theorem nojunk_ioerror_order : (trS U.ax2764).pat = (KoreAML.Cons.noJunkItem (c.sortName ioerror) ioerrorTextGens).pat := by
  decide +kernel
theorem nojunk_ioerror_members : ioerrorTextGens.isPerm ((c.gens ioerror).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for IOError's no junk (2764)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_ioerror_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax2764).pat := by
  intro M _ I hI
  rw [nojunk_ioerror_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens ioerror).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_ioerror_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := ioerror)
    (show ioerror ∈ consSorts c by decide +kernel) (show (c.gens ioerror).isEmpty = false by decide +kernel), rfl⟩)

/-- IOInt, a sort with generators. -/
def ioint : Srt := 14

theorem ioint_name : c.sortName ioint = "IOInt" := by decide +kernel

/-- IOInt's no-junk sentence (2766) is the item over IOInt's generators in the text's order, the same
generators as `Semantics.gens` lists. -/
theorem nojunk_ioint_order : (trS U.ax2766).pat =
    (KoreAML.Cons.noJunkItem (c.sortName ioint) ((gensInOrder c defn.pres ioint).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_ioint_members :
    ((gensInOrder c defn.pres ioint).map (Gen.toK c)).isPerm ((c.gens ioint).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for IOInt's no junk (2766)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_ioint_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax2766).pat := by
  intro M _ I hI
  rw [nojunk_ioint_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens ioint).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_ioint_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := ioint)
    (show ioint ∈ consSorts c by decide +kernel) (show (c.gens ioint).isEmpty = false by decide +kernel), rfl⟩)

/-- IOString, a sort with generators. -/
def iostring : Srt := 15

theorem iostring_name : c.sortName iostring = "IOString" := by decide +kernel

/-- IOString's no-junk sentence (2767) is the item over IOString's generators in the text's order, the same
generators as `Semantics.gens` lists. -/
theorem nojunk_iostring_order : (trS U.ax2767).pat =
    (KoreAML.Cons.noJunkItem (c.sortName iostring) ((gensInOrder c defn.pres iostring).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_iostring_members :
    ((gensInOrder c defn.pres iostring).map (Gen.toK c)).isPerm ((c.gens iostring).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for IOString's no junk (2767)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_iostring_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax2767).pat := by
  intro M _ I hI
  rw [nojunk_iostring_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens iostring).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_iostring_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := iostring)
    (show iostring ∈ consSorts c by decide +kernel) (show (c.gens iostring).isEmpty = false by decide +kernel), rfl⟩)

/-- Stream, a sort with generators. -/
def stream : Srt := 16

theorem stream_name : c.sortName stream = "Stream" := by decide +kernel

/-- Stream's generators in the order the text's no-junk sentence (2777) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def streamTextGens : List KoreAML.Gen :=
  match (c.gens stream).map (Gen.toK c) with
  | [g0, g1, g2, g3] => [g0, g1, g3, g2]
  | gs => gs

/-- Stream's no-junk sentence (2777) is the item over Stream's generators in the text's order. -/
theorem nojunk_stream_order : (trS U.ax2777).pat = (KoreAML.Cons.noJunkItem (c.sortName stream) streamTextGens).pat := by
  decide +kernel
theorem nojunk_stream_members : streamTextGens.isPerm ((c.gens stream).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for Stream's no junk (2777)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_stream_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax2777).pat := by
  intro M _ I hI
  rw [nojunk_stream_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens stream).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_stream_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := stream)
    (show stream ∈ consSorts c by decide +kernel) (show (c.gens stream).isEmpty = false by decide +kernel), rfl⟩)

end KCore.TieE2CellsStream

#check @KCore.TieE2CellsStream.nojunk_trivial_entailed
#check @KCore.TieE2CellsStream.nojunk_items_entailed
#check @KCore.TieE2CellsStream.nojunk_kitem_entailed
#check @KCore.TieE2CellsStream.nojunk_ioerror_order
#check @KCore.TieE2CellsStream.nojunk_ioerror_members
#check @KCore.TieE2CellsStream.nojunk_ioerror_entailed
#check @KCore.TieE2CellsStream.nojunk_ioint_order
#check @KCore.TieE2CellsStream.nojunk_ioint_members
#check @KCore.TieE2CellsStream.nojunk_ioint_entailed
#check @KCore.TieE2CellsStream.nojunk_iostring_order
#check @KCore.TieE2CellsStream.nojunk_iostring_members
#check @KCore.TieE2CellsStream.nojunk_iostring_entailed
#check @KCore.TieE2CellsStream.nojunk_stream_order
#check @KCore.TieE2CellsStream.nojunk_stream_members
#check @KCore.TieE2CellsStream.nojunk_stream_entailed
#print axioms KCore.TieE2CellsStream.nojunk_trivial_entailed
#print axioms KCore.TieE2CellsStream.nojunk_items_entailed
#print axioms KCore.TieE2CellsStream.nojunk_kitem_entailed
#print axioms KCore.TieE2CellsStream.nojunk_ioerror_order
#print axioms KCore.TieE2CellsStream.nojunk_ioerror_members
#print axioms KCore.TieE2CellsStream.nojunk_ioerror_entailed
#print axioms KCore.TieE2CellsStream.nojunk_ioint_order
#print axioms KCore.TieE2CellsStream.nojunk_ioint_members
#print axioms KCore.TieE2CellsStream.nojunk_ioint_entailed
#print axioms KCore.TieE2CellsStream.nojunk_iostring_order
#print axioms KCore.TieE2CellsStream.nojunk_iostring_members
#print axioms KCore.TieE2CellsStream.nojunk_iostring_entailed
#print axioms KCore.TieE2CellsStream.nojunk_stream_order
#print axioms KCore.TieE2CellsStream.nojunk_stream_members
#print axioms KCore.TieE2CellsStream.nojunk_stream_entailed
