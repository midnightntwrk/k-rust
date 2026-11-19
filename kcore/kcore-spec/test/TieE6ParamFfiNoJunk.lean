/-
  Part NoJunk of the tie (C14) on `f2-examples/e6-param-ffi.kompile.kore`, test/TieE6ParamFfi.lean: the sections
  `--split` puts here, in the tie's namespace. A test file imports no test file, so this one
  repeats the literals and the definitions and facts it reads. Written by
  `test/constructs/tiegen.py e6-param-ffi --split`; run from the package root:
  `lake env lean -j1 test/TieE6ParamFfiNoJunk.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamFfi

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-ffi.kompile.kore"
definition_of defn from "f2-examples/e6-param-ffi.kompile.kore"
user_axioms U from "f2-examples/e6-param-ffi.kompile.kore" module "E6-PARAM-FFI"
user_axioms PreludeKseq from "f2-examples/e6-param-ffi.kompile.kore" module "KSEQ"

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

theorem nj480 : (trS U.ax480).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj481 : (trS U.ax481).pat = orTopBot (sym (.sort "SortBytes")) := by decide +kernel
theorem nj484 : (trS U.ax484).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj489 : (trS U.ax489).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj492 : (trS U.ax492).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel
theorem nj495 : (trS U.ax495).pat = orTopBot (sym (.sort "SortString")) := by decide +kernel

/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by
Γ for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax480, U.ax481, U.ax484, U.ax489, U.ax492, U.ax495], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [nj480]; exact orTopBot_valid hD rfl
  · rw [nj481]; exact orTopBot_valid hD rfl
  · rw [nj484]; exact orTopBot_valid hD rfl
  · rw [nj489]; exact orTopBot_valid hD rfl
  · rw [nj492]; exact orTopBot_valid hD rfl
  · rw [nj495]; exact orTopBot_valid hD rfl

set_option maxHeartbeats 1000000 in
/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of
one of Γ's constructor items. -/
theorem nojunk_items : ∀ ad ∈ [U.ax483, U.ax485, U.ax486, U.ax487, U.ax488, U.ax490, U.ax491, U.ax494],
    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- **E for those**: Γ entails each, for every H. -/
theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ [U.ax483, U.ax485, U.ax486, U.ax487, U.ax488, U.ax490, U.ax491, U.ax494],
    Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same
generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax493).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for KItem's no junk (493)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax493).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

/-- Endianness, a sort with generators. -/
def endianness : Srt := 22

theorem endianness_name : c.sortName endianness = "Endianness" := by decide +kernel

/-- Endianness's generators in the order the text's no-junk sentence (482) lists them, a permutation
of those `Semantics.gens` lists. -/
noncomputable def endiannessTextGens : List KoreAML.Gen :=
  match (c.gens endianness).map (Gen.toK c) with
  | [g0, g1] => [g1, g0]
  | gs => gs

/-- Endianness's no-junk sentence (482) is the item over Endianness's generators in the text's order. -/
theorem nojunk_endianness_order : (trS U.ax482).pat = (KoreAML.Cons.noJunkItem (c.sortName endianness) endiannessTextGens).pat := by
  decide +kernel
theorem nojunk_endianness_members : endiannessTextGens.isPerm ((c.gens endianness).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for Endianness's no junk (482)**, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_endianness_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax482).pat := by
  intro M _ I hI
  rw [nojunk_endianness_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens endianness).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_endianness_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := endianness)
    (show endianness ∈ consSorts c by decide +kernel) (show (c.gens endianness).isEmpty = false by decide +kernel), rfl⟩)

end KCore.TieE6ParamFfi

#check @KCore.TieE6ParamFfi.nojunk_trivial_entailed
#check @KCore.TieE6ParamFfi.nojunk_items_entailed
#check @KCore.TieE6ParamFfi.nojunk_kitem_entailed
#check @KCore.TieE6ParamFfi.nojunk_endianness_order
#check @KCore.TieE6ParamFfi.nojunk_endianness_members
#check @KCore.TieE6ParamFfi.nojunk_endianness_entailed
#print axioms KCore.TieE6ParamFfi.nojunk_trivial_entailed
#print axioms KCore.TieE6ParamFfi.nojunk_items_entailed
#print axioms KCore.TieE6ParamFfi.nojunk_kitem_entailed
#print axioms KCore.TieE6ParamFfi.nojunk_endianness_order
#print axioms KCore.TieE6ParamFfi.nojunk_endianness_members
#print axioms KCore.TieE6ParamFfi.nojunk_endianness_entailed
