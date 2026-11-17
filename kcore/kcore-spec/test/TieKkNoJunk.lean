/-
  The no-junk sentences of kore.k's text as kompile wrote it
  (`examples/ref-kk/RefKk/definition.kore`, user module `KORE`), layer 2 of the tie (C14), on the
  literals `kore` and `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package
  root: `lake env lean test/TieKkNoJunk.lean`.

  The account's 28 no-junk sentences (test/TieKk.lean, `classes`), each entailed by Γ for every H:
  - `nojunk_items`: the 22 of the sorts with generators other than KItem are the patterns of
    Γ's constructor items;
  - `nojunk_trivial_entailed`: the 5 of the sorts without constructors (Bool, Float, Int, KConfigVar,
    String: 352, 355, 361, 364, 375) are `\or{S}(\top{S}(), \bottom{S}())`, valid in any model
    of definedness;
  - `nojunk_kitem_entailed`: KItem's (365) is Γ's item over the same generators in another order.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKk

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kk/RefKk/definition.kore"
definition_of defn from "examples/ref-kk/RefKk/definition.kore"
user_axioms U from "examples/ref-kk/RefKk/definition.kore" module "KORE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The no-junk sentences that are Γ's constructor items. -/
noncomputable def njItems : List AxiomDecl :=
    [U.ax351, U.ax353, U.ax354, U.ax356, U.ax357, U.ax358, U.ax359, U.ax360, U.ax362, U.ax363,
     U.ax366, U.ax367, U.ax368, U.ax369, U.ax370, U.ax371, U.ax372, U.ax373, U.ax374, U.ax376,
     U.ax377, U.ax378]

/-- **No junk of the sorts with generators other than KItem**: the translation of each text
sentence is the pattern of one of Γ's constructor items. -/
theorem nojunk_items : njItems.all (fun ad => (consItemsK c).any (·.pat == (trS ad).pat)) = true := by
  decide +kernel

theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ njItems, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp nojunk_items ad had)
  exact sat_cons hI (Or.inl ⟨it, hit, (beq_iff_eq.mp he)⟩)

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

theorem nj352 : (trS U.ax352).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj355 : (trS U.ax355).pat = orTopBot (sym (.sort "SortFloat")) := by decide +kernel
theorem nj361 : (trS U.ax361).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj364 : (trS U.ax364).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel
theorem nj375 : (trS U.ax375).pat = orTopBot (sym (.sort "SortString")) := by decide +kernel

/-- **E for the sorts without constructors**: entailed by Γ (by any theory with definedness), for
every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax352, U.ax355, U.ax361, U.ax364, U.ax375], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl | rfl
  · rw [nj352]; exact orTopBot_valid hD rfl
  · rw [nj355]; exact orTopBot_valid hD rfl
  · rw [nj361]; exact orTopBot_valid hD rfl
  · rw [nj364]; exact orTopBot_valid hD rfl
  · rw [nj375]; exact orTopBot_valid hD rfl

/-- KItem's (365) is the item over KItem's generators in the text's order (`gensInOrder`), the
same generators as `Semantics.gens` lists, in another order. -/
theorem nojunk_kitem_order : (trS U.ax365).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by
  decide +kernel
theorem nojunk_kitem_members :
    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by
  decide +kernel

/-- **E for 365**: Γ entails KItem's no-junk sentence, for every H (`noJunkItem_of_subset`). -/
theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax365).pat := by
  intro M _ I hI
  rw [nojunk_kitem_order]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)
    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)

end KCore.TieKk

#print axioms KCore.TieKk.nojunk_items_entailed
#print axioms KCore.TieKk.nojunk_trivial_entailed
#print axioms KCore.TieKk.nojunk_kitem_entailed
