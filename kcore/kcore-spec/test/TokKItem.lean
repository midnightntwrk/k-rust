/-
  `ReadingNote.tokKItem` on `f2-examples/hashsort.kompile.kore` (`hashsort.k`: `syntax #Tok [token]`,
  `syntax Exp ::= Int | tok(#Tok)`), stated on the literal `defn` and the text's sentence as written
  (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`, as `Theory.ofDefinition` translates it). Run
  from the package root: `lake env lean -j1 test/TokKItem.lean`.

  The text's KItem no-junk sentence (axiom 125; HASHSORT sentence 263, account sentence 278) lists
  13 injections and not `inj{#Tok, KItem}`, no subsort axiom states `#Tok < KItem`, and the
  equations of `is#Tok` apply `inj{#Tok, KItem}`. The definition holds `#Tok` below KItem
  (`tok_sub`): the reading adds the subsort, and `Γ`'s no-junk item of KItem lists 14 generators.
  - `text_entails_item`: the sentence entails that item, in every interpretation with definedness
    (no interpretation of the parameters read); `item_in_gamma`: the item is `Γ`'s, for every H.
  - `tok_refuted`: for every H, `Γ (c.withHooks H)` with the sentence has no model
    (`Faithful.noJunk_omitted_refuted`: `inj{#Tok, KItem}(\dv{#Tok}("x"))` is an element of KItem
    apart from the images of the 13 injections, by Cons-Fun and Cons-Dist).
  - `consistent`: for every H, `Γ (c.withHooks H)` has a model with the step's closure; so `Γ` does
    not entail the sentence (`text_not_entailed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TokKItem

open KCore ML Faithful

kore_term kore from "f2-examples/hashsort.kompile.kore"
definition_of defn from "f2-examples/hashsort.kompile.kore"
user_axioms U from "f2-examples/hashsort.kompile.kore" module "HASHSORT"
noncomputable abbrev c : Semantics := defn.sem

/-- The text's sentence as written, translated (`Theory.ofDefinition`'s translation). -/
noncomputable def trS (ad : KoreAML.AxiomDecl) : KoreAML.Item := KoreAML.trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort `#Tok`. -/
noncomputable def tok : Srt := (c.userSorts.filter (c.sortName · == "'Hash'Tok")).headD 0

/-- The generators of KItem the text's sentence lists: KItem's generators in the text's order
(`gensInOrder`) but `inj{#Tok, KItem}`. -/
noncomputable def gsText : List Gen := (gensInOrder c defn.pres Srt.kitem).filter fun g => match g with
  | .inj b => b != tok
  | .ctor _ => true

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem tok_named : c.sortName tok = "'Hash'Tok" := by decide +kernel
/-- `#Tok` is a sort of the definition below KItem (`sortsBelowKItem`); the text states no subsort
axiom of it. -/
theorem tok_sub : (tok, Srt.kitem) ∈ c.subsorts := by decide +kernel
/-- Sentence 125 is the no-junk sentence of KItem over the generators `gsText`. -/
theorem nojunk_text : (trS U.ax125).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gsText.map (Gen.toK c))).pat := by decide +kernel
theorem gsText_sub : (gsText.map (Gen.toK c)).all (fun g => decide (g ∈ (c.gens Srt.kitem).map (Gen.toK c))) = true := by
  decide +kernel
theorem gsText_length : gsText.length + 1 = (c.gens Srt.kitem).length := by decide +kernel
theorem kitem_cons : Srt.kitem ∈ consSorts c := by decide +kernel
theorem kitem_gens : (c.gens Srt.kitem).isEmpty = false := by decide +kernel
theorem noFnOvl : c.fnOvlSyms = [] := by decide +kernel
/-- `inj{#Tok, KItem}` is a generator of KItem, not an open one. -/
theorem tok_gen : (c.gens Srt.kitem).any (fun g => match g with | .inj b => b == tok | .ctor _ => false) = true ∧
    c.isOpenGen (.inj tok) = false := by decide +kernel
/-- Each generator the text's sentence lists is an injection from a sort below KItem, a generator
of KItem that is not open, with no order and no lower bound shared with `#Tok`. -/
theorem gsText_apart : gsText.all (fun g => match g with
    | .inj b => (c.gens Srt.kitem).any (fun g' => match g' with | .inj b' => b' == b | .ctor _ => false) &&
        !c.isOpenGen (.inj b) && b != tok && !(c.le tok b || c.le b tok) &&
        (c.lowerBounds tok b).isEmpty && (c.lowerBounds b tok).isEmpty
    | .ctor _ => false) = true := by decide +kernel
/-- `\dv{#Tok}("x")` is a value of `#Tok`, and its injection a value of KItem. -/
theorem tok_value : c.sortOf (.dv tok (.tok "x")) = some tok := by decide +kernel
theorem tok_inj_value : c.sortOf (.inj tok Srt.kitem (.dv tok (.tok "x"))) = some Srt.kitem := by decide +kernel

theorem gen_mem_of {b : Srt}
    (h : (c.gens Srt.kitem).any (fun g' => match g' with | .inj b' => b' == b | .ctor _ => false) = true) :
    Gen.inj b ∈ c.gens Srt.kitem := by
  obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp h
  cases g with
  | ctor _ => cases hm
  | inj b' => rw [← (beq_iff_eq.mp hm)]; exact hg

/-- **The text's sentence entails `Γ`'s item, in every interpretation**: KItem's no-junk sentence
as the text writes it (13 injections) entails, with definedness, the no-junk item of KItem over
its 14 generators, `inj{#Tok, KItem}` among them (`noJunkItem_of_subset`). No interpretation of
the parameters is read. -/
theorem text_entails_item {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    (h : I ⊧ᴵ (trS U.ax125).pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c))).pat := by
  rw [nojunk_text] at h
  exact noJunkItem_of_subset hD (fun g hg => of_decide_eq_true (List.all_eq_true.mp gsText_sub g hg)) h

/-- That item is `Γ`'s, for every H. -/
theorem item_in_gamma (H : HookParams) :
    KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c)) ∈ consItemsK (c.withHooks H) :=
  noJunkItem_mem (c := c.withHooks H) (N := Srt.kitem) kitem_cons kitem_gens

/-- Each generator the text's sentence lists, as `noJunk_omitted_refuted` asks of it. -/
theorem gsText_hyp : ∀ g ∈ gsText, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧
    b ≠ tok ∧ (c.le tok b || c.le b tok) = false ∧ c.lowerBounds tok b = [] ∧ c.lowerBounds b tok = [] := by
  intro g hg
  have hap := List.all_eq_true.mp gsText_apart g hg
  cases g with
  | ctor k => cases hap
  | inj b =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff] at hap
    obtain ⟨⟨⟨⟨⟨hbm, hbo⟩, hbt⟩, hle⟩, hlb1⟩, hlb2⟩ := hap
    exact ⟨b, rfl, List.mem_filter.mpr ⟨gen_mem_of hbm, by rw [hbo]; rfl⟩, hbt, hle, hlb1, hlb2⟩

/-- **`tokKItem`, for every interpretation: sentence 125 is refuted**, `Γ` with it has no model
(`noJunk_omitted_refuted`): `inj{#Tok, KItem}(\dv{#Tok}("x"))` is an element of KItem, apart from
the image of each of the 13 injections the sentence lists. -/
theorem tok_refuted (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (c.withHooks H) → ¬ (I ⊧ᴵ (trS U.ax125).pat) := by
  intro M _ I hI hax
  rw [nojunk_text] at hax
  exact noJunk_omitted_refuted coreOK noRaw H kitem_cons noFnOvl
    (List.mem_filter.mpr ⟨gen_mem_of tok_gen.1, by rw [tok_gen.2]; rfl⟩) tok_value tok_inj_value gsText_hyp hI hax

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (c.withHooks H) [] [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

/-- **`Γ` has a model, for every H** (with the step's closure): the refutation is the sentence's. -/
theorem consistent (H : HookParams) : Consistent (c.withHooks H) :=
  consistent_of_fnHyp _ ((Semantics.coreOK_withHooks c H).trans coreOK)
    (fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H))

/-- **`Γ` does not entail sentence 125, for every H**: a model of `Γ` (`consistent`) in which the
sentence fails (`tok_refuted`). -/
theorem text_not_entailed (H : HookParams) : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    (I ⊧ᴵP Γ (c.withHooks H)) ∧ ¬ (I ⊧ᴵ (trS U.ax125).pat) := by
  obtain ⟨M, hM, I, hI⟩ := consistent H
  have hΓ : I ⊧ᴵP Γ (c.withHooks H) := fun φ h => hI φ (Or.inl (Or.inl h))
  exact ⟨M, hM, I, hΓ, tok_refuted H M hM I hΓ⟩

end KCore.TokKItem
