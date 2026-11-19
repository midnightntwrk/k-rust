/-
  KItem's no-junk sentence on the texts of construct fixtures e6-mod-sort-kbott and
  e6-mod-kvariable-syntax (`f2-examples/e6-mod-sort-kbott.kompile.kore`, axiom 89, and
  `f2-examples/e6-mod-kvariable-syntax.kompile.kore`, axiom 89), the one sentence their ties
  (test/TieE6ModSortKbott.lean, test/TieE6ModKvariableSyntax.lean) leave in `uncovered`. Stated on
  the literals `kore` and `defn` and the sentences as written (`trS ad := trAxiom k.symbolDecls
  k.aliasNames ad`). Run from the package root: `lake env lean -j1 test/TieE6KItemOmitted.lean`.

  Each text declares a sort X (`sort SortKBott{}`, kast.md:70; `sort Sort'Hash'KVariable{}`,
  kast.md:351) that its KItem no-junk sentence does not list, states no subsort axiom of X, and
  applies `inj{X, KItem}` in the equations of the sort predicate `isX`. The reading holds X below
  KItem (`x_sub`, `Parse.ReadingNote.tokKItem`), so `Γ`'s no-junk item of KItem lists 13
  generators, the sentence 12. X has no constructor and no token: no value of X is exhibited, and
  `Γ` holds no item stating that X has an element.
  - `text_entails_item`: the sentence entails `Γ`'s item, in every interpretation with definedness;
    `item_in_gamma`: the item is `Γ`'s, for every H.
  - `refuted_with_nonempty`: for every H, no model of `Γ (cH H)` satisfies both the sentence and
    the text's G-nonempty item of X (`nonemptyItem`, an item of `(Theory.ofDefinition kore).signature`
    pattern for pattern: `nonempty_in_text`). An element of X has an image under `inj{X, KItem}` (Cons-Fun), an element of
    KItem apart from the image of each of the 12 injections the sentence lists (Cons-Dist); the
    sentence says it is one of them (`noJunk_omitted_refuted_elemE6o`).
  So the sentence holds in a model of `Γ` only where X is empty there, and the text's own
  translation states X nonempty: `Γ` with the text's sentences has no model. This file does not tie
  the sentence; it states where the reading and the text part.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore

open ML Faithful

namespace TieE6KItemOmitted

/-- **A no-junk sentence without an injection, at an element of the injection's source sort.** Let
N be a constructor sort, `inj{a, N}` one of its generators that is not open, x an element of the
sort a in a model of `Γ (c.withHooks H)`, and `gs` generators of N each an injection `inj{b, N}`
that is not open, from a sort b other than a, incomparable with a and with no lower bound in common
with it. Then the model does not satisfy the no-junk sentence of N over `gs`: `inj{a, N}` builds
one element of N from x (Cons-Fun); the sentence says it is one that some `inj{b, N}` builds from
an element of b, so the two injections build one element, which their Cons-Dist item denies. -/
theorem noJunk_omitted_refuted_elemE6o {c : Semantics} (H : HookParams) {N a : Srt} (hN : N ∈ consSorts c) (hno : c.fnOvlSyms = [])
    (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·)) {gs : List Gen}
    (hgs : ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·) ∧ b ≠ a ∧
      (c.le a b || c.le b a) = false ∧ c.lowerBounds a b = [] ∧ c.lowerBounds b a = [])
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (c.withHooks H))
    {x : M} (hx : InS I (c.sortName a) x) :
    ¬ (I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName N) (gs.map (Gen.toK c))).pat) := by
  intro hax
  have hD := defOK hI
  have hN' : N ∈ consSorts (c.withHooks H) := hN
  have hno' : (c.withHooks H).fnOvlSyms = [] := hno
  have hamem' : Gen.inj a ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := ha
  obtain ⟨y0, hy0, hset_a⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hN' hamem' rfl, rfl⟩))
    (xs := [x]) rfl (single_sorts hx)
  have hset_a : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [x] m ↔ m = y0 := hset_a
  obtain ⟨g, hg, ys, hys, hgs'⟩ := noJunk_elim hD hax hy0
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨b, rfl, hbmem, hba, hle, hlb1, hlb2⟩ := hgs g0 hg0
  obtain ⟨y, hy, rfl⟩ : ∃ y, InS I (c.sortName b) y ∧ ys = [y] := by
    cases hys with
    | cons hy hr => cases hr; exact ⟨_, hy, rfl⟩
  have hbmem' : Gen.inj b ∈ ((c.withHooks H).gens N).filter (!(c.withHooks H).isOpenGen ·) := hbmem
  obtain ⟨y1, -, hy1⟩ := fun_at hD (sat_cons hI (Or.inl ⟨_, funItem_mem hN' hbmem' rfl, rfl⟩)) (xs := [y]) rfl
    (single_sorts hy)
  have hy1 : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y1 := hy1
  have hset_b : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m ↔ m = y0 := fun m => by
    rw [hy1 m, ← (hy1 _).mp hgs']
  have hseq : ∀ m, GS I (c.sortName N) (Gen.toK c (.inj a)) [x] m ↔
      GS I (c.sortName N) (Gen.toK c (.inj b)) [y] m := fun m => by rw [hset_a, hset_b]
  have hne : Gen.inj a ≠ Gen.inj b := fun h => hba (by cases h; rfl)
  rcases mem_pairs_of hne hamem' hbmem' with hp | hp
  · rcases injPair_mem hN' hp hle with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [_]) (ys := [y]) rfl rfl
        (single_sorts hx) (single_sorts hy) hseq
    · exact hl hlb1
  · rcases injPair_mem hN' hp (by rw [Bool.or_comm]; exact hle) with ⟨-, hit⟩ | ⟨hl, -⟩
    · exact dist_at hD (sat_cons hI (Or.inl ⟨_, hit, rfl⟩)) (xs := [y]) (ys := [_]) rfl rfl
        (single_sorts hy) (single_sorts hx) (fun m => (hseq m).symm)
    · exact hl hlb2

theorem gen_mem_of {c : Semantics} {b : Srt}
    (h : (c.gens Srt.kitem).any (fun g' => match g' with | .inj b' => b' == b | .ctor _ => false) = true) :
    Gen.inj b ∈ c.gens Srt.kitem := by
  obtain ⟨g, hg, hm⟩ := List.any_eq_true.mp h
  cases g with
  | ctor _ => cases hm
  | inj b' => rw [← (beq_iff_eq.mp hm)]; exact hg

/-- The generators a KItem no-junk sentence lists that are as `noJunk_omitted_refuted_elemE6o`
asks, from the decision `apartB`. -/
def apartB (c : Semantics) (x : Srt) (gs : List Gen) : Bool :=
  gs.all (fun g => match g with
    | .inj b => (c.gens Srt.kitem).any (fun g' => match g' with | .inj b' => b' == b | .ctor _ => false) &&
        !c.isOpenGen (.inj b) && b != x && !(c.le x b || c.le b x) &&
        (c.lowerBounds x b).isEmpty && (c.lowerBounds b x).isEmpty
    | .ctor _ => false)

theorem hyp_of_apartB {c : Semantics} {x : Srt} {gs : List Gen} (h : apartB c x gs = true) :
    ∀ g ∈ gs, ∃ b, g = .inj b ∧ Gen.inj b ∈ (c.gens Srt.kitem).filter (!c.isOpenGen ·) ∧
      b ≠ x ∧ (c.le x b || c.le b x) = false ∧ c.lowerBounds x b = [] ∧ c.lowerBounds b x = [] := by
  intro g hg
  have hap := List.all_eq_true.mp h g hg
  cases g with
  | ctor k => cases hap
  | inj b =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.isEmpty_iff] at hap
    obtain ⟨⟨⟨⟨⟨hbm, hbo⟩, hbt⟩, hle⟩, hlb1⟩, hlb2⟩ := hap
    exact ⟨b, rfl, List.mem_filter.mpr ⟨gen_mem_of hbm, by rw [hbo]; rfl⟩, hbt, hle, hlb1, hlb2⟩

/-- An element of a sort constant from its G-nonempty item. -/
theorem inS_of_nonempty {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    {n : String} {b : Bool} (h : I ⊧ᴵ (KoreAML.nonemptyItem ⟨"Sort" ++ n, [], b⟩).pat) : ∃ a, InS I n a :=
  KoreAML.nonempty_of hD h (e := KoreAML.val0)

end TieE6KItemOmitted

namespace TieE6KItemOmittedKBott

open TieE6KItemOmitted

kore_term kore from "f2-examples/e6-mod-sort-kbott.kompile.kore"
definition_of defn from "f2-examples/e6-mod-sort-kbott.kompile.kore"
user_axioms U from "f2-examples/e6-mod-sort-kbott.kompile.kore" module "E6-MOD-SORT-KBOTT"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : KoreAML.AxiomDecl) : KoreAML.Item := KoreAML.trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort KBott. -/
noncomputable def xs : Srt := (c.userSorts.filter (c.sortName · == "KBott")).headD 0

/-- The generators of KItem the text's sentence lists: KItem's generators in the text's order but
`inj{KBott, KItem}`. -/
noncomputable def gsText : List Gen := (gensInOrder c defn.pres Srt.kitem).filter fun g => match g with
  | .inj b => b != xs
  | .ctor _ => true

theorem coreOK : c.coreOK = true := by decide_cheap
theorem x_named : c.sortName xs = "KBott" := by decide +kernel
/-- KBott is a sort of the definition below KItem; the text states no subsort axiom of it. -/
theorem x_sub : (xs, Srt.kitem) ∈ c.subsorts := by decide +kernel
/-- Sentence 89 is the no-junk sentence of KItem over the generators `gsText`. -/
theorem nojunk_text : (trS U.ax89).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gsText.map (Gen.toK c))).pat := by decide +kernel
theorem gsText_sub : (gsText.map (Gen.toK c)).all (fun g => decide (g ∈ (c.gens Srt.kitem).map (Gen.toK c))) = true := by
  decide +kernel
theorem gsText_length : gsText.length + 1 = (c.gens Srt.kitem).length := by decide +kernel
theorem kitem_cons : Srt.kitem ∈ consSorts c := by decide +kernel
theorem kitem_gens : (c.gens Srt.kitem).isEmpty = false := by decide +kernel
theorem noFnOvl : c.fnOvlSyms = [] := by decide +kernel
/-- `inj{KBott, KItem}` is a generator of KItem, not an open one. -/
theorem x_gen : (c.gens Srt.kitem).any (fun g => match g with | .inj b => b == xs | .ctor _ => false) = true ∧
    c.isOpenGen (.inj xs) = false := by decide +kernel
theorem gsText_apart : apartB c xs gsText = true := by decide +kernel

/-- The text's G-nonempty item of KBott is one of its translation's signature items. -/
theorem nonempty_in_text :
    (KoreAML.Theory.ofDefinition kore).signature.any
      (·.pat == (KoreAML.nonemptyItem ⟨"Sort" ++ "KBott", [], false⟩).pat) = true := by
  decide +kernel

/-- **The text's sentence entails `Γ`'s item, in every interpretation with definedness.** -/
theorem text_entails_item {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    (h : I ⊧ᴵ (trS U.ax89).pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c))).pat := by
  rw [nojunk_text] at h
  exact noJunkItem_of_subset hD (fun g hg => of_decide_eq_true (List.all_eq_true.mp gsText_sub g hg)) h

/-- That item is `Γ`'s, for every H. -/
theorem item_in_gamma (H : HookParams) :
    KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c)) ∈ consItemsK (cH H) :=
  noJunkItem_mem (c := cH H) (N := Srt.kitem) kitem_cons kitem_gens

/-- **For every H, no model of `Γ` satisfies sentence 89 and the text's G-nonempty item of KBott.** -/
theorem refuted_with_nonempty (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → I ⊧ᴵ (trS U.ax89).pat →
      ¬ (I ⊧ᴵ (KoreAML.nonemptyItem ⟨"Sort" ++ "KBott", [], false⟩).pat) := by
  intro M _ I hI hax hne
  obtain ⟨x, hx⟩ := inS_of_nonempty (defOK hI) hne
  rw [← x_named] at hx
  rw [nojunk_text] at hax
  exact noJunk_omitted_refuted_elemE6o H kitem_cons noFnOvl
    (List.mem_filter.mpr ⟨gen_mem_of x_gen.1, by rw [x_gen.2]; rfl⟩) (hyp_of_apartB gsText_apart) hI hx hax

end TieE6KItemOmittedKBott

namespace TieE6KItemOmittedKVariable

open TieE6KItemOmitted

kore_term kore from "f2-examples/e6-mod-kvariable-syntax.kompile.kore"
definition_of defn from "f2-examples/e6-mod-kvariable-syntax.kompile.kore"
user_axioms U from "f2-examples/e6-mod-kvariable-syntax.kompile.kore" module "E6-MOD-KVARIABLE-SYNTAX"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : KoreAML.AxiomDecl) : KoreAML.Item := KoreAML.trAxiom kore.symbolDecls kore.aliasNames ad

/-- The sort #KVariable. -/
noncomputable def xs : Srt := (c.userSorts.filter (c.sortName · == "'Hash'KVariable")).headD 0

/-- The generators of KItem the text's sentence lists: KItem's generators in the text's order but
`inj{#KVariable, KItem}`. -/
noncomputable def gsText : List Gen := (gensInOrder c defn.pres Srt.kitem).filter fun g => match g with
  | .inj b => b != xs
  | .ctor _ => true

theorem coreOK : c.coreOK = true := by decide_cheap
theorem x_named : c.sortName xs = "'Hash'KVariable" := by decide +kernel
/-- #KVariable is a sort of the definition below KItem; the text states no subsort axiom of it. -/
theorem x_sub : (xs, Srt.kitem) ∈ c.subsorts := by decide +kernel
/-- Sentence 89 is the no-junk sentence of KItem over the generators `gsText`. -/
theorem nojunk_text : (trS U.ax89).pat =
    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) (gsText.map (Gen.toK c))).pat := by decide +kernel
theorem gsText_sub : (gsText.map (Gen.toK c)).all (fun g => decide (g ∈ (c.gens Srt.kitem).map (Gen.toK c))) = true := by
  decide +kernel
theorem gsText_length : gsText.length + 1 = (c.gens Srt.kitem).length := by decide +kernel
theorem kitem_cons : Srt.kitem ∈ consSorts c := by decide +kernel
theorem kitem_gens : (c.gens Srt.kitem).isEmpty = false := by decide +kernel
theorem noFnOvl : c.fnOvlSyms = [] := by decide +kernel
/-- `inj{#KVariable, KItem}` is a generator of KItem, not an open one. -/
theorem x_gen : (c.gens Srt.kitem).any (fun g => match g with | .inj b => b == xs | .ctor _ => false) = true ∧
    c.isOpenGen (.inj xs) = false := by decide +kernel
theorem gsText_apart : apartB c xs gsText = true := by decide +kernel

/-- The text's G-nonempty item of #KVariable is one of its translation's signature items. -/
theorem nonempty_in_text :
    (KoreAML.Theory.ofDefinition kore).signature.any
      (·.pat == (KoreAML.nonemptyItem ⟨"Sort" ++ "'Hash'KVariable", [], false⟩).pat) = true := by
  decide +kernel

/-- **The text's sentence entails `Γ`'s item, in every interpretation with definedness.** -/
theorem text_entails_item {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    (h : I ⊧ᴵ (trS U.ax89).pat) :
    I ⊧ᴵ (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c))).pat := by
  rw [nojunk_text] at h
  exact noJunkItem_of_subset hD (fun g hg => of_decide_eq_true (List.all_eq_true.mp gsText_sub g hg)) h

/-- That item is `Γ`'s, for every H. -/
theorem item_in_gamma (H : HookParams) :
    KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((c.gens Srt.kitem).map (Gen.toK c)) ∈ consItemsK (cH H) :=
  noJunkItem_mem (c := cH H) (N := Srt.kitem) kitem_cons kitem_gens

/-- **For every H, no model of `Γ` satisfies sentence 89 and the text's G-nonempty item of
#KVariable.** -/
theorem refuted_with_nonempty (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH H) → I ⊧ᴵ (trS U.ax89).pat →
      ¬ (I ⊧ᴵ (KoreAML.nonemptyItem ⟨"Sort" ++ "'Hash'KVariable", [], false⟩).pat) := by
  intro M _ I hI hax hne
  obtain ⟨x, hx⟩ := inS_of_nonempty (defOK hI) hne
  rw [← x_named] at hx
  rw [nojunk_text] at hax
  exact noJunk_omitted_refuted_elemE6o H kitem_cons noFnOvl
    (List.mem_filter.mpr ⟨gen_mem_of x_gen.1, by rw [x_gen.2]; rfl⟩) (hyp_of_apartB gsText_apart) hI hx hax

end TieE6KItemOmittedKVariable

end KCore

#check @KCore.TieE6KItemOmittedKBott.refuted_with_nonempty
#check @KCore.TieE6KItemOmittedKBott.text_entails_item
#check @KCore.TieE6KItemOmittedKVariable.refuted_with_nonempty
#check @KCore.TieE6KItemOmittedKVariable.text_entails_item
#print axioms KCore.TieE6KItemOmittedKBott.refuted_with_nonempty
#print axioms KCore.TieE6KItemOmittedKVariable.refuted_with_nonempty
