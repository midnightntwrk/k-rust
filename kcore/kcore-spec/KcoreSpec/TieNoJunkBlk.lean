/-
  A no-junk sentence of a text is a constructor item of Γ, shown from its disjunct list.

  The text's no-junk sentence of a sort N is `\or{N}(d₁, …, dₖ)`, and Γ's item for N
  (`KoreAML.Cons.noJunkItem`) is the translation of the sentence whose disjuncts are
  `noJunkDisjuncts N [] gs`. The translation of a sentence without sort variables reads only its
  pattern: the variable table, the guards and the sort `⊤_N` come from the pattern, the label from
  the index and module, which are not part of the item's pattern. The symbol declarations enter
  only through the sort of the pattern, which for `\or{N}` is N whatever they are; the aliases
  enter only where the pattern applies one. So the text's sentence translates to the item's
  pattern as soon as its disjuncts are the item's and it applies no alias
  (`tnjItem_pat_of_disj`).

  `tnjItem_any_of_eq`: a pattern equal to the item's pattern of a constructor sort with
  generators is the pattern of an item of `consItemsK c` (`noJunkItem_mem`), which is the
  statement a tie's no-junk section asks, shown without scanning `consItemsK c`.
-/
import KcoreSpec.TieCons
import KcoreSpec.FaithfulNeg
import KcoreSpec.TieFRRead

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

/-- **The translation of a no-junk sentence is Γ's no-junk item**: a sentence with no sort
variable whose pattern is `\or{N}(ds)`, with `ds` the disjuncts `noJunkDisjuncts N [] gs` and no
alias applied, translates to the pattern of `noJunkItem N gs`, whatever the declarations. -/
theorem tnjItem_pat_of_disj {decls : List KoreAML.SymbolDecl} {aliases : List String}
    {ad : KoreAML.AxiomDecl} {N : String} {gs : List KoreAML.Gen} {ds : List Kore.Pattern}
    (hsv : ad.ax.sortVars = []) (hp : ad.ax.pattern = .or (KoreAML.srt N) ds)
    (hds : ds = KoreAML.noJunkDisjuncts N [] gs)
    (hal : TieFRRead.aliasFreeFR aliases ad.ax.pattern = true) :
    (KoreAML.trAxiom decls aliases ad).pat = (KoreAML.Cons.noJunkItem N gs).pat := by
  subst hds
  rw [hp] at hal
  simp only [KoreAML.Cons.noJunkItem, KoreAML.Cons.noJunkAx, KoreAML.trAxiom, hsv, hp,
    KoreAML.sortOf]
  rw [TieFRRead.tr_aliasFree _ _ _ hal]

/-- **Membership in Γ's constructor items from an equation**: a pattern equal to the no-junk item's
pattern of a constructor sort N with generators is the pattern of an item of `consItemsK c`. -/
theorem tnjItem_any_of_eq {c : Semantics} {N : Srt} (hN : N ∈ consSorts c)
    (hg : (c.gens N).isEmpty = false) {φ : KoreAML.P}
    (h : φ = (KoreAML.Cons.noJunkItem (c.sortName N) ((c.gens N).map (Gen.toK c))).pat) :
    (consItemsK c).any (·.pat == φ) = true := by
  subst h
  exact List.any_eq_true.mpr ⟨_, noJunkItem_mem hN hg, beq_self_eq_true _⟩

end Faithful
end KCore
