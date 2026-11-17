/-
  The tie of a rewrite rule in the direction from Γ to the text, for any text. Γ's axiom of a rule
  is the text's sentence with conjuncts more on its left side (the negation of the rules of a
  smaller priority, the definedness of the right side, the rule's `pre`). At a valuation where each
  of them holds of every element the text's left side holds, the two sentences say the same, so a
  model of Γ's axiom satisfies the text's sentence there.
-/
import KcoreSpec.TieLemmas

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace Faithful

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A rewrite whose left side is a conjunction, and the one with conjuncts more on the left side,
hold the same elements at a valuation where each conjunct more holds of every element the others
all hold. -/
theorem tieRewrites_more {ctx : KoreAML.Ctx} {C C1 C2 : Kore.KSort} {ls xs : List Kore.Pattern} {r : Kore.Pattern}
    {e : Valuation M} (hl : ls ≠ [])
    (hx : ∀ x ∈ xs, ∀ a, (∀ p ∈ ls, (KoreAML.tr ctx p).interpret I e a) → (KoreAML.tr ctx x).interpret I e a) (m : M) :
    (KoreAML.tr ctx (.rewrites C (.and C1 (ls ++ xs)) r)).interpret I e m ↔
      (KoreAML.tr ctx (.rewrites C (.and C2 ls) r)).interpret I e m := by
  have h1 : KoreAML.tr ctx (.rewrites C (.and C1 (ls ++ xs)) r) =
      KoreAML.sRewrites (KoreAML.trSort ctx.vars C) (KoreAML.trAndList ctx (KoreAML.trSort ctx.vars C1) (ls ++ xs))
        (KoreAML.tr ctx r) := by
    rw [KoreAML.tr, KoreAML.tr]
  have h2 : KoreAML.tr ctx (.rewrites C (.and C2 ls) r) =
      KoreAML.sRewrites (KoreAML.trSort ctx.vars C) (KoreAML.trAndList ctx (KoreAML.trSort ctx.vars C2) ls)
        (KoreAML.tr ctx r) := by
    rw [KoreAML.tr, KoreAML.tr]
  rw [h1, h2]
  unfold KoreAML.sRewrites
  rw [KoreAML.interp_sImp, KoreAML.interp_sImp, interp_trAndList (by simp [hl]), interp_trAndList hl]
  refine and_congr_right fun _ => ⟨fun h hls => h fun p hp => ?_, fun h hall => h fun p hp => hall p (List.mem_append_left _ hp)⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hls p hp
  · exact hx p hp m hls

/-- **Γ's rule axiom gives the text's sentence where the conjuncts Γ adds hold**: `g` is a rewrite
axiom whose left side is the conjuncts `ls` followed by `xs`, `t` the one whose left side is `ls`,
with the same right side, variable table and free variables. In a model of `g`'s translation, at a
valuation where each conjunct of `xs` holds of every element all of `ls` hold, `t`'s translation
holds. -/
theorem tieRule_more (hD : KoreAML.DefOK I) {ds ds' : List KoreAML.SymbolDecl} {al : List String}
    {g t : KoreAML.AxiomDecl} {C C1 C2 : Kore.KSort} {ls xs : List Kore.Pattern} {r : Kore.Pattern} (hl : ls ≠ [])
    (hg : g.ax.pattern = .rewrites C (.and C1 (ls ++ xs)) r) (ht : t.ax.pattern = .rewrites C (.and C2 ls) r)
    (htab : KoreAML.tableOf g.ax.sortVars g.ax.pattern = KoreAML.tableOf t.ax.sortVars t.ax.pattern)
    (hfree : (g.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] g.ax.pattern).eraseDups =
      (t.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] t.ax.pattern).eraseDups)
    (h : I ⊧ᴵ (KoreAML.trAxiom ds al g).pat) (e : Valuation M)
    (hx : ∀ x ∈ xs, ∀ a,
      (∀ p ∈ ls, (KoreAML.tr ⟨KoreAML.tableOf t.ax.sortVars t.ax.pattern, al⟩ p).interpret I e a) →
        (KoreAML.tr ⟨KoreAML.tableOf t.ax.sortVars t.ax.pattern, al⟩ x).interpret I e a) (m : M) :
    (KoreAML.trAxiom ds' al t).pat.interpret I e m := by
  have h1 := h e m
  unfold KoreAML.trAxiom at h1 ⊢
  dsimp only at h1 ⊢
  rw [htab, hfree] at h1
  generalize KoreAML.tableOf t.ax.sortVars t.ax.pattern = T at h1 hx ⊢
  rw [interpret_impl] at h1 ⊢
  intro hgd
  have h2 := h1 hgd
  rw [KoreAML.interp_equal hD] at h2 ⊢
  intro a
  have h3 := h2 a
  rw [hg] at h3
  rw [ht]
  simp only [KoreAML.sortOf] at h3 ⊢
  exact (tieRewrites_more hl hx a).symm.trans h3

end

end Faithful

end KCore
