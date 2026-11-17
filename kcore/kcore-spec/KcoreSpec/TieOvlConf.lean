/-
  KCore, outside the cone: a no-confusion sentence of two generators,
  `\not{N}(\and{N}(g(X̄), g'(Ȳ)))`, fails in an interpretation with definedness where the two
  generators' sets meet: at a valuation that meets the sentence's guards and gives `X̄` and `Ȳ`
  elements at which `g` and `g'` build a common element of `N`, the translation of the sentence is
  not the whole of `N`. The hypotheses on the sentence are those `tieDist_entailed` reads, decided
  on the text. A tie file applies it where Γ states that the two generators meet (an overload
  equation, `KoreAML.Cons.ovlEqItem`): there every model of Γ refutes the sentence.
-/
import KcoreSpec.TieCons

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A no-confusion sentence of two generators that meet is refuted.** -/
theorem tieDist_refuted (hD : KoreAML.DefOK I) {N : String} {g g' : KoreAML.Gen}
    {i : Nat} {mod : String} {a : Kore.Axiom} {xs ys : List Kore.EVar} {p1 p2 : Kore.Pattern}
    (hpat : a.pattern = .not (KoreAML.srt N) (.and (KoreAML.srt N) [p1, p2]))
    (hp1 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p1 = KoreAML.Cons.genPat N g
      ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hp2 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p2 = KoreAML.Cons.genPat N g'
      ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (e : Valuation M)
    (hg : ∀ k ∈ (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf (KoreAML.tableOf a.sortVars a.pattern) k).interpret I e m)
    {m : M} (hN : InS I N m)
    (h1 : GS I N g ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map e.evalEvar) m)
    (h2 : GS I N g' ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map e.evalEvar) m) :
    ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) := by
  intro h
  have hx := KoreAML.trAxiom_at hD h e hg m
  dsimp only at hx
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hp1 hp2 h1 h2 hx
  rw [hpat] at hx
  simp only [KoreAML.sortOf] at hx
  have hin : (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I e m := by
    rw [trSort_srt]; exact (inS_iff e).mpr hN
  have hl : (KoreAML.sNot (KoreAML.trSort t (KoreAML.srt N))
      (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2))).interpret I e m := hx.mpr hin
  rw [KoreAML.interp_sNot, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars] at hl
  exact hl.1 ⟨h1, h2⟩

end

end Faithful
end KCore
