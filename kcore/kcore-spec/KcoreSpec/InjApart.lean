/-
  Two injections into a constructor sort from sorts that the order does not compare.

  In every model of `Γ c`, let `N` be a constructor sort and `a`, `b` two distinct sorts whose
  injections are generators of `N` (no open generator), such that `subsorts` relates them in
  neither direction and no sort lies below both. Γ then holds Cons-Dist of `inj{a,N}` and
  `inj{b,N}` (`injPair_mem`), so no element of `a` and element of `b` have the same injection
  into `N` (`inj_apart_of_incomparable`). Consequently no model of `Γ c` in which `a` has an
  element gives each element of `a` an element of `b` with the same injection into `N`
  (`inj_apart_no_model`).
-/
import KcoreSpec.FaithfulNeg

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **Cons-Dist of two incomparable injections, at elements.** In a model of `Γ c`, injections
into the constructor sort `N` from two sorts that `subsorts` does not compare and that have no
common lower bound build no element in common: an element `e` of `a` and an element `s` of `b`
do not have the same injection into `N`. -/
theorem inj_apart_of_incomparable (hI : I ⊧ᴵP Γ c) {N a b : Srt} (hN : N ∈ consSorts c)
    (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hb : Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : a ≠ b) (hab : (c.le a b || c.le b a) = false)
    (hlb : c.lowerBounds a b = []) (hlb' : c.lowerBounds b a = [])
    {e s : M} (he : InS I (c.sortName a) e) (hs : InS I (c.sortName b) s)
    (heq : ∀ m, GS I (c.sortName N) (.inj (c.sortName a)) [e] m ↔
      GS I (c.sortName N) (.inj (c.sortName b)) [s] m) : False := by
  have hsing : ∀ (A : String) (x : M), InS I A x →
      ∀ (i : Nat) (y : M) (t : String), [x][i]? = some y →
        (KoreAML.Gen.inj A).argSorts[i]? = some t → InS I t y := by
    intro A x hx i y t h1 h2
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      simp only [KoreAML.Gen.argSorts, List.getElem?_cons_zero, Option.some.injEq] at h2
      subst h1; subst h2; exact hx
    | succ n => simp at h1
  have hne' : Gen.inj a ≠ Gen.inj b := fun h => hne (by cases h; rfl)
  rcases mem_pairs_of_ne ha hb hne' with hp | hp
  · rcases injPair_mem hN hp hab with ⟨-, hm⟩ | ⟨hx, -⟩
    · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hm, rfl⟩)) rfl rfl (hsing _ _ he) (hsing _ _ hs) heq
    · exact hx hlb
  · rcases injPair_mem hN hp (by rw [Bool.or_comm]; exact hab) with ⟨-, hm⟩ | ⟨hx, -⟩
    · exact dist_at (defOK hI) (sat_cons hI (Or.inl ⟨_, hm, rfl⟩)) rfl rfl (hsing _ _ hs) (hsing _ _ he)
        (fun m => (heq m).symm)
    · exact hx hlb'

/-- **No model maps `a` into `b` below `N`.** Under the hypotheses of
`inj_apart_of_incomparable`, if `a` has an element, no model of `Γ c` gives every element `e` of
`a` an element `s` of `b` whose injection into `N` is `e`'s. -/
theorem inj_apart_no_model (hI : I ⊧ᴵP Γ c) {N a b : Srt} (hN : N ∈ consSorts c)
    (ha : Gen.inj a ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hb : Gen.inj b ∈ (c.gens N).filter (!c.isOpenGen ·))
    (hne : a ≠ b) (hab : (c.le a b || c.le b a) = false)
    (hlb : c.lowerBounds a b = []) (hlb' : c.lowerBounds b a = [])
    (hinh : ∃ e, InS I (c.sortName a) e)
    (htext : ∀ e, InS I (c.sortName a) e → ∃ s, InS I (c.sortName b) s ∧
      ∀ m, GS I (c.sortName N) (.inj (c.sortName b)) [s] m ↔
        GS I (c.sortName N) (.inj (c.sortName a)) [e] m) : False := by
  obtain ⟨e, he⟩ := hinh
  obtain ⟨s, hs, heq⟩ := htext e he
  exact inj_apart_of_incomparable hI hN ha hb hne hab hlb hlb' he hs (fun m => (heq m).symm)

end

end Faithful

end KCore
