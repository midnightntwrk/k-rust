/-
  A sentence with a free element variable renamed is satisfied by the same interpretations. For the
  tie of an `[owise]` equation whose exclusion binds a variable under a name of its own: Γ's
  sentence reuses the equation's name for the bound variable, so the two translations differ by the
  index of a free variable.
-/
import KcoreSpec.FaithfulTr

set_option autoImplicit false

namespace KCore

open ML

namespace Faithful

/-- Substituting the variable `y` for the free occurrences of `x` captures no occurrence: no binder
of `y` has a free `x` below it. -/
def renOK (x y : EVar) : KoreAML.P → Bool
  | .existential z φ => !(Pattern.existential z φ : KoreAML.P).isFreeEvar x || (decide (y ≠ z) && renOK x y φ)
  | .mu _ φ => renOK x y φ
  | .application φ ψ | .implication φ ψ => renOK x y φ && renOK x y ψ
  | _ => true

theorem renOK_sound {x y : EVar} : ∀ {φ : KoreAML.P}, renOK x y φ = true →
    Pattern.substitutableForEvarIn x (.evar y) φ
  | .evar _, _ | .svar _, _ | .bottom, _ | .symbol _, _ => by simp [Pattern.substitutableForEvarIn]
  | .application φ ψ, h | .implication φ ψ, h => by
    simp only [renOK, Bool.and_eq_true] at h
    simp only [Pattern.substitutableForEvarIn]
    exact ⟨renOK_sound h.1, renOK_sound h.2⟩
  | .mu _ φ, h => by
    simp only [renOK] at h
    simp only [Pattern.substitutableForEvarIn]
    exact renOK_sound h
  | .existential z φ, h => by
    simp only [renOK, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Pattern.substitutableForEvarIn]
    split
    · rename_i hf
      rcases h with h | h
      · rw [hf] at h; cases h
      · exact ⟨by simp [Pattern.isFreeEvar]; exact fun e => h.1 e.symm, renOK_sound h.2⟩
    · trivial

/-- **A sentence with a free variable renamed says the same.** Where `y` is not free in `φ` and
substituting it for `x` captures nothing, an interpretation satisfies `φ[x ⇐ y]` exactly when it
satisfies `φ`: a sentence holds at every valuation, and the two read `x` and `y` at one element. -/
theorem sat_renamed {M : Type} {I : Interpretation KoreAML.Sym M} {φ : KoreAML.P} {x y : EVar}
    (hs : renOK x y φ = true) (hy : φ.isFreeEvar y = false) :
    (I ⊧ᴵ φ.substEvar x (.evar y)) ↔ (I ⊧ᴵ φ) := by
  have key : ∀ (e : Valuation M) m, (φ.substEvar x (.evar y)).interpret I e m =
      φ.interpret I ⟨Function.update e.evalEvar x (e.evalEvar y), e.evalSvar⟩ m :=
    fun e m => subf_xy_eq_eval_xey m e (renOK_sound hs)
  constructor
  · intro h e m
    have h1 := h ⟨Function.update e.evalEvar y (e.evalEvar x), e.evalSvar⟩ m
    rw [key] at h1
    refine (only_free_var_relevant _ _ _ _ (fun z hz => ?_) (fun _ _ => rfl) m).mp h1
    by_cases hzx : z = x
    · subst hzx; simp [Function.update_same]
    · have hzy : z ≠ y := fun e' => by rw [e', hy] at hz; cases hz
      simp [Function.update_noteq hzx, Function.update_noteq hzy]
  · intro h e m
    rw [key]
    exact h _ m

end Faithful
end KCore
