/-
  A run of the step relation read in matching logic: soundness (`SoundC`) entails each step,
  `⟦x⟧ → •⟦y⟧`; this lifts it to a run. `eventually φ` is the least fixpoint `μX. φ ∨ •X`, the
  states with a finite path of `•` to φ (one-path reachability); a run from x to z gives
  `Γ c ⊧ ⟦x⟧ → eventually ⟦z⟧`, and a run of n steps gives `Γ c ⊧ ⟦x⟧ → •ⁿ⟦z⟧`.
-/
import KcoreSpec.Sound
import KcoreSpec.Runs

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- The set variable `eventually` binds. -/
def evVar : SVar := ⟨0⟩

/-- `eventually φ := μX. φ ∨ •X`: φ, or a successor in `eventually φ`. -/
def eventually (φ : KoreAML.P) : KoreAML.P := .mu evVar (φ ⋁ KoreAML.sNext (.svar evVar))

/-- n applications of `•`. -/
def nextN : Nat → KoreAML.P → KoreAML.P
  | 0, φ => φ
  | n + 1, φ => KoreAML.sNext (nextN n φ)

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- A closed φ lies in `eventually φ`. -/
theorem eventually_base {φ : KoreAML.P} (hφ : KoreAML.Closed φ) (e : Valuation M) (m : M)
    (h : φ.interpret I e m) : (eventually φ).interpret I e m := by
  intro B hB
  refine hB m ?_
  simp only [Pattern.interpret]
  intro hn
  exact absurd ((hφ.interp e _ m).mp h) hn

/-- A successor of an element of `eventually φ` lies in it. -/
theorem eventually_step {φ : KoreAML.P} (e : Valuation M) (m a b : M)
    (ha : I.evalSymb .next a) (hb : (eventually φ).interpret I e b) (hab : I.evalApp a b m) :
    (eventually φ).interpret I e m := by
  intro B hB
  refine hB m ?_
  simp only [Pattern.interpret]
  intro _
  refine ⟨a, b, ha, ?_, hab⟩
  show Function.update e.evalSvar evVar B evVar b
  rw [Function.update_same]
  exact hb B hB

end

/-- **A run is entailed, one-path**: for a semantics `coreOK` accepts that reads no confined sort,
a run from x to z makes `Γ c` entail that x reaches z, `⟦x⟧ → eventually ⟦z⟧` (each step by
`sound_at_step`). -/
theorem star_entails {c : Semantics} (hs : c.coreOK = true) (hrc : c.readsConfined = false)
    {x z : Config c} (h : Star (Step c) x z) :
    Γ c ⊧ (den c x.val ⇒ eventually (den c z.val)) := by
  induction h with
  | refl =>
    intro M _ I _ e m hm
    exact eventually_base (den_closed c _) e m hm
  | @cons x y z hxy _ ih =>
    intro M _ I hI e m hm
    obtain ⟨a, b, ha, hb, hab⟩ := KoreAML.interp_app.mp (sound_at_step c hs hrc x y hxy hI e m hm)
    exact eventually_step e m a b ha (ih hI e b hb) hab

/-- **A run of n steps is entailed**: `⟦x⟧ → •ⁿ⟦z⟧`. -/
theorem star_entails_nextN {c : Semantics} (hs : c.coreOK = true) (hrc : c.readsConfined = false)
    {x z : Config c} (h : Star (Step c) x z) :
    ∃ n, Γ c ⊧ (den c x.val ⇒ nextN n (den c z.val)) := by
  induction h with
  | refl => exact ⟨0, by intro M _ I _ e m hm; exact hm⟩
  | @cons x y z hxy _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    intro M _ I hI e m hm
    obtain ⟨a, b, ha, hb, hab⟩ := KoreAML.interp_app.mp (sound_at_step c hs hrc x y hxy hI e m hm)
    exact KoreAML.interp_app.mpr ⟨a, b, ha, hn hI e b hb, hab⟩

end KCore
