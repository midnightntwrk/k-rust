/-
  The extension of a model of the theory without the detached names satisfies the rules' premises
  and the step's closure where they name nothing of `D` (KcoreSpec/ConsTransferFrag.lean): the
  statements exist as stated and depend on no axiom but `propext`, `Classical.choice` and
  `Quot.sound`. Run from the package root: `lake env lean test/ConsTransferFrag.lean`.
-/
import KcoreSpec.ConsTransferFrag

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P}
    (hφ : ΓRules c φ ∨ Γstep c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  rcases hφ with hφ | hφ
  · exact sat_own_rules hD hI hφ hn
  · exact sat_own_step hD hI hφ hn

example (c : Semantics) (r : Rule) : KFrag (prioRuleK c r) := kfrag_prioRuleK_fg c r

/-- info: 'KCore.Cons.sat_own_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_rules

/-- info: 'KCore.Cons.sat_own_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_step
