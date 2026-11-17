/-
  The extension of a model of the theory without the detached names satisfies the premises of the
  domains, of the interpretation's values at silent points and the closure axiom of Bool that name
  nothing of `D` (KcoreSpec/ConsTransferDomains.lean): the statements exist as stated and depend on
  no axiom but `propext`, `Classical.choice` and `Quot.sound`. Run from the package root:
  `lake env lean test/ConsTransferDomains.lean`.
-/
import KcoreSpec.ConsTransferDomains

open KCore KCore.Cons ML Faithful

example {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : ∀ σ, D σ → plainSym σ) (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P}
    (hφ : ΓDomains c φ ∨ ΓFallback c φ ∨ Γcl c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  rcases hφ with hφ | hφ | hφ
  · exact sat_own_domains hD hI hφ hn
  · exact sat_own_fallback hD hI hφ hn
  · exact sat_own_cl hD hI hφ hn

/-- info: 'KCore.Cons.sat_own_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_domains

/-- info: 'KCore.Cons.sat_own_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_fallback

/-- info: 'KCore.Cons.sat_own_cl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sat_own_cl
