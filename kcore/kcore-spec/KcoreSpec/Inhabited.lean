/-
  KCore. A sort with a value has an element in every model of `Γ`: the premise the reader's
  connective readings `existsAsVariable`, `orSplit` and `requiresOrSplit` rest on where they read a
  rule without a variable of the axiom (`Parse.splitRule`). The axiom's sentence for such a rule is
  `∀x̄. (L → •R)` with x̄ in neither L nor R, which is `(∃x̄. L) → •R`, and `∃x. L` is `L` exactly
  where the sort of x has an element. The reader reads the rule only at a sort of which it exhibits a
  value (`Parse.exhibit?`, `Parse.sortOf_of_exhibit`); `Γ` entails an element there
  (`inhabited_of_value`, from `ΓDomains`'s item `∃y:s. ⟦v⟧ = y`). Not part of the reviewed layer's
  statements: no headline reads it.
-/
import KcoreSpec.FaithfulNeg
import KcoreSpec.Parse

set_option autoImplicit false

namespace KCore.Faithful

open ML

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- A sort with a value is inhabited in every model of `Γ`, from `ΓDomains`. -/
theorem inhabited_of_value {c : Semantics} (hI : I ⊧ᴵP Γ c) {v : GroundTerm} {s : Srt}
    (hv : c.sortOf v = some s) (e : Valuation M) :
    ∃ a, (KoreAML.inhOf (KoreAML.Cons.sortP (c.sortName s))).interpret I e a := by
  have hD := defOK hI
  have h := sat_dom hI (Or.inr (Or.inr (Or.inl ⟨v, s, hv, rfl⟩))) e default
  rw [KoreAML.interp_sExists] at h
  obtain ⟨a, h2, -⟩ := h
  rw [KoreAML.interp_member hD] at h2
  exact ⟨_, (inS_iff e).mpr ((inS_iff _).mp h2)⟩

/-- A sort of which the reader exhibits a value (`Parse.exhibit?`) is inhabited in every model of
`Γ`. -/
theorem inhabited_of_exhibit {c : Semantics} (hI : I ⊧ᴵP Γ c) {s : Srt} {v : GroundTerm}
    (h : Parse.exhibit? c s = some v) (e : Valuation M) :
    ∃ a, (KoreAML.inhOf (KoreAML.Cons.sortP (c.sortName s))).interpret I e a :=
  inhabited_of_value hI (Parse.sortOf_of_exhibit h) e

end KCore.Faithful
