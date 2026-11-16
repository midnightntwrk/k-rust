/-
  KCore. Exactness, for a definition whose rules' left sides need not bind every variable: the
  right-to-left half (`exact_open`, Sound.lean, takes the other from `has_model_choice_open` at
  `T := Step`).

  - Right to left, in any model of `Γc` with the step's closure: a successor of x's element in y's
    element is given by the axiom of a rule r at a valuation of r's variables in their sorts
    (`step_successor_axiomOpen`). x's element is in no competitor's `applies` there, so no
    competitor applies at values (`successor_split_rule`, under `StepDecided`); and the valuation
    gives a σ of values with every other premise of `StepBy c r σ x y` (`stepBy_of_values`: each
    open variable by arm A, B or C). So `Step c x y` (`step_of_successorOpen`).
-/
import KcoreSpec.OpenChoice
import KcoreSpec.OpenComplete

set_option autoImplicit false

namespace KCore

open ML Faithful

/-- **A successor in a model is a step**, for a semantics that `coreOK` accepts whose functions meet
`FnHyp` and whose rules have `ruleSorted` and `rulePlainOpen`: in a model of `Γc` with the step's
closure, where x's element has a successor in y's element, `Step c x y`. -/
theorem step_of_successorOpen (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (x y : Config c) (e : Valuation M)
    (hs : (KoreAML.sNext (den c y.val)).interpret I e (elemOf c I x.val)) : Step c x y := by
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  have hd := stepDecided_of_rules (hypSound_of_core h) hf.1 hrules x.val
  obtain ⟨b, hb, r, hr, tbl, e2, hkeys, hkeysC, hin, hl, hreq, hcomp, hy, hens⟩ :=
    step_successor_axiomOpen hrules x hI e _ hs
  have hbe : b = elemOf c I y.val := ((elemOf_spec hIΓ y.property e).1 b).mp hb
  subst hbe
  obtain ⟨hsr, hpr⟩ := hrules r hr
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    rcases successor_split_rule h hrules x hd hIc hf.2.2.2.2.1.2 hsr hpr (hd r hr) hkeys hkeysC hin hl hreq hcomp hy hens with
      ⟨-, y', σ, hst, -⟩ | ⟨-, σ, hu, -⟩
    · exact (hst hr).hprio
    · exact hu.2.2
  obtain ⟨σ, -, hst⟩ := stepBy_of_values h hf hIc hr hsr hpr hkeys hin x y hl hreq hy hens
  exact step_iff_by.mpr ⟨r, σ, hst hprio⟩

end KCore
