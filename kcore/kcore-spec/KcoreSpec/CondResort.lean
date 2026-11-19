/-
  KCore. The Holds lemma at the sort variable `R`.

  `holds_atR`: the Holds lemma at `R`, from the Holds lemma at the sort of the Booleans, which has
  an element, and a condition's pattern at `R` and at a numbered sort (`cond_crossAt`,
  CondCross.lean). `holds_entails_atR`: in every model of `Γc`.
-/
import KcoreSpec.CondCross
import KcoreSpec.CondPred
import KcoreSpec.ClausePreCore
import KcoreSpec.TermSoundCEx

set_option autoImplicit false

namespace KCore

open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

open ML Faithful

namespace HoldsShape

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The Holds lemma at `R` in every model of `Γc`**: `holds_entailsCEx`' reading of a condition, at
the sort a valuation gives `R`. -/
theorem holds_entails_atR (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (p : Cond) (hrc : hasBinder p = true → c.readsConfined = true)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hok : c.condOK vars p = true) (hbd : Cond.bound c vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl) {σr : M}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr : KoreAML.IsSort I σr)
    (hh : Holds c vars.length σ p b) (a : M) (ha : KoreAML.Inh I σr a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p)).interpret I e a ↔ b = true :=
  holds_atR (atomFacts_of_core h hIc (termSoundEx (Semantics.coreOK_iff_ex.mp h) hIc hc))
    (termsInSort_of_core h fun φ hφ => hIc φ (Or.inl hφ)) (holds_entailsCEx (Semantics.coreOK_iff_ex.mp h) hIc hc p hrc)
    hok hbd hP hr hk hRm hR hσr hh a ha

end

end HoldsShape

end KCore
