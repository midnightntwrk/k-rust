/-
  KCore. The per-rule fact of a rule whose open variables the right side or a cut holds under a
  set of symbols.

  `Semantics.rulePlainHeldH c H r` is `rulePlainPP` with two readings widened over a set H of held
  symbols: the first arm reads the variables the right side holds under constructors, injections
  and the symbols of H (`occsUnder c H`), and a variable counts as decided, where `rulePlainPP`
  asks a confined sort, also if a cut of `pre` holds it (`memHeldH c H` over the left side's
  variables). `Semantics.rulePlainHO2` (PredPlain.lean), what `rulesPlain` asks of one rule, gives
  `rulePlainHeldH` at `Semantics.holds`, so `coreOK` and `HypModelCore` give it of each rule
  (`Semantics.ruleFactsHeld_of_core`, `HypModelCore.ruleFactsHeld`); `rulePlainHeldH` is monotone
  in H. That a successor's valuation can be taken at values for such a rule
  (`rule_step_values_heldCEx`) is ExactHeldCEx.lean's.
-/
import KcoreSpec.StepValuesPP
import KcoreSpec.MemHeldValues

set_option autoImplicit false

namespace KCore

/-- **The conjunct of the plain shapes for one rule, over a set H of held symbols**: `rulePlainPP`
with the first arm reading the variables the right side holds under constructors, injections and
the symbols of H, and `conf` reading "of a confined sort, or held by a cut of `pre`". -/
def Semantics.rulePlainHeldH (c : Semantics) (H : Sym → Bool) (r : Rule) : Bool :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false || memHeldH c H (varOccs r.lhs) r.pre i
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (occsUnder c H r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- **What `rulePlainHeldH` says of an open variable**: the right side holds it, or its sort is
confined, or a cut holds it; or it is a condition variable, the conditions are closed and none of
their variables is held by the right side, the `ensures` or `post`. -/
theorem Semantics.rulePlainHeldH_opens {c : Semantics} {H : Sym → Bool} {r : Rule}
    (hp : c.rulePlainHeldH H r = true) : ∀ i ∈ r.opens,
      ((occsUnder c H r.rhs).contains i = true ∨ (r.vars[i]?.map c.confined).getD false = true ∨
        memHeldH c H (varOccs r.lhs) r.pre i = true) ∨
      (i ∈ r.condVars ∧ r.reqClosed = true ∧ ∀ j ∈ r.condVars,
        j ∉ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post) := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  intro i hi
  rcases hp.1 i hi with (hA | hB | hM) | ⟨hC, hcl, hap⟩
  · exact Or.inl (Or.inl hA)
  · exact Or.inl (Or.inr (Or.inl hB))
  · exact Or.inl (Or.inr (Or.inr hM))
  · refine Or.inr ⟨List.contains_iff_mem.mp hC, hcl, fun j hj hjr => ?_⟩
    have := hap j hj
    rw [List.contains_iff_mem.mpr hjr] at this
    exact absurd this (by decide)

/-- **What `rulePlainHeldH` says of a rule that competes with a larger one**: no condition
variable is open, or each open condition variable is of a confined sort or held by a cut, or the
conditions are closed. -/
theorem Semantics.rulePlainHeldH_compete {c : Semantics} {H : Sym → Bool} {r : Rule}
    (hp : c.rulePlainHeldH H r = true) (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true) :
    r.reqOpen = false ∨
      (∀ i ∈ r.openCondVars, (r.vars[i]?.map c.confined).getD false = true ∨
        memHeldH c H (varOccs r.lhs) r.pre i = true) ∨ r.reqClosed = true := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  rcases hp.2 with ((h1 | h2) | h3) | h4
  · exact Or.inl (by simpa using h1)
  · rw [hlarger] at h2; exact absurd h2 (by decide)
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

/-- `rulePlainHeldH` is monotone in the set of held symbols. -/
theorem Semantics.rulePlainHeldH_mono {c : Semantics} {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true)
    {r : Rule} (hp : c.rulePlainHeldH H r = true) : c.rulePlainHeldH H' r = true := by
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp ⊢
  have hm : ∀ i, memHeldH c H (varOccs r.lhs) r.pre i = true → memHeldH c H' (varOccs r.lhs) r.pre i = true :=
    fun i hi => by
      obtain ⟨s, v, t, hq, hv, hti⟩ := memHeldH_parts hi
      exact memHeldH_of_parts hq hv (occsUnder_mono c hH t i hti)
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases hp.1 i hi with (hA | hB | hM) | hC
    · exact Or.inl (Or.inl (List.contains_iff_mem.mpr (occsUnder_mono c hH _ i (List.contains_iff_mem.mp hA))))
    · exact Or.inl (Or.inr (Or.inl hB))
    · exact Or.inl (Or.inr (Or.inr (hm i hM)))
    · exact Or.inr hC
  · rcases hp.2 with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr fun i hi => (h3 i hi).imp id (hm i))
    · exact Or.inr h4

/-- A rule with `rulePlainHO2` has `rulePlainHeldH` at `Semantics.holds`: `heldOccs` and `memHeld`
are `occsUnder` and `memHeldH` at those symbols. -/
theorem Semantics.rulePlainHeldH_of_HO2 {c : Semantics} {r : Rule} (hp : c.rulePlainHO2 r = true) :
    c.rulePlainHeldH c.holds r = true := by
  simp only [Semantics.rulePlainHO2, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  simp only [Semantics.rulePlainHeldH, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases hp.1 i hi with (hA | hB | hM) | hC
    · rw [heldOccs_eq] at hA; exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr (Or.inl hB))
    · rw [memHeld_eq_H] at hM; exact Or.inl (Or.inr (Or.inr hM))
    · exact Or.inr hC
  · rcases hp.2 with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr fun i hi => (h3 i hi).imp id fun hM => by rw [memHeld_eq_H] at hM; exact hM)
    · exact Or.inr h4

/-- A rule with `rulePlainHO1` has `rulePlainHeldH` at `Semantics.holds`. -/
theorem Semantics.rulePlainHeldH_of_HO1 {c : Semantics} {r : Rule} (hp : c.rulePlainHO1 r = true) :
    c.rulePlainHeldH c.holds r = true :=
  Semantics.rulePlainHeldH_of_HO2 (Semantics.rulePlainHO2_of_HO1 hp)

/-- What `coreOK` gives of each rule: `ruleSorted`, and `rulePlainHeldH` at the symbols
`Semantics.holds` names. -/
theorem Semantics.ruleFactsHeld_of_core {c : Semantics} (h : c.coreOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true := fun r hr =>
  ⟨(Semantics.ruleFactsHO2_of_core h r hr).1,
    Semantics.rulePlainHeldH_of_HO2 (Semantics.ruleFactsHO2_of_core h r hr).2⟩

/-- What `HypModelCore` gives of each rule: `ruleSorted`, and `rulePlainHeldH` at the symbols
`Semantics.holds` names. -/
theorem Faithful.Model.HypModelCore.ruleFactsHeld {c : Semantics} (h : Faithful.Model.HypModelCore c) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH c.holds r = true := fun _ hr =>
  ⟨(h.ruleFactsHO2 hr).1, Semantics.rulePlainHeldH_of_HO2 (h.ruleFactsHO2 hr).2⟩

namespace Faithful

open ML
open KoreAML (VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

end Faithful

end KCore
