/-
  KCore. The conjunct of the rules' plain shapes for one rule with predicates.

  `rulePlainHO2` is what `rulesPlain` asks of one rule (`rulesPlain_iff_memHeld`), a rule with
  existential variables or predicates included: which variables the left side leaves open the
  values decide (each held by the right side under constructors, injections and the symbols
  `Semantics.holds` names, or of a confined sort, or held by a cut of `pre` (`memHeld`), or held by
  closed conditions no variable of which the right side, the `ensures` or `post` holds), and that a
  rule competing with a larger one has open condition variables of confined sorts or held by a cut,
  or closed conditions. `sortedOK` and `coreOK` give each rule `ruleSorted` and `rulePlainHO2`
  (`ruleFactsHO2_of_sortedOK`, `ruleFactsHO2_of_core`). `rulePlainHO1` is `rulePlainHO2` with no
  variable counted as held by a cut; it gives `rulePlainHO2` (`rulePlainHO2_of_HO1`).
  A definition whose rules have `rulePlainPP` or `rulePlainEx`, decided on its rules, has those
  facts with `ruleSorted` under `coreOK` (`ruleFactsPP_of_coreAll`, `ruleFactsEx_of_coreAll`).
  `rulePlainPP` is `rulePlainHO1` with the first arm reading the variables held under constructors
  and injections only; it gives `rulePlainHO1` (`rulePlainHO1_of_pp`). `rulePlainEx` is
  `rulePlainPP` with `\top` predicates (`rulePlainEx_iff_pp`).
-/
import KcoreSpec.ExPlain

set_option autoImplicit false

namespace KCore

/-- **The conjunct of the plain shapes for one rule with predicates, constructors only**: the open
variables are decided by the values, the right side holding them under constructors and injections,
and a rule competing with a larger one has open condition variables of confined sorts, or closed
conditions; `rest` holds the variables of `post`. -/
def Semantics.rulePlainPP (c : Semantics) (r : Rule) : Bool :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- `rulePlainEx` is `rulePlainPP` with `\top` predicates. -/
theorem Semantics.rulePlainEx_iff_pp {c : Semantics} {r : Rule} :
    c.rulePlainEx r = true ↔ r.pre.isTop = true ∧ r.post.isTop = true ∧ c.rulePlainPP r = true := by
  simp only [Semantics.rulePlainEx, Semantics.rulePlainPP, Bool.and_eq_true, and_assoc]

/-- A rule with `rulePlainEx` has `rulePlainPP`. -/
theorem Semantics.rulePlainPP_of_ex {c : Semantics} {r : Rule} (h : c.rulePlainEx r = true) :
    c.rulePlainPP r = true :=
  (Semantics.rulePlainEx_iff_pp.mp h).2.2

/-- `rulePlainPP` with the first arm reading `heldOccs`, the variables the right side holds under
constructors, injections and the symbols `Semantics.holds` names. -/
def Semantics.rulePlainHO1 (c : Semantics) (r : Rule) : Bool :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (heldOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- A rule with `rulePlainPP` has `rulePlainHO1`: the right side holds under `heldOccs` what it
holds under constructors. -/
theorem Semantics.rulePlainHO1_of_pp {c : Semantics} {r : Rule} (hp : c.rulePlainPP r = true) :
    c.rulePlainHO1 r = true := by
  simp only [Semantics.rulePlainPP, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  simp only [Semantics.rulePlainHO1, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, hp.2⟩
  rcases hp.1 i hi with (hA | hB) | hC
  · exact Or.inl (Or.inl (List.contains_iff_mem.mpr
      (ctorOccs_subset_heldOccs c _ i (List.contains_iff_mem.mp hA))))
  · exact Or.inl (Or.inr hB)
  · exact Or.inr hC

/-- Where every rule has `rulePlainPP` (a decidable fact of the rules), `coreOK` gives each rule
`ruleSorted` and `rulePlainPP`. -/
theorem Semantics.ruleFactsPP_of_coreAll {c : Semantics} (h : c.coreOK = true)
    (hpp : c.rules.all c.rulePlainPP = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true := fun r hr => by
  have hs := Semantics.sortedOK_sorted (Semantics.coreOK_parts h).1
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact ⟨hs.2 r hr, List.all_eq_true.mp hpp r hr⟩

/-- Where every rule has `rulePlainEx` (a decidable fact of the rules), `coreOK` gives each rule
`ruleSorted` and `rulePlainEx`. -/
theorem Semantics.ruleFactsEx_of_coreAll {c : Semantics} (h : c.coreOK = true)
    (hex : c.rules.all c.rulePlainEx = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true := fun r hr => by
  have hs := Semantics.sortedOK_sorted (Semantics.coreOK_parts h).1
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact ⟨hs.2 r hr, List.all_eq_true.mp hex r hr⟩

/-- **What `rulesPlain` asks of one rule**: `rulePlainHO1` with `conf` reading "of a confined
sort, or held by a cut of `pre`" (`memHeld` over the left side's variables). -/
def Semantics.rulePlainHO2 (c : Semantics) (r : Rule) : Bool :=
  let conf := fun i => (r.vars[i]?.map c.confined).getD false || memHeld c (varOccs r.lhs) r.pre i
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (heldOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- A rule with `rulePlainHO1` has `rulePlainHO2`: a variable of a confined sort is one of a
confined sort or held by a cut. -/
theorem Semantics.rulePlainHO2_of_HO1 {c : Semantics} {r : Rule} (hp : c.rulePlainHO1 r = true) :
    c.rulePlainHO2 r = true := by
  simp only [Semantics.rulePlainHO1, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hp
  simp only [Semantics.rulePlainHO2, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases hp.1 i hi with (hA | hB) | hC
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr (Or.inl hB))
    · exact Or.inr hC
  · rcases hp.2 with ((h1 | h2) | h3) | h4
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr fun i hi => Or.inl (h3 i hi))
    · exact Or.inr h4

/-- `rulesPlain` is `rulePlainHO2` of each rule. -/
theorem Semantics.rulesPlain_iff_memHeld {c : Semantics} :
    c.rulesPlain = true ↔ ∀ r ∈ c.rules, c.rulePlainHO2 r = true := by
  simp only [Semantics.rulesPlain, Semantics.rulePlainHO2, List.all_eq_true]

/-- What `sortedOK` gives of each rule, with no fact on its left side's variables, its existential
variables or its predicates: `ruleSorted` and `rulePlainHO2`. -/
theorem Semantics.ruleFactsHO2_of_sortedOK {c : Semantics} (h : c.sortedOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHO2 r = true := by
  intro r hr
  have hs := Semantics.sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have hp : c.rulesPlain = true := by
    simp only [Semantics.sortedOK, Bool.and_eq_true] at h
    exact h.1.1.2
  exact ⟨hs.2 r hr, Semantics.rulesPlain_iff_memHeld.mp hp r hr⟩

/-- What `coreOK` gives of each rule, with no fact on its left side's variables, its existential
variables or its predicates: `ruleSorted` and `rulePlainHO2`. -/
theorem Semantics.ruleFactsHO2_of_core {c : Semantics} (h : c.coreOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHO2 r = true :=
  Semantics.ruleFactsHO2_of_sortedOK (Semantics.coreOK_parts h).1

end KCore
