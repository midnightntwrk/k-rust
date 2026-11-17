/-
  KCore. The conjunct of the rules' plain shapes for one rule with predicates.

  `rulePlainPP` is what `rulesPlain` asks of one rule (`rulesPlain_iff_pp`), a rule with existential
  variables or predicates included: which variables the left side leaves open the values decide (each held
  by the right side under constructors, or of a confined sort, or held by closed conditions no
  variable of which the right side, the `ensures` or `post` holds), and that a rule competing with a
  larger one has open condition variables of confined sorts, or closed conditions. `rulePlainEx` is
  it with `\top` predicates (`rulePlainEx_iff_pp`). `sortedOK` and `coreOK` give each rule
  `ruleSorted` and `rulePlainPP` (`ruleFactsPP_of_sortedOK`, `ruleFactsPP_of_core`), and
  `rulePlainEx` where the rules' predicates are `\top` (`ruleFactsEx_of_coreTop`).
-/
import KcoreSpec.ExPlain

set_option autoImplicit false

namespace KCore

/-- **The conjunct of the plain shapes for one rule with predicates**: the open variables are
decided by the values, and a rule competing with a larger one has open condition variables of
confined sorts, or closed conditions; `rest` holds the variables of `post`. -/
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

/-- `rulesPlain` is `rulePlainPP` of each rule. -/
theorem Semantics.rulesPlain_iff_pp {c : Semantics} :
    c.rulesPlain = true ↔ ∀ r ∈ c.rules, c.rulePlainPP r = true := by
  simp only [Semantics.rulesPlain, Semantics.rulePlainPP, List.all_eq_true]

/-- What `sortedOK` gives of each rule, with no fact on its left side's variables, its existential
variables or its predicates: `ruleSorted` and `rulePlainPP`. -/
theorem Semantics.ruleFactsPP_of_sortedOK {c : Semantics} (h : c.sortedOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true := by
  intro r hr
  have hs := Semantics.sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have hp : c.rulesPlain = true := by
    simp only [Semantics.sortedOK, Bool.and_eq_true] at h
    exact h.1.1.2
  exact ⟨hs.2 r hr, Semantics.rulesPlain_iff_pp.mp hp r hr⟩

/-- What `coreOK` gives of each rule, with no fact on its left side's variables, its existential
variables or its predicates: `ruleSorted` and `rulePlainPP`. -/
theorem Semantics.ruleFactsPP_of_core {c : Semantics} (h : c.coreOK = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainPP r = true :=
  Semantics.ruleFactsPP_of_sortedOK (Semantics.coreOK_parts h).1

/-- Where `Cond.isTop` accepts every rule's predicates, `coreOK` gives each rule `ruleSorted` and
`rulePlainEx`. -/
theorem Semantics.ruleFactsEx_of_coreTop {c : Semantics} (h : c.coreOK = true)
    (htop : c.rules.all (fun r => r.pre.isTop && r.post.isTop) = true) :
    ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainEx r = true := fun r hr => by
  have ht := List.all_eq_true.mp htop r hr
  simp only [Bool.and_eq_true] at ht
  exact ⟨(Semantics.ruleFactsPP_of_core h r hr).1,
    Semantics.rulePlainEx_iff_pp.mpr ⟨ht.1, ht.2, (Semantics.ruleFactsPP_of_core h r hr).2⟩⟩

end KCore
