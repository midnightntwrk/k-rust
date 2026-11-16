/-
  KCore. The conjunct of the rules' plain shapes for one rule with predicates.

  `rulePlainPP` is the body `rulesPlain` has for one rule once rules with existential variables and
  predicates are admitted: which variables the left side leaves open the values decide (each held
  by the right side under constructors, or of a confined sort, or held by closed conditions no
  variable of which the right side, the `ensures` or `post` holds), and that a rule competing with a
  larger one has open condition variables of confined sorts, or closed conditions. `rulePlainEx` is
  it with `\top` predicates (`rulePlainEx_iff_pp`).
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

end KCore
