/-
  KCore. The conjunct of the rules' plain shapes for one rule without predicates, once a rule may
  have existential variables.

  `Semantics.rulePlainEx` is `Semantics.rulePlainOpen` less `r.exs.isEmpty`: `\top` predicates, and
  each variable the left side does not bind, an existential one included, held by the right side
  under constructors, of a confined sort, or held by closed conditions no variable of which the right
  side, the `ensures` or `post` holds; a rule that competes with a larger one has open condition
  variables of confined sorts or closed conditions. An existential variable is in no condition of the
  left side, so it passes by the first two arms only. `rulePlainOpen` is `rulePlainEx` with no
  existential variable (`rulePlainOpen_iff_ex`); the predicates of a rule with `rulePlainEx` are
  `\top` (`rulePlainEx_top`). `rulesPlain` asks less of a rule: `rulePlainHO2` (PredPlain.lean).
-/
import KcoreSpec.OpenStep

set_option autoImplicit false

namespace KCore

/-- What `rulesPlain` asks of the rule r with the first arm reading constructors and injections
only (`ctorOccs`), and `\top` predicates; its left side need not bind every variable and it may
have existential variables. -/
def Semantics.rulePlainEx (c : Semantics) (r : Rule) : Bool :=
  r.pre.isTop && r.post.isTop &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
   let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))

/-- `rulePlainOpen` is `rulePlainEx` and no existential variable. -/
theorem Semantics.rulePlainOpen_iff_ex {c : Semantics} {r : Rule} :
    c.rulePlainOpen r = true ↔ c.rulePlainEx r = true ∧ r.exs = [] := by
  simp only [Semantics.rulePlainOpen, Semantics.rulePlainEx, Bool.and_eq_true, List.isEmpty_iff]
  constructor
  · rintro ⟨⟨⟨hex, hpre⟩, hpost⟩, hrest⟩
    exact ⟨⟨⟨hpre, hpost⟩, hrest⟩, hex⟩
  · rintro ⟨⟨⟨hpre, hpost⟩, hrest⟩, hex⟩
    exact ⟨⟨⟨hex, hpre⟩, hpost⟩, hrest⟩

/-- The predicates of a rule with `rulePlainEx` are `\top`. -/
theorem Semantics.rulePlainEx_top {c : Semantics} {r : Rule} (h : c.rulePlainEx r = true) :
    r.pre = .top ∧ r.post = .top := by
  simp only [Semantics.rulePlainEx, Bool.and_eq_true] at h
  obtain ⟨⟨hpre, hpost⟩, -⟩ := h
  exact ⟨Cond.eq_top_of_isTop hpre, Cond.eq_top_of_isTop hpost⟩

end KCore
