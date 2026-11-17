/-
  KCore. The step relation of a definition (KCORE-SPEC.md §4). Frozen layer.

  A rule r rewrites x to y
  when, under a well-sorted σ, its left-hand side denotes x, its `requires` evaluates to `true` and
  its premise predicate `pre` holds, its right-hand side evaluates to y (defined), its `ensures`
  evaluates to `true` and its right-side predicate `post` holds, **and no rule of a smaller priority
  applies to x**: for every rule r' with `r'.prio < r.prio`, every σ' that gives the variables of
  r''s left side and conditions values of their sorts and under which r''s left-hand side denotes x
  makes r''s `requires` evaluate to something other than `true` or its `pre` false (`NotApplies`).
  That is the matching-logic reading of
      lhs ∧ ⌈req = true⌉ ∧ pre ∧ ¬ ⋁_{r' ∈ higher} ∃x̄'. (lhs' ∧ ⌈req' = true⌉ ∧ pre')  ⇒  rhs,
  the same negated-competitor premise kompile writes for an `[owise]` equation; Γ_D reads the
  `priority` and `owise` attributes into it (KCORE-SPEC.md §4). Whether r' could also produce a
  defined right-hand side does not matter: a rule that applies blocks the lower priorities.
  The right side is `rhs` where the `ensures` evaluates to `true`; `NotApplies` reads neither.
  `NotApplies` is a positive statement (the `requires` *evaluates* to false or undefined, or `pre`
  *is* false), so Step stays a non-recursive inductive with one constructor for every definition.
-/
import KcoreSpec.Evaluation
import KcoreSpec.DefinitionWf

set_option autoImplicit false

namespace KCore

/-- `RuleReqFails c σ r`: the rule has a `requires` whose result under σ is not `true`, or its
premise predicate is false under σ. -/
inductive RuleReqFails (c : Semantics) (σ : Subst) (r : Rule) : Prop where
  | intro {t : Term} {v : Option GroundTerm} (ht : r.req = some t) (he : EvalTerm c σ t v)
      (hv : v ≠ some (bool true)) : RuleReqFails c σ r
  | pre (h : Holds c r.vars.length σ r.pre false) : RuleReqFails c σ r

/-- Rule r does not apply to x: under every σ that gives the variables of its left side and its
conditions values of their sorts and under which its left side denotes x, a condition fails. -/
def NotApplies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x → RuleReqFails c σ r

inductive Step (c : Semantics) : Config c → Config c → Prop where
  | rule {x y : Config c} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
      (hσ : c.WellSorted r.vars σ)
      (hmatch : PatVal c σ r.lhs x.val)
      (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
      (hpre : Holds c r.vars.length σ r.pre true)
      (heval : EvalTerm c σ r.rhs (some y.val))
      (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
      (hpost : Holds c r.vars.length σ r.post true)
      (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) : Step c x y

/-- `Step.rule`'s premises for the rule r and the substitution σ. -/
structure StepBy (c : Semantics) (r : Rule) (σ : Subst) (x y : Config c) : Prop where
  mem : r ∈ c.rules
  hσ : c.WellSorted r.vars σ
  hmatch : PatVal c σ r.lhs x.val
  hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true))
  hpre : Holds c r.vars.length σ r.pre true
  heval : EvalTerm c σ r.rhs (some y.val)
  hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))
  hpost : Holds c r.vars.length σ r.post true
  hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val

theorem step_iff_by {c : Semantics} {x y : Config c} : Step c x y ↔ ∃ r σ, StepBy c r σ x y :=
  ⟨fun h => by
    cases h with
    | rule r mem σ hσ hmatch hreq hpre heval hens hpost hprio =>
      exact ⟨r, σ, ⟨mem, hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩⟩,
   fun ⟨r, σ, ⟨mem, hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩⟩ =>
    .rule r mem σ hσ hmatch hreq hpre heval hens hpost hprio⟩

/-- `RuleApplies c r x`: rule r applies to x: under some σ that gives the variables of its left side
and its conditions values of their sorts, its left-hand side denotes x, its `requires` evaluates to
`true` and its premise predicate holds. -/
def RuleApplies (c : Semantics) (r : Rule) (x : GroundTerm) : Prop :=
  ∃ σ, c.WellSortedAt r.vars r.leftVars σ ∧ PatVal c σ r.lhs x ∧
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true

/-- The evaluations the step at x reads have results: the left side's conditions wherever
`NotApplies` reads them, the right side's wherever `Step.rule` reads them. A result may be
"undefined" (`none`); what is excluded is an evaluation with no result at all. -/
def StepDecided (c : Semantics) (x : GroundTerm) : Prop :=
  ∀ r ∈ c.rules, (∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x) →
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b)

/-- σ is a match of r's left side at x that no rule of a smaller priority blocks. -/
def Unblocked (c : Semantics) (r : Rule) (σ : Subst) (x : GroundTerm) : Prop :=
  c.WellSortedAt r.vars (varOccs r.lhs) σ ∧ PatVal c σ r.lhs x ∧
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x

/-! ## A rule with the plain shapes

Where a rule's predicates are `\top` and its left side binds every variable, the premises above
are the ones without predicates over every variable. -/

/-- `\top` holds, and is never false. -/
theorem Holds.top_eq {c : Semantics} {n : Nat} {σ : Subst} {b : Bool} (h : Holds c n σ .top b) :
    b = true := by
  cases h; rfl

/-- σ that gives every variable a value gives each listed one a value. -/
theorem Semantics.WellSorted.at {c : Semantics} {vars : List Srt} {σ : Subst} (h : c.WellSorted vars σ)
    (is : List Nat) : c.WellSortedAt vars is σ :=
  fun i _ s hs => h i s hs

/-- Where the left side binds every variable, a σ that gives the variables of the left side and the
conditions values gives every variable one. -/
theorem Rule.wellSorted_of_at {c : Semantics} {r : Rule} (hb : binds r.vars.length (varOccs r.lhs) = true)
    {σ : Subst} (h : c.WellSortedAt r.vars r.leftVars σ) : c.WellSorted r.vars σ := by
  intro i s hs
  have hi : i < r.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  refine h i ?_ s hs
  have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  exact List.mem_append_left _ (List.contains_iff_mem.mp this)

/-- Where a clause's patterns bind every variable, a σ that gives the variables of the patterns and
the conditions values gives every variable one. -/
theorem Clause.wellSorted_of_at {c : Semantics} {cl : Clause}
    (hb : binds cl.vars.length (varOccsList cl.pats) = true)
    {σ : Subst} (h : c.WellSortedAt cl.vars cl.leftVars σ) : c.WellSorted cl.vars σ := by
  intro i s hs
  have hi : i < cl.vars.length := (List.getElem?_eq_some_iff.mp hs).1
  refine h i ?_ s hs
  have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
  exact List.mem_append_left _ (List.contains_iff_mem.mp this)

/-- The patterns of each clause of a generated sort predicate bind its one variable. -/
theorem Semantics.sortPreds_binds {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, -, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl <;>
    rcases hcl with rfl | rfl <;> rfl

/-- The premise predicate of each clause of a generated sort predicate is `\top`. -/
theorem Semantics.sortPreds_pre {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    ∀ cl ∈ fn.clauses, cl.pre = .top := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, -, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl <;>
    rcases hcl with rfl | rfl <;> rfl

theorem Rule.wellSortedAt_iff {c : Semantics} {r : Rule} (hb : binds r.vars.length (varOccs r.lhs) = true)
    {σ : Subst} : c.WellSortedAt r.vars r.leftVars σ ↔ c.WellSorted r.vars σ :=
  ⟨Rule.wellSorted_of_at hb, fun h => h.at _⟩

/-- A failing condition of a rule whose premise predicate is `\top` is a `requires` whose result
is not `true`. -/
theorem RuleReqFails.req_of_top {c : Semantics} {σ : Subst} {r : Rule} (hp : r.pre = .top)
    (h : RuleReqFails c σ r) :
    ∃ t v, r.req = some t ∧ EvalTerm c σ t v ∧ v ≠ some (bool true) := by
  cases h with
  | intro ht he hv => exact ⟨_, _, ht, he, hv⟩
  | pre h => rw [hp] at h; exact absurd (Holds.top_eq h) (by simp)

/-- `NotApplies` over every variable, for a rule whose left side binds every variable. -/
theorem NotApplies.of_wellSorted {c : Semantics} {r : Rule} {x : GroundTerm}
    (hb : binds r.vars.length (varOccs r.lhs) = true)
    (h : ∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x → RuleReqFails c σ r) : NotApplies c r x :=
  fun σ hσ hm => h σ (Rule.wellSorted_of_at hb hσ) hm

/-- `Step.rule` for a rule whose predicates are `\top`. -/
theorem Step.rule_top {c : Semantics} {x y : Config c} (r : Rule) (mem : r ∈ c.rules) (σ : Subst)
    (hpre : r.pre = .top) (hpost : r.post = .top)
    (hσ : c.WellSorted r.vars σ)
    (hmatch : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) : Step c x y :=
  .rule r mem σ hσ hmatch hreq (hpre ▸ .top) heval hens (hpost ▸ .top) hprio

end KCore
