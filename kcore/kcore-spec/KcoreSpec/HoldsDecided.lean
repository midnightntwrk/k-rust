/-
  KCore. A well-sorted condition has a truth value, and the evaluations a step reads have results,
  for rules with any predicates.

  - `holds_decided`: a condition with `condOK` has a truth value (`∃ b, Holds … p b`) at every σ that
    gives its free variables (`varOccsCond`) values of their sorts, where every function has a result
    at arguments of its sorts (`HypSoundCore`, `FnTerminates`). A binder's truth value is read by
    classical choice of the truth value of its body at each extension of σ; no list of a sort's
    values is read.
  - `Rule.decided_pp`, `stepDecided_pp`: `Rule.decided_of_total` and `stepDecided_of_rules` for a
    well-sorted rule with any `pre` and `post`, without `rulePlainOpen`: every configuration is
    `StepDecided` where every rule is well sorted.
-/
import KcoreSpec.OpenStep

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

section
variable {c : Semantics}

/-- A well-sorted condition is true or false at such a σ. -/
theorem holds_true_or_false (h : HypSoundCore c) (hft : FnTerminates c) (p : Cond) {vars : List Srt}
    {σ : Subst} (hok : c.condOK vars p = true) (hσ : c.WellSortedAt vars (varOccsCond vars.length p) σ) :
    Holds c vars.length σ p true ∨ Holds c vars.length σ p false := by
  obtain ⟨b, hb⟩ := holds_decided h hft p hok hσ
  cases b with
  | true => exact .inl hb
  | false => exact .inr hb

/-- **The evaluations a step by a rule reads have results**, for a well-sorted rule with any
predicates: `Rule.decided_of_total` without `rulePlainOpen`. -/
theorem Rule.decided_pp (h : HypSoundCore c) (hft : FnTerminates c) {r : Rule}
    (hs : c.ruleSorted r = true) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b) := by
  obtain ⟨-, hreq, hens, hrhs⟩ := Semantics.ruleSorted_parts c hs
  have hs' := hs
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hpre⟩, -⟩, hpost⟩, -⟩, -⟩, -⟩ := hs'
  have hreqs : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hens; simpa [reqOK] using hens
  refine ⟨fun σ hσ _ => ⟨fun t ht => evalTerm_total_at h hft fns_headsOK
      (hσ.mono (Rule.req_leftVars ht)) (hreqs t ht),
      holds_decided h hft r.pre hpre (hσ.mono fun i hi =>
        List.mem_append_right _ (List.mem_append_right _ hi))⟩,
    fun σ hσ _ _ _ => ⟨Model.evalTerm_total h hft fns_headsOK hσ hrhs,
      fun e he => Model.evalTerm_total h hft fns_headsOK hσ (hensS e he),
      holds_decided h hft r.post hpost (hσ.at _)⟩⟩

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted: `stepDecided_of_rules` without `rulePlainOpen`. -/
theorem stepDecided_pp (h : HypSoundCore c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true) (x : GroundTerm) : StepDecided c x :=
  fun r hmem _ => Rule.decided_pp h hft (hr r hmem) x

end

end Faithful

open Faithful

/-- Every configuration of a semantics that `coreOK` accepts and whose functions meet `FnHyp` is
`StepDecided`: `stepDecided_pp` with the rules' `ruleSorted`, which `coreOK` gives. -/
theorem stepDecided_of_fnHyp {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) (x : Config c) :
    StepDecided c x.val :=
  stepDecided_pp (hypSound_of_core h) hf.1
    (fun r hr => List.all_eq_true.mp (by
      have hs := Semantics.sortedOK_sorted (Semantics.coreOK_parts h).1
      simp only [Bool.and_eq_true] at hs
      exact hs.2) r hr) x.val

end KCore
