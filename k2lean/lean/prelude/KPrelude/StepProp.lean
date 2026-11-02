import KPrelude.Invariant
import KPrelude.Measure

/-!
# A fact of every step (`gen --step-property`, `docs/design.md` §3.12)

A step property relates a cell's content before and after each step: the author writes a `Bool`
K function `P` of two contents of one cell (`feesUp(F1, F2) => F1 <=Int F2`), and
`gen --step-property NAME@CELL` states, per rule, that the rule's step relates its source and
target by it (`Step.Rel.r StepProp.holds`, the per-rule principle that measures, refinements,
confluence and noninterference state their obligations with). It is not an invariant, a fact of
one state: "never decreases" relates two states. Where `P` is transitive (an obligation of its
own, never assumed), the fact holds between a configuration and every one reached from it in one
or more steps (`plus_of_step`).

`k2l_step [unfold] [lemmas]` proves one rule's case, and the transitivity obligation, by the
measure's stages (`k2l_measure`): the rule's variables of one value form taken apart, the
property and the functions it calls unfolded by their proved equations, the author's lemmas at
each call, a case split on the calls left, then the hooks in Lean's arithmetic. Nothing in those
stages is specific to `Lower`: they read any obligation whose definitions unfold to `Int` and
`Bool` arithmetic over the values of K functions.
-/

namespace KPrelude.StepProp

universe u

variable {α : Type u} {S Q : α → α → Prop}

/-- A relation that every step satisfies and that is transitive holds along every path of one or
more steps. -/
theorem plus_of_step (hs : ∀ {c c' : α}, S c c' → Q c c')
    (ht : ∀ {a b c : α}, Q a b → Q b c → Q a c) {c c' : α} (h : Relation.TransGen S c c') :
    Q c c' := by
  induction h with
  | single hab => exact hs hab
  | tail _ hbc ih => exact ht ih (hs hbc)

/-- `k2l_step [unfold] [lemmas]`: one rule's case `Step.Rel.r Q` of a step property, or its
transitivity, by the measure's stages with no sums (module doc). -/
macro "k2l_step" " [" us:ident,* "]" " [" ls:ident,* "]" : tactic =>
  `(tactic| k2l_measure [$us,*] [$ls,*] [] [])

end KPrelude.StepProp
