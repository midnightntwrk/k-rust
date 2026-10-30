import KPrelude.Scaffold
import KPrelude.Paths

/-! Every run ends, and where (`direction.md` §1, §5). In a finite execution, such as a transaction
whose steps are the tasks of a script, "every run ends" is termination of the step relation, which a
measure that every step decreases proves (`terminates_of_measure`): no fairness assumption and no
temporal operator, only the runs of `KPrelude.Paths`. A maximal run from a configuration that
terminates reaches a terminal configuration (`ends_of_terminates`).

`Every S a Res` says that every run from `a` ends in a terminal configuration satisfying `Res`.
It composes termination, a property of one run, with what a comparison of runs says of the
terminal configurations reached: their uniqueness (confluence, `every_same`), or the result of a
reference run (`Forward.result_unique_of`), through `every_of`. -/

universe u

namespace KPrelude.Ends

variable {α : Type u} {S : α → α → Prop}

/-- A measure that every step from a configuration satisfying a preserved `H` decreases: no
infinite path starts where `H` holds. -/
theorem terminates_of_measure_on {H : α → Prop} (hH : Preserved S H) (μ : α → Nat)
    (hμ : ∀ (a b : α), H a → S a b → μ b < μ a) : ∀ a, H a → Paths.Terminates S a := by
  intro a
  induction a using measure_ind μ with
  | h a ih => exact fun ha => Acc.intro a fun b hb => ih b (hμ a b ha hb) (hH a b ha hb)

/-- A measure that every step decreases: no infinite path starts anywhere. -/
theorem terminates_of_measure (μ : α → Nat) (hμ : ∀ (a b : α), S a b → μ b < μ a) (a : α) :
    Paths.Terminates S a :=
  terminates_of_measure_on (H := fun _ => True) (fun _ _ _ _ => trivial) μ
    (fun a b _ h => hμ a b h) a trivial

/-- A maximal run from a configuration that terminates reaches a terminal configuration. -/
theorem ends_of_terminates {a : α} (h : Paths.Terminates S a) {s : Nat → α} (h0 : s 0 = a)
    (hs : Paths.IsRun S s) : ∃ n, Terminal S (s n) :=
  Classical.byContradiction fun hn => h.not_inf ⟨s, h0, fun n => by
    rcases hs n with hstep | ⟨-, ht⟩
    · exact hstep
    · exact (hn ⟨n, ht⟩).elim⟩

/-- Every run from `a` ends: it reaches a terminal configuration, which satisfies `Res`. -/
def Every (S : α → α → Prop) (a : α) (Res : α → Prop) : Prop :=
  ∀ s, s 0 = a → Paths.IsRun S s → ∃ n, Terminal S (s n) ∧ Res (s n)

/-- Termination, and `Res` at every terminal configuration reached: every run ends in `Res`. -/
theorem every_of {a : α} {Res : α → Prop} (h : Paths.Terminates S a)
    (hres : ∀ b, Star S a b → Terminal S b → Res b) : Every S a Res := by
  intro s h0 hs
  obtain ⟨n, ht⟩ := ends_of_terminates h h0 hs
  exact ⟨n, ht, hres _ (h0 ▸ Paths.IsRun.star hs n) ht⟩

/-- Some terminal configuration is reached from a configuration that terminates. -/
theorem exists_terminal_of_terminates {a : α} (h : Paths.Terminates S a) :
    ∃ b, Star S a b ∧ Terminal S b := by
  obtain ⟨s, h0, hs⟩ := Paths.exists_run (R := S) a
  obtain ⟨n, ht⟩ := ends_of_terminates h h0 hs
  exact ⟨s n, h0 ▸ Paths.IsRun.star hs n, ht⟩

/-- Termination and unique terminal configurations: every run ends, all in one configuration. -/
theorem every_same {a : α} (h : Paths.Terminates S a)
    (huniq : ∀ (b₁ b₂ : α), Star S a b₁ → Terminal S b₁ → Star S a b₂ → Terminal S b₂ → b₁ = b₂) :
    ∃ c, Star S a c ∧ Terminal S c ∧ Every S a (· = c) := by
  obtain ⟨c, hc, ht⟩ := exists_terminal_of_terminates h
  exact ⟨c, hc, ht, every_of h fun b hb hbt => huniq b c hb hbt hc ht⟩

end KPrelude.Ends
