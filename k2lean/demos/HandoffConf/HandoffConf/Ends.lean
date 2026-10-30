import HandoffConf.Slots
import HandoffConf.Live
import KPrelude.Ends
import KPrelude.InvDisjoint

/-! Every order of the script's tasks ends (`direction.md` §5, a finite execution): the work left,
a weight on the tasks, drops at every step (`work_lt`), so `handoff` terminates from every
configuration, with no hypothesis (`terminates`). Each task weighs what its `<k>` has yet to do:
`1` for nothing (`done` removes it), `2` for an instruction (it runs, then `done`), and `3` per
instruction of a program plus `2` (`fork` moves one instruction out, then `nil` and `done`).
With the confluence of `HandoffConf.Slots`, every run from a configuration satisfying the script's
well-formedness ends, all in one configuration (`every_order_same`). -/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HandoffConf

variable [Handoff.Hooks]

open KPrelude

/-- The work left in a `<k>`. -/
def kWork : Handoff.SortK → Nat
  | .dotk => 1
  | .kseq (.inj_Instr _) .dotk => 2
  | .kseq (.inj_Pgm P) .dotk => 3 * (iinstrs P).length + 2
  | _ => 0

/-- The work left in a task. -/
def taskWork : Handoff.SortTaskCell → Nat
  | .«<task>» _ _ (.«<k>» K) => kWork K

/-- The work left in a map of tasks. -/
def work (m : Handoff.SortTaskCellMap) : Nat :=
  ((ListIso.toList m).map fun p => taskWork p.2).sum

theorem work_concat {a b m : Handoff.SortTaskCellMap} (h : MapHook.concat a b = some m) :
    work m = work a + work b := by
  unfold work
  rw [((MapHook.perm_toList_concat h).map _).sum_nat, List.map_append, List.sum_append_nat]

theorem work_element (k : Handoff.SortTidCell) (t : Handoff.SortTaskCell) :
    work (MapHook.element k t) = taskWork t := by
  simp [work, MapHook.element, ListIso.toList_ofList]

/-- Every step lowers the work left by one. -/
theorem work_lt {c c' : Handoff.SortGeneratedTopCell} (h : Handoff.Step c c') :
    work (tasks c') < work (tasks c) := by
  cases h with
  | fork _ _ _ _ _ _ _ I P _ _ hm _ hr hr₃ =>
    simp only [tasks]
    rw [work_concat hm, work_concat hr₃, work_concat hr]
    simp only [work_element, taskWork, kWork, iinstrs, List.length_cons]
    omega
  | nil _ _ _ _ _ _ _ _ hm hr =>
    simp only [tasks]
    rw [work_concat hm, work_concat hr]
    simp only [work_element, taskWork, kWork]
    omega
  | new _ _ _ _ _ _ _ _ _ _ _ hm hr =>
    simp only [tasks]
    rw [work_concat hm, work_concat hr]
    simp only [work_element, taskWork, kWork]
    omega
  | «resume-lit» _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm _ hr =>
    simp only [tasks]
    rw [work_concat hm, work_concat hr]
    simp only [work_element, taskWork, kWork]
    omega
  | «resume-oid» _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm _ _ hr =>
    simp only [tasks]
    rw [work_concat hm, work_concat hr]
    simp only [work_element, taskWork, kWork]
    omega
  | done _ _ _ _ _ _ _ hm =>
    simp only [tasks]
    rw [work_concat hm]
    simp only [work_element, taskWork, kWork]
    omega

/-- No infinite run of `handoff` starts anywhere. -/
theorem terminates (c : Handoff.SortGeneratedTopCell) : Paths.Terminates Handoff.Step c :=
  Ends.terminates_of_measure (fun c => work (tasks c)) (fun _ _ h => work_lt h) c

/-- Every run of `handoff` reaches a terminal configuration. -/
theorem every_run_ends (c : Handoff.SortGeneratedTopCell) :
    Ends.Every Handoff.Step c fun _ => True :=
  Ends.every_of (terminates c) fun _ _ _ => trivial

/-- Under the script's well-formedness, every order ends, all in one configuration. -/
theorem every_order_same {c : Handoff.SortGeneratedTopCell} (hinv : Handoff.Invariant c) :
    ∃ n, Star Handoff.Step c n ∧ Terminal Handoff.Step n ∧ Ends.Every Handoff.Step c (· = n) :=
  Ends.every_same (terminates c) fun _ _ h₁ t₁ h₂ t₂ => terminal_unique hinv h₁ t₁ h₂ t₂

#k2l_assert_axioms work_lt terminates every_run_ends every_order_same

end HandoffConf
