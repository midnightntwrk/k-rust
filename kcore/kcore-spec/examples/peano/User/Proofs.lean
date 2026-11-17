/-
  Peano's eleven properties, from the generated package (`Peano.deterministic`, `Peano.step_iff`,
  `Peano.counter_invariant`) and the decisions of User/Facts.lean. No per-rule proof.
-/
import User.Facts

set_option autoImplicit false

namespace Peano

open KCore

theorem deterministic' : deterministic.statement := fun _ _ _ h h' => deterministic c.hooks h h'

private theorem lfPred : c.lookupFn Sym.«pred» = some (c.fns[0]'(by decide +kernel)) := rfl

/-- No clause of `pred` has a priority below 50. -/
private theorem pred_prios : ∀ cl ∈ (c.fns[0]'(by decide +kernel)).clauses, ¬ cl.prio < 50 := by decide +kernel

theorem pred_succ : pred_succ.statement := fun N hN =>
  .clause (σ := [(0, N)]) lfPred (List.mem_cons_self ..)
    (fun i s h => by
      cases i with
      | zero => cases h; exact ⟨N, rfl, hN⟩
      | succ i => cases h)
    (.cons (.ctor rfl (.cons (.var rfl) .nil)) .nil) (fun _ h => nomatch h) .top
    (fun cl hcl _ hlt => absurd hlt (pred_prios cl hcl)) .var (fun _ h => nomatch h)

theorem pred_owise : pred_owise.statement := fun N hS hN =>
  .clause (σ := [(0, N)]) lfPred (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (fun i s h => by
      cases i with
      | zero => cases h; exact ⟨N, rfl, hS⟩
      | succ i => cases h)
    (.cons (.var rfl) .nil) (fun _ h => nomatch h) .top
    (fun cl hcl _ hlt => by
      rcases List.mem_cons.mp hcl with rfl | hcl
      · refine .intro fun σ _ hm => ?_
        cases hm with
        | cons h _ => cases h with
          | hook hp _ _ => exact absurd hp (by decide)
          | coll hc _ _ _ => exact absurd hc (by decide)
          | ovl hc _ _ _ => exact absurd hc (by decide)
          | ctor _ hs => cases hs with
            | cons _ hs' => cases hs' with
              | nil => exact absurd rfl (hN _)
      · rw [List.mem_singleton.mp hcl] at hlt; exact absurd hlt (by decide))
    (.ctor rfl .nil) (fun _ h => nomatch h)

theorem counterIs_iff (ctr v : GroundTerm) : (∃ k, v = top k ctr) ↔ v.atPath counterPath = some ctr := by
  constructor
  · rintro ⟨k, rfl⟩; rfl
  · intro h
    obtain ⟨vs, u, rfl, hl, hu, hw⟩ := GroundTerm.atPath_arg h
    cases hw
    match vs, hl, hu with
    | [k, _], _, hu => cases hu; exact ⟨k, rfl⟩

/-- The generated counter kind, with no obligations. -/
theorem counterIs_invariant : counterIs_invariant.statement := fun ctr =>
  ⟨fun _ h => h, fun x y hx hs => (counterIs_iff ctr y.val).mpr
    ((counter_invariant c.hooks ctr (fun _ h => nomatch h)).2 x y ((counterIs_iff ctr x.val).mp hx) hs)⟩

theorem counterIs_reach : counterIs_reach.statement := fun ctr _ _ hx hr =>
  (counterIs_invariant ctr).reach hx hr

/-- A configuration where the guard holds holds `z` in a `done(_)` at the head of its k cell. -/
theorem doneHoldsZero_of_guard (y : GroundTerm) (hg : doneGuard.Holds y) :
    ∀ v ctr, y = cfg (done v) ctr → v = natVal z :=
  fun v ctr hy => Option.some.inj (hg (done v) (by rw [hy]; rfl) rfl)

/-- The guard every step leaves (no obligations); a start configuration has `run(_)`, not
`done(_)`, at the head of its k cell. -/
theorem doneHoldsZero_invariant : doneHoldsZero_invariant.statement :=
  ⟨fun x ⟨n, ctr, hx⟩ v ctr' h => by
    rw [hx] at h
    injection h with _ h; injection h with h _
    injection h with _ h; injection h with h _
    injection h with _ h; injection h with h _
    injection h with _ _ h; injection h with h _
    exact absurd h (by decide),
   invariant_of_steps (Inv' := fun v => ∀ v' ctr, v = cfg (done v') ctr → v' = natVal z)
    (fun r h => (guard_sound doneGuard r h).mono fun _ y hy _ => doneHoldsZero_of_guard y hy)
    guardDone (fun _ h => nomatch h)⟩

theorem doneHoldsZero_reach : doneHoldsZero_reach.statement := fun _ _ hx hr =>
  doneHoldsZero_invariant.reach hx hr

/-- With no match of any rule at x, the executable step lists nothing. -/
theorem successorsN_nil (n : Nat) (x : GroundTerm)
    (h : ∀ r ∈ c.rules, Exec.ruleMatches c n r x = []) : Exec.successorsN c n x = [] := by
  unfold Exec.successorsN
  have hf : (c.rules.map fun r => (r, Exec.ruleMatches c n r x)).filter
      (fun (_, l) => l.any fun (_, b) => b != some false) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      simp [h r hr]
  simp only [hf, List.map_nil, List.min?_nil]

theorem stuck_of {x : Config c}
    (h : c.rules.all (fun r => ((Exec.matchP c (Exec.patFuel [r.lhs]) [] r.lhs x.val).filter
      (Exec.wellSorted c r.vars)).isEmpty) = true) (y : Config c) : ¬ Step c x y := by
  intro hs
  obtain ⟨n, hn⟩ := (step_iff x y).mp hs
  rw [successorsN_nil n x.val fun r hr => by
    simp only [Exec.ruleMatches, List.isEmpty_iff.mp (List.all_eq_true.mp h r hr), List.map_nil]] at hn
  cases hn

theorem step_run_succ : step_run_succ.statement :=
  let x : Config c := ⟨_, sorted_runSZ⟩
  let ⟨y, hy, hsy⟩ := List.any_eq_true.mp succ_runSZ
  let ⟨hs, hst⟩ := Det.step_of_mem (x := x) ok srReady matchReady hy
  ⟨x, ⟨y, hs⟩, rfl, Exec.same_iff.mp hsy, hst⟩

theorem step_run_zero : step_run_zero.statement :=
  let x : Config c := ⟨_, sorted_runZ⟩
  let ⟨y, hy, hsy⟩ := List.any_eq_true.mp succ_runZ
  let ⟨hs, hst⟩ := Det.step_of_mem (x := x) ok srReady matchReady hy
  ⟨x, ⟨y, hs⟩, rfl, Exec.same_iff.mp hsy, hst⟩

theorem stuck_done : stuck_done.statement := ⟨⟨_, sorted_doneZ⟩, rfl, stuck_of nomatch_doneZ⟩

theorem doneHoldsZero_fails : doneHoldsZero_fails.statement :=
  ⟨⟨_, sorted_doneSZ⟩, rfl, fun h => by
    have := h (natVal (s z)) ctr0 rfl
    injection this with _ _ h'
    injection h' with h''
    exact absurd h'' (by decide)⟩

-- the axioms of all eleven
#eval show Lean.CoreM Unit from do
  for n in [``deterministic', ``pred_succ, ``pred_owise, ``step_run_succ, ``step_run_zero, ``stuck_done,
      ``doneHoldsZero_fails, ``doneHoldsZero_invariant, ``doneHoldsZero_reach, ``counterIs_invariant,
      ``counterIs_reach] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end Peano
