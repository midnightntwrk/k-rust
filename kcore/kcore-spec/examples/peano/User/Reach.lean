/-
  All-path reachability claims on peano, proved with the symbolic layer, one symbolic step each
  (`AllPath.step`): the rule fires on every instance of the claim's left-hand side (progress), and
  every step from it lands on the instance of the right-hand side at the same valuation (coverage:
  the rule is the only one whose left-hand side overlaps the claim's, `candidates`, decided, so a
  step is by it: `Fires.mem_of_candidates`, KcoreSpec/Candidates.lean). The instance of a
  left-hand side is read by `PatVal.iff_inst`; a known configuration against a rule's left-hand
  side by the value-directed lemmas (KcoreSpec/SymbolicLemmas.lean).

  - Rule 1 read as a claim, from its left-hand side to its right-hand side.
  - Rule 0 read as a claim, with `pred(Y)` read as its value. Its right-hand side read as a pattern
    denotes nothing (`pred` is a function, not a constructor: `rule0_rhs_empty`), so the literal
    claim would say no complete path starts at `run(s(X))`, which is false; the true claim has
    `run(X)` there, `pred(s(X))` being `X` (`pred_s`).
-/
import User.Facts
import KcoreSpec.Candidates

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano.Reach

open KCore KCore.Reachability

/-- A rule without a `requires` read as a claim: its variables universal, from its left-hand side
to its right-hand side read as a pattern. -/
def ruleClaim (r : Rule) : Claim := ⟨⟨r.vars, r.lhs, fun _ => True⟩, ⟨r.vars, r.rhs, fun _ => True⟩⟩

/-- Both rules have priority 50: one case per rule (`rules_cases`). -/
theorem prio_all {r : Rule} (h : r ∈ c.rules) : r.prio = 50 := by
  rcases rules_cases h with h | h
  · cases rule0.symm.trans h; rfl
  · cases rule1.symm.trans h; rfl

/-- No rule has a smaller priority than another. -/
theorem no_prio {r : Rule} (h : r ∈ c.rules) {x : GroundTerm} :
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x :=
  fun _ hr' hlt => absurd hlt (by rw [prio_all hr', prio_all h]; omega)

/-- Rule 1 as a claim holds on every complete path. -/
theorem rule1_valid {r : Rule} (hr : c.rules[1]? = some r) : (ruleClaim r).AllPathValid c := by
  obtain rfl := Option.some.inj (rule1.symm.trans hr)
  intro ρ
  refine AllPath.step (P' := (ruleClaim _).post.DenFrom c 2 ρ) ?_ (AllPath.refl fun _ h => h)
  rintro x ⟨hρ, hx, -⟩
  -- the configuration: `run(z)` in the k cell, ρ's counter in the counter cell
  obtain ⟨u1, h1, -⟩ := hρ 1 _ rfl
  have hx' := (PatVal.iff_inst (by decide +kernel)).mp hx
  simp [ruleClaim, h1] at hx'
  obtain ⟨hxv, h0⟩ := hx'
  -- progress: the right-hand side's value under ρ
  refine ⟨Step.progress_of_rule ok srReady hr hρ hx (fun _ h => nomatch h)
    (no_prio (List.mem_of_getElem? hr)) (v := cfg (done (natVal z)) u1)
    (by simp (disch := decide +kernel) [EvalTerm.ctor_iff, h0, h1, allSome]) (fun _ h => nomatch h), ?_⟩
  -- coverage: rule 1 is the only candidate, and gives the right-hand side's value
  intro y hy
  obtain ⟨r', σ, ⟨i, hi, h⟩, -, hm, -, he, -⟩ := Step.cases_of
    (Fires.mem_of_candidates ok matchReady (is := [1]) (by decide +kernel) (by decide +kernel) hρ hx) hy
  cases List.mem_singleton.mp hi; cases rule1.symm.trans h
  rw [← hxv] at hm
  refine ⟨ρ, fun _ _ => rfl, hρ, ?_, trivial⟩
  simp (disch := decide +kernel) [PatVal.app_ctor_iff, PatVal.app_inj_iff] at hm
  simp (disch := decide +kernel) [EvalTerm.ctor_iff, hm.1, hm.2, allSome] at he
  simp (disch := decide +kernel) [ruleClaim, PatVal.app_ctor_iff, he, h0, h1]

/-- Rule 0's right-hand side read as a pattern denotes nothing: `pred` is a function. -/
theorem rule0_rhs_empty {r : Rule} (hr : c.rules[0]? = some r) {σ : Subst} {v : GroundTerm} :
    ¬ PatVal c σ r.rhs v := by
  obtain rfl := Option.some.inj (rule0.symm.trans hr)
  simp (disch := decide +kernel) [PatVal.ctor_iff_of_not_hook, PatVal.app_none_iff]

/-- Rule 0's claim with `pred(Y)` read as its value, `X` (`Y` is `s(X)`): from `run(s(X) #as Y)`
to `run(X)`, the counter kept. -/
def rule0Claim (r : Rule) : Claim :=
  ⟨⟨r.vars, r.lhs, fun _ => True⟩,
   ⟨r.vars, .app topLabel [.app Sym.«<k>» [.app kseq
     [.inj Srt.State KCore.Srt.kitem (.app Sym.run [.var 0]), .app dotk []]], .var 2],
    fun _ => True⟩⟩

/-- `pred`'s clauses but the first are of a priority above 50: the second, `[owise]`, of 200, and
there is no third. -/
theorem pred_clause_other {j : Nat} (hj : j ≠ 0) {cl' : Clause}
    (h : (c.lookupFn Sym.pred).bind (·.clauses[j]?) = some cl') : 50 < cl'.prio := by
  match j, hj with
  | 1, _ => rw [fn_pred_1] at h; cases h; decide
  | j + 2, _ =>
    cases hf : c.lookupFn Sym.pred with
    | none => rw [hf] at h; cases h
    | some fn =>
      have hl := fn_pred_sig
      rw [hf] at h hl
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      simp only [Option.bind_some] at h
      rw [List.getElem?_eq_none (by omega)] at h
      cases h

/-- No clause of `pred` has a priority below its first's. -/
theorem pred_no_lower (j : Nat) (cl' : Clause) (h : (c.lookupFn Sym.pred).bind (·.clauses[j]?) = some cl') :
    ¬ cl'.prio < 50 := by
  by_cases hj : j = 0
  · subst hj; rw [fn_pred_0] at h; cases h; decide
  · have := pred_clause_other hj h; omega

/-- `pred(s(u))` is `u`, and only `u`, for `u` a `Nat`: its first clause applies. -/
theorem pred_s {u : GroundTerm} (hu : c.sortOf u = some Srt.Nat) {r : Option GroundTerm} :
    Eval c Sym.pred [s u] r ↔ r = some u := by
  have hσ : c.WellSorted [Srt.Nat] [(0, u)] := fun i _ h => by
    cases i with
    | zero => cases h; exact ⟨u, rfl, hu⟩
    | succ => cases h
  have hm : PatVals c [(0, u)] [.app Sym.s [.var 0]] [s u] := by
    simp (disch := decide +kernel) [PatVal.app_ctor_iff]
  constructor
  · intro h
    obtain ⟨σ, -, hm', he⟩ :=
      Eval.inv_of_clause_bind fn_pred_0
        (fun j hj cl' hcl' hle => absurd hle (Nat.not_le.mpr (pred_clause_other hj hcl'))) rfl hσ hm h
    simp (disch := decide +kernel) [PatVal.app_ctor_iff] at hm'
    simpa [hm'] using he
  · rintro rfl
    exact Eval.of_clause_bind fn_pred_0 (fun j cl' hcl' hlt => absurd hlt (pred_no_lower j cl' hcl')) hσ hm
      (fun _ h => nomatch h) .var

/-- Rule 0's claim holds on every complete path. -/
theorem rule0_valid {r : Rule} (hr : c.rules[0]? = some r) : (rule0Claim r).AllPathValid c := by
  obtain rfl := Option.some.inj (rule0.symm.trans hr)
  intro ρ
  refine AllPath.step (P' := (rule0Claim _).post.DenFrom c 3 ρ) ?_ (AllPath.refl fun _ h => h)
  rintro x ⟨hρ, hx, -⟩
  -- the configuration: `run(s(X))` in the k cell, `Y` is `s(X)`
  obtain ⟨u0, h0, hs0⟩ := hρ 0 _ rfl
  obtain ⟨u1, h1, -⟩ := hρ 1 _ rfl
  obtain ⟨u2, h2, -⟩ := hρ 2 _ rfl
  have hx' := (PatVal.iff_inst (by decide +kernel)).mp hx
  simp [rule0Claim, h0, h1, h2] at hx'
  obtain ⟨hxv, rfl⟩ := hx'
  -- progress: the right-hand side's value under ρ, `pred(s(X))` being `X`
  refine ⟨Step.progress_of_rule ok srReady hr hρ hx (fun _ h => nomatch h)
    (no_prio (List.mem_of_getElem? hr)) (v := cfg (run u0) u2)
    (by simp (disch := decide +kernel) [EvalTerm.ctor_iff, EvalTerm.call_iff, h1, h2, allSome,
      pred_s hs0]) (fun _ h => nomatch h), ?_⟩
  -- coverage: rule 0 is the only candidate, and gives `run(X)`
  intro y hy
  obtain ⟨r', σ, ⟨i, hi, h⟩, -, hm, -, he, -⟩ := Step.cases_of
    (Fires.mem_of_candidates ok matchReady (is := [0]) (by decide +kernel) (by decide +kernel) hρ hx) hy
  cases List.mem_singleton.mp hi; cases rule0.symm.trans h
  rw [← hxv] at hm
  refine ⟨ρ, fun _ _ => rfl, hρ, ?_, trivial⟩
  simp (disch := decide +kernel) [PatVal.app_ctor_iff, PatVal.app_inj_iff] at hm
  simp (disch := decide +kernel) [EvalTerm.ctor_iff, EvalTerm.call_iff, hm.1.2, hm.2, allSome,
    pred_s hs0] at he
  simp (disch := decide +kernel) [rule0Claim, PatVal.app_ctor_iff, he, h0, h2]

end Peano.Reach
