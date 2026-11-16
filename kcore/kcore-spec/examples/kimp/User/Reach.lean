/-
  An all-path reachability claim on kimp, proved with the symbolic layer in one symbolic step
  (`AllPath.step`): rule 23, `if (E) S` to `if (E) S else {}`, read as a claim from its left-hand
  side to its right-hand side. Of kimp's 79 rules, only rule 23's left-hand side overlaps the
  claim's (`candidates`, decided), so the coverage half has one case: no case split over the rules.
-/
import Kimp.Surface
import KcoreSpec.Candidates

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Kimp.Reach

open KCore KCore.Reachability

/-- A rule without a `requires` read as a claim: its variables universal, from its left-hand side
to its right-hand side read as a pattern. -/
def ruleClaim (r : Rule) : Claim := ⟨⟨r.vars, r.lhs, fun _ => True⟩, ⟨r.vars, r.rhs, fun _ => True⟩⟩

/-- No rule has a smaller priority than another: all have priority 50. -/
theorem no_prio {r : Rule} (h : r ∈ c.rules) {x : GroundTerm} :
    ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x := by
  have hp : c.rules.all (·.prio == 50) = true := by decide +kernel
  intro r' hr' hlt
  have h1 := List.all_eq_true.mp hp r h
  have h2 := List.all_eq_true.mp hp r' hr'
  simp only [beq_iff_eq] at h1 h2
  omega

/-- Rule 23 as a claim holds on every complete path. -/
theorem rule23_valid {r : Rule} (hr : c.rules[23]? = some r) : (ruleClaim r).AllPathValid c := by
  obtain rfl := Option.some.inj (rule23.symm.trans hr)
  intro ρ
  refine AllPath.step (P' := (ruleClaim _).post.DenFrom c 5 ρ) ?_ (AllPath.refl fun _ h => h)
  rintro x ⟨hρ, hx, -⟩
  -- the configuration: `if (E) S ~> K` in the k cell, ρ's values in the others
  obtain ⟨u0, h0, -⟩ := hρ 0 _ rfl
  obtain ⟨u1, h1, -⟩ := hρ 1 _ rfl
  obtain ⟨u2, h2, -⟩ := hρ 2 _ rfl
  obtain ⟨u3, h3, -⟩ := hρ 3 _ rfl
  obtain ⟨u4, h4, -⟩ := hρ 4 _ rfl
  have hx' := (PatVal.iff_inst (by decide +kernel)).mp hx
  simp [ruleClaim, h0, h1, h2, h3, h4] at hx'
  -- progress: the right-hand side's value under ρ
  refine ⟨Step.progress_of_rule ok srReady hr hρ hx (fun _ h => nomatch h)
    (no_prio (List.mem_of_getElem? hr))
    (v := .ctor topLabel [.ctor Sym.«<k>» [.ctor kseq [.inj Srt.«Stmt» KCore.Srt.kitem
      (.ctor Sym.«if(_)_else__IMP-SYNTAX_Stmt_Expr_Stmt_Stmt» [u0, u1, .ctor Sym.«{}_IMP-SYNTAX_Stmt» []]), u2]], u3, u4])
    (by simp (disch := decide +kernel) [EvalTerm.ctor_iff, h0, h1, h2, h3, h4, allSome]) (fun _ h => nomatch h), ?_⟩
  -- coverage: rule 23 is the only candidate, and gives the right-hand side's value
  intro y hy
  obtain ⟨r', σ, ⟨i, hi, h⟩, -, hm, -, he, -⟩ := Step.cases_of
    (Fires.mem_of_candidates ok matchReady (is := [23]) (by decide +kernel) (by decide +kernel) hρ hx) hy
  cases List.mem_singleton.mp hi; cases rule23.symm.trans h
  rw [← hx'] at hm
  refine ⟨ρ, fun _ _ => rfl, hρ, ?_, trivial⟩
  simp (disch := decide +kernel) [PatVal.app_ctor_iff, PatVal.app_inj_iff] at hm
  obtain ⟨⟨⟨g0, g1⟩, g2⟩, g3, g4⟩ := hm
  simp (disch := decide +kernel) [EvalTerm.ctor_iff, g0, g1, g2, g3, g4, allSome] at he
  simp (disch := decide +kernel) [ruleClaim, PatVal.app_ctor_iff, he, h0, h1, h2, h3, h4]

end Kimp.Reach
