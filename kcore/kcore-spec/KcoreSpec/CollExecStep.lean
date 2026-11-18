/-
  KCore, checked layer: the executable step of CollExec.lean on a core that `execReady` accepts.

  - `clauseComplete_of_ready`, `ruleComplete_of_ready`: the two matcher completeness statements
    soundness reads (`ClauseComplete`, `RuleComplete`, CollExecSound.lean) hold wherever
    `execReady` does, from `cmatch_complete` (CollExecMatch.lean): `execReady` gives the patterns'
    readiness, that they bind every variable, `MatchCtxO` (`matchReadyO`) and, through `sortedOK`,
    their sorts over `patCtxAll` (a generated sort predicate's clauses are sorted over `patCtx`
    already, `sortPreds_ctx`).
  - `successorsN_step_ready`, `successors_step_ready`: every successor the executable step lists is
    a `Step` successor, from `execReady` alone.
-/
import KcoreSpec.CollExecMatch

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-- The patterns of every clause of every function evaluation reads have the argument sorts over a
left-hand side's context. -/
theorem clausePats_sorted (hok : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args := by
  rcases List.mem_append.mp hfn with hfn' | hfn'
  · replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    have := hok.1.2 fn hfn' cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact this.1.1.1.1.1
  · exact sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats (sortPreds_ctx hfn' cl hcl).1

/-- The left-hand side of every rule has the configuration sort over a left-hand side's context. -/
theorem rulePat_sorted (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort := by
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  exact (Semantics.ruleSorted_parts c (hok.2 r hr)).1

/-- The patterns of every clause of every function evaluation reads have the argument sorts over
the context without function-overloaded symbols: a function's by `ovlPatsOK`, a sort predicate's
because its patterns are sorted over the matcher's context. -/
theorem clausePats_nf (hok : c.sortedOK = true) (hmc : MatchCtxO c) {fn : Fn} (hfn : fn ∈ c.allFns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) : sortsOfTerms c.patCtxNF cl.vars cl.pats = some fn.args :=
  Semantics.pats_nf hmc.ovlHyp hfn hcl (clausePats_sorted hok hfn hcl)

/-- The left-hand side of every rule has the configuration sort over the context without
function-overloaded symbols (`ovlPatsOK`). -/
theorem rulePat_nf (hok : c.sortedOK = true) (hmc : MatchCtxO c) {r : Rule} (hr : r ∈ c.rules) :
    sortOfTerm c.patCtxNF r.vars r.lhs = some topCellSort :=
  sortOfTerm_to_nf _ (rulePat_sorted hok hr) (Semantics.ovlPats_lhs (Semantics.overloadsOK_pats hmc.ovlOK) hr)

/-- **The clauses' matcher is complete** where `execReady` holds. -/
theorem clauseComplete_of_ready (hr : execReady c = true) : ClauseComplete c := by
  simp only [execReady, Bool.and_eq_true, List.all_eq_true] at hr
  replace hr := hr.1
  obtain ⟨⟨⟨⟨⟨hok, -⟩, hmr⟩, hfns⟩, -⟩, -⟩ := hr
  intro fn hfn cl hcl vs τ _ hτ hpv
  have h1 := hfns fn hfn cl hcl
  exact cmatch_complete (matchCtxO_of hmr) (Clause.wellSorted_of_at h1.2 hτ) hpv h1.1 h1.2
    (clausePats_nf hok (matchCtxO_of hmr) hfn hcl)

/-- No clause is `aside` where `execReady` holds. -/
theorem asideFree_of_ready (hr : execReady c = true) : c.AsideFree := by
  simp only [execReady, Bool.and_eq_true] at hr
  have h2 : c.asideFree = true := hr.1.2
  exact @Semantics.asideFree_spec c h2

/-- **The rules' matcher is complete** where `execReady` holds. -/
theorem ruleComplete_of_ready (hr : execReady c = true) : RuleComplete c := by
  have hr' := hr
  simp only [execReady, Bool.and_eq_true, List.all_eq_true] at hr
  replace hr := hr.1
  obtain ⟨⟨⟨⟨⟨hok, -⟩, hmr⟩, -⟩, hrules⟩, -⟩ := hr
  intro r hr x τ _ hτ hpv
  have h1 := hrules r hr
  exact cmatch_complete (matchCtxO_of hmr) (Rule.wellSorted_of_at (rule_atoms_of_execReady hr' hr).2.2 hτ)
    (.cons hpv .nil) h1.1.1.1
    (by simpa [varOccsList] using h1.1.1.2)
    (sortsOfTerms_cons.mpr ⟨_, _, rulePat_nf hok (matchCtxO_of hmr) hr, sortsOfTerms_nil.mpr rfl, rfl⟩)

/-- Every successor the executable step lists, at any fuel, is a `Step` successor, where
`execReady` holds. -/
theorem successorsN_step_ready (hr : execReady c = true) {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : y ∈ successorsN c n x.val) : ∃ h : c.sortOf y = some topCellSort, Step c x ⟨y, h⟩ := by
  have hr' := hr
  simp only [execReady, Bool.and_eq_true] at hr'
  replace hr' := hr'.1
  exact successorsN_step hr'.1.1.1.1.1 hr'.1.1.1.1.2 (matchCtxO_of hr'.1.1.1.2).ovlCase
    (clauseComplete_of_ready hr) (ruleComplete_of_ready hr) hy

/-- **The executable step is sound** where `execReady` holds: every successor `CExec.successors`
lists is a `Step` successor. -/
theorem successors_step_ready (hr : execReady c = true) {x : Config c} {y : GroundTerm}
    (hy : y ∈ successors c x.val) : ∃ h : c.sortOf y = some topCellSort, Step c x ⟨y, h⟩ :=
  successors_step_of_ready hr (clauseComplete_of_ready hr) (ruleComplete_of_ready hr) hy

end KCore.CExec
