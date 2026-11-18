/-
  KCore, checked layer: `clauseFixed` decides match independence (`MatchIndependent`,
  EvalFunctional.lean). The patterns of a clause it accepts fix the clause's variables: two
  well-sorted matches at one argument list agree on all of them (`uniqList_sound`), so on those of
  the right-hand side and the `ensures`: the same instance of both, `Coherent`'s first alternative
  (`clauseFixed_sound`). The clauses
  it does not confirm are named obligations (`matchObligations`, `MatchObligations`); with them, every
  clause of a core that `ok` and `matchReady` accept is match independent (`matchIndependentAll_of`).
-/
import KcoreSpec.EvalFunctional
import KcoreSpec.Uniq

set_option autoImplicit false

namespace KCore

open KCore.Exec

variable {c : Semantics}

/-- A clause without existential variables that `clauseFixed` accepts is match independent: its patterns, well sorted in a
left-hand side's context without function-overloaded symbols (`patCtxNF`), fix all of its variables, and its right-hand side's and
its `ensures`' are among them. -/
theorem clauseFixed_sound {cl : Clause} {ss : List Srt} {x : TermCtx} {s : Srt} (hmc : MatchCtxO c)
    (hpt : sortsOfTerms c.patCtxNF cl.vars cl.pats = some ss)
    (hrt : sortOfTerm x cl.vars cl.rhs = some s) (hens : reqOK x cl.vars cl.ens = true)
    (hfx : c.clauseFixed cl = true) (hx : cl.exs = []) :
    MatchIndependent c cl := by
  refine ⟨?_, fun hne => absurd hx hne⟩
  intro vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ _
  unfold Semantics.clauseFixed at hfx
  split at hfx
  · rename_i D hD
    simp only [List.all_eq_true, List.contains_iff_mem, List.mem_range] at hfx
    have hag : ∀ i, i < cl.vars.length → σ.lookup i = σ'.lookup i := fun i hi =>
      Det.uniqList_sound hmc ((wellSortedAt_univ hx).mp hσ) ((wellSortedAt_univ hx).mp hσ') cl.pats hD hm hm' hpt (fun _ h => by cases h) i (hfx i hi)
    refine .inl ⟨hx, hx, rfl, rfl, fun i hi => hag i (sortOfTerm_vars hrt i hi), fun t ht i hi => ?_⟩
    rw [ht] at hens
    exact hag i (sortOfTerm_vars (reqOK_some hens) i hi)
  · cases hfx

/-- Each clause that `matchObligations` names is match independent: the obligation, as
`Obligations` (Statements.lean) states it. -/
def MatchObligations (c : Semantics) : Prop :=
  ∀ p ∈ c.matchObligations, ∀ fn, c.lookupFn p.1 = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
    MatchIndependent c cl

theorem MatchObligations.of_nil (h : c.matchObligations = []) : MatchObligations c :=
  fun p hp => by rw [h] at hp; exact absurd hp List.not_mem_nil

/-- With every clause fixed and no overloading symbol, no clause is named. -/
theorem matchObligations_nil_of_fixed (h : c.clausesFixed = true) (hno : c.ovls = []) : c.matchObligations = [] := by
  simp only [Semantics.clausesFixed, Semantics.allFns, List.all_append, Bool.and_eq_true,
    List.all_eq_true] at h
  simp only [Semantics.matchObligations, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_true', Bool.not_eq_false]
  intro f hf i hi
  rw [List.getElem?_eq_getElem hi, Option.all_some, hno]
  exact h.1 f hf _ (List.getElem_mem hi)

theorem clausesFixed_of_nil (h : c.matchObligations = []) : c.clausesFixed = true := by
  simp only [Semantics.matchObligations, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.mem_range] at h
  simp only [Semantics.clausesFixed, Semantics.allFns, List.all_append, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨fun f hf cl hcl => ?_, fun f hf cl hcl => sortPreds_fixed hf cl hcl⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  have := h f hf i hi
  rw [List.getElem?_eq_getElem hi, Option.all_some] at this
  simp at this
  exact this.2

theorem MatchObligations.of_fixed (h : c.clausesFixed = true) (hno : c.ovls = []) : MatchObligations c :=
  .of_nil (matchObligations_nil_of_fixed h hno)

/-- **Every clause is match independent** in a core that `okM` and `matchReady` accept, given the
named obligations: a clause `clauseFixed` confirms by `clauseFixed_sound` (its patterns sorted as
`okM` checks them), the others by their obligation. The sort predicates' clauses are fixed
(`sortPreds_fixed`). -/
theorem matchIndependentAll_of_okM (hok : c.okM = true) (hmr : c.matchReady = true)
    (hob : MatchObligations c) : MatchIndependentAll c := by
  intro f fn hfn cl hcl
  obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
  obtain ⟨L, _, hclk⟩ := clauseCtx_of_okM hok fn hmem
  obtain ⟨hpt, _, _, _, hrt, hens, _, hx, _⟩ := hclk cl hcl
  cases hfx : c.clauseFixed cl with
  | true => exact clauseFixed_sound (matchCtx_of hmr) (sortsOfTerms_nf_of_nil
      (Semantics.fnOvlSyms_of_noOvl (matchCtx_of hmr).noOvl)
      (sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) _ _ hpt)) hrt hens hfx hx
  | false =>
    rcases List.mem_append.mp hmem with hf | hp
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
      refine hob (fn.label, i) ?_ fn (by rw [hlab]; exact hfn) _ (List.getElem?_eq_getElem hi)
      simp only [Semantics.matchObligations, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Prod.mk.injEq]
      refine ⟨fn, hf, i, ⟨hi, ?_⟩, rfl, rfl⟩
      simp [List.getElem?_eq_getElem hi, hfx, (matchCtx_of hmr).noOvl]
    · exact absurd (sortPreds_fixed hp cl hcl) (by rw [hfx]; decide)

/-- **Every clause is match independent** in a core that `ok` and `matchReady` accept, given the
named obligations (`matchIndependentAll_of_okM`). -/
theorem matchIndependentAll_of (hok : c.ok = true) (hmr : c.matchReady = true)
    (hob : MatchObligations c) : MatchIndependentAll c :=
  matchIndependentAll_of_okM (Semantics.okM_of_ok hok) hmr hob

end KCore
