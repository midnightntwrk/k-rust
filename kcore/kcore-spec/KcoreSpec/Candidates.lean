/-
  The rules that can fire on an instance of a pattern `t`: those whose left-hand side `overlap`s
  `t` (`candidates`, decided). A rule whose left-hand side `overlap` finds apart from `t` matches no
  value that `t` denotes (`Det.overlap_sound_term`), so a step from an instance of `t` is by a
  candidate (`Fires.mem_candidates`, `Step.candidate`), and a case split on a step needs one case
  per candidate only.

  `overlap_sound_term` reads both patterns as well sorted in a left-hand side's context
  (`patCtxAll`, which the matcher's context `patCtx` extends with the collection pattern symbols)
  under well-sorted valuations, in a core whose sorts and constructors are as matching reads them
  (`MatchCtx`). Here both are read in the matcher's context: a rule's left-hand side is so in a
  core that `ok` accepts (`Exec.ruleOK_of`); the pattern `t`, a symbolic state's term, is so by a
  decision on it.
-/
import KcoreSpec.SymbolicLemmas
import KcoreSpec.FnExclusive

set_option autoImplicit false

namespace KCore

variable {c : Semantics}

/-- The indices of the rules whose left-hand side `overlap`s `t`. -/
def candidates (c : Semantics) (t : Term) : List Nat :=
  (List.range c.rules.length).filter fun i =>
    (c.rules[i]?.map fun r => overlap c.meet c.collHead r.lhs t).getD false

theorem mem_candidates_iff {t : Term} {i : Nat} {r : Rule} (hr : c.rules[i]? = some r) :
    i ∈ candidates c t ↔ overlap c.meet c.collHead r.lhs t = true := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  simp [candidates, List.mem_filter, List.mem_range, hi]

/-- A rule that fires on an instance of `t` is a candidate for `t`: `t` well sorted in the
matcher's context under a well-sorted σ, every rule's left-hand side well sorted there. -/
theorem Fires.mem_candidates (hmc : Exec.MatchCtx c)
    (hlhs : ∀ r ∈ c.rules, ∃ s, sortOfTerm c.patCtx r.vars r.lhs = some s)
    {vars : List Srt} {σ : Subst} {t : Term} {s : Srt}
    (hσ : c.WellSorted vars σ) (ht : sortOfTerm c.patCtx vars t = some s)
    {x y : Config c} (hx : PatVal c σ t x.val) {r : Rule} {σ' : Subst} (hr : r ∈ c.rules)
    (hf : Fires c r σ' x y) : ∃ i ∈ candidates c t, c.rules[i]? = some r := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  refine ⟨i, (mem_candidates_iff hi).mpr ?_, hi⟩
  cases ho : overlap c.meet c.collHead r.lhs t with
  | true => rfl
  | false =>
    obtain ⟨s', hs'⟩ := hlhs r hr
    exact (Det.overlap_sound_term hmc hf.1 hσ r.lhs (sortOfTerm_nf_of_nil (Semantics.fnOvlSyms_of_noOvl hmc.noOvl)
        (sortOfTerm_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) _ _ hs'))
      (sortOfTerm_nf_of_nil (Semantics.fnOvlSyms_of_noOvl hmc.noOvl)
        (sortOfTerm_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) _ _ ht)) ho hf.2.1 hx).elim

/-- A step from an instance of `t` is by a candidate rule for `t`, which fires. -/
theorem Step.candidate (hmc : Exec.MatchCtx c)
    (hlhs : ∀ r ∈ c.rules, ∃ s, sortOfTerm c.patCtx r.vars r.lhs = some s)
    {vars : List Srt} {σ : Subst} {t : Term} {s : Srt}
    (hσ : c.WellSorted vars σ) (ht : sortOfTerm c.patCtx vars t = some s)
    {x y : Config c} (hx : PatVal c σ t x.val) (h : Step c x y) :
    ∃ i ∈ candidates c t, ∃ r, c.rules[i]? = some r ∧ ∃ σ', Fires c r σ' x y :=
  let ⟨r, σ', ⟨i, hi, hr⟩, hf⟩ := Step.cases_of (Fires.mem_candidates hmc hlhs hσ ht hx) h
  ⟨i, hi, r, hr, σ', hf⟩

/-- In a core that `ok` accepts, every rule's left-hand side is well sorted in the matcher's
context. -/
theorem lhs_sorted_of_okM (hok : c.okM = true) :
    ∀ r ∈ c.rules, ∃ s, sortOfTerm c.patCtx r.vars r.lhs = some s :=
  fun _ hr => ⟨_, (Exec.ruleOKM_of hok hr).1⟩

theorem lhs_sorted_of_ok (hok : c.ok = true) :
    ∀ r ∈ c.rules, ∃ s, sortOfTerm c.patCtx r.vars r.lhs = some s :=
  lhs_sorted_of_okM (Semantics.okM_of_ok hok)

/-- `Fires.mem_candidates` in a core that `ok` and `matchReady` accept, with the candidates
given as `is`: the two side conditions on `t` are decided (`decide +kernel`) once `is` is
written down, and a case split on `i ∈ is` has one case per candidate. -/
theorem Fires.mem_of_candidates (hok : c.ok = true) (hmr : c.matchReady = true)
    {vars : List Srt} {t : Term} (ht : (sortOfTerm c.patCtx vars t).isSome = true)
    {is : List Nat} (hc : candidates c t = is) {σ : Subst} (hσ : c.WellSorted vars σ)
    {x y : Config c} (hx : PatVal c σ t x.val) {r : Rule} {σ' : Subst} (hr : r ∈ c.rules)
    (hf : Fires c r σ' x y) : ∃ i ∈ is, c.rules[i]? = some r := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp ht
  exact hc ▸ Fires.mem_candidates (Exec.matchCtx_of hmr) (lhs_sorted_of_ok hok) hσ hs hx hr hf

end KCore
