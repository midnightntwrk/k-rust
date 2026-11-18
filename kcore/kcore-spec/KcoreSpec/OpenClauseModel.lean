/-
  KCore. The functions have one result and evaluation solves the equations (`FnDet`, `FnSolves`),
  for a semantics whose clauses are asked CN-4's bodies (`Semantics.sortedOKCl`), with no hypothesis
  on the sorts of the variables the patterns and conditions do not hold.

  One result is coherence (`fnDet_of_coherent`), which reads of the user's functions only the
  agreement of their equations and the match independence of their clauses
  (`coherentAll_ofCl`). Evaluation solves the equations where every function terminates
  (`fnSolves_of_totalCl`): a clause of a smaller priority than a deciding one has a result for its
  `requires` at each match, the match being well sorted on its patterns and conditions, which hold
  the `requires`' variables (`prioDecided_of_totalCl`, through `evalTerm_total_atCl`); and a clause
  instance that decides has a result, deciding giving a substitution well sorted on every variable
  (`coDefined_of_totalCl`). A clause with a variable of a sort without a value decides nowhere, so
  nothing is asked of its right side. `fnModel_of_fnHypCl` is `fnModel_of_fnHyp`'s conclusion.
-/
import KcoreSpec.OpenClauseFn
import KcoreSpec.RightHeldExtend

set_option autoImplicit false

namespace KCore

namespace Faithful

variable {c : Semantics}

/-- Every function's clauses are match independent, where the user's are: a sort predicate's
right-hand side has no variable. -/
theorem matchIndependentAll_ofCl (hmi : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) :
    MatchIndependentAll c := by
  intro f fn hfn cl hcl
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · exact hmi fn hu cl hcl
  · refine ⟨fun vs σ σ' _ _ _ _ _ _ _ => ?_, fun hne => absurd (Semantics.sortPreds_exs hp cl hcl) hne⟩
    refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
      fun i hi => absurd hi ?_, fun t ht => ?_⟩
    · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
      rw [hr, varOccs]
      exact List.not_mem_nil
    · rw [sortPreds_ens hp cl hcl] at ht; cases ht

/-- **The clauses of one priority are coherent** where each user function's equations agree and
its clauses are match independent (`CoherentAll_of` from what it reads). -/
theorem coherentAll_ofCl (hag : ∀ fn ∈ c.fns, ClausesAgree c fn)
    (hmi : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) : CoherentAll c :=
  coherentAll_of_parts (matchIndependentAll_ofCl hmi) fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hag fn hu
    · exact sortPreds_agree hp

/-- **A well-sorted term has a result under a substitution well sorted on its variables**, where
every function terminates: the variables outside `is` are given the sort `Bool` and a value of it
(`Semantics.extendHeld`), at which the term has the same sort and the same result. -/
theorem evalTerm_total_atCl (hsc : SortCtx c) (hov : OvlOK c) (hft : FnTerminates c) {L : List CtorSig}
    (hL : HeadsOK c L) {vars : List Srt} {is : List Nat} {σ : Subst} (hσ : c.WellSortedAt vars is σ)
    {t : Term} {s : Srt} (hvt : ∀ i ∈ varOccs t, i ∈ is) (ht : sortOfTerm (c.rhsCtx L) vars t = some s) :
    ∃ r, EvalTerm c σ t r := by
  let vars' : List Srt := (List.range vars.length).map fun i => if i ∈ is then vars.getD i 0 else Srt.bool
  have hv' : ∀ i, vars'[i]? =
      if i < vars.length then some (if i ∈ is then vars.getD i 0 else Srt.bool) else none := by
    intro i
    simp only [vars', List.getElem?_map]
    split
    · rename_i h; rw [List.getElem?_range h]; rfl
    · rename_i h; rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]; rfl
  have hagree : ∀ i ∈ is, vars'[i]? = vars[i]? := by
    intro i hi
    rw [hv']
    by_cases hlt : i < vars.length
    · simp [hlt, hi, List.getD_eq_getElem?_getD]
    · simp only [hlt, ite_false]
      exact (List.getElem?_eq_none (Nat.le_of_not_lt hlt)).symm
  have hheld : c.HeldAt vars' is := by
    intro i s' hs'
    by_cases hi : i ∈ is
    · exact Or.inl hi
    · right
      rw [hv'] at hs'
      split at hs'
      · simp only [Option.some.injEq] at hs'
        subst hs'
        exact ⟨bool true, sortOf_bool true⟩
      · cases hs'
  have hσ' : c.WellSortedAt vars' is σ := fun i hi s' hs' => hσ i hi s' (by rw [← hagree i hi]; exact hs')
  obtain ⟨σ', hσw, hσa⟩ := Semantics.extendHeld hheld hσ'
  have ht' : sortOfTerm (c.rhsCtx L) vars' t = some s := by
    rw [sortOfTerm_congr t fun i hi => hagree i (hvt i hi)]; exact ht
  obtain ⟨r, hr⟩ := Model.evalTerm_totalCl hsc hov hft hL hσw ht'
  exact ⟨r, Exec.EvalTerm.congr hr fun i hi => hσa i (hvt i hi)⟩

/-- Where every function terminates, each `requires` of a clause has a result at each match well
sorted on its patterns and conditions (`PrioDecided`), for a semantics `sortedOKCl` accepts. -/
theorem prioDecided_of_totalCl (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (ht : FnTerminates c) : PrioDecided c := by
  intro fn hfn vs cl σ _ _ cl' hcl' _ _ σ' hσ' _
  obtain ⟨L, hL, -, hpre, -, -, hreqs, -⟩ := clauseOpenFacts_of_sortedOKCl (hpreTop := hpreTop) hok fn (List.mem_append_left _ hfn) cl' hcl'
  refine ⟨fun t hq => ?_, true, Clause.holds_preTop hpre σ'⟩
  exact evalTerm_total_atCl (sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)) hov ht hL hσ'
    (Clause.req_leftVars hq) (hreqs t hq)

/-- Where every function terminates, each clause instance has a result under each well-sorted
substitution, for a semantics `sortedOKCl` accepts: its `ensures` has one, and where that is
`true`, its right-hand side. -/
theorem instRes_of_totalCl (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (ht : FnTerminates c) {fn : Fn} (hfn : fn ∈ c.fns) {cl' : Clause} (hcl' : cl' ∈ fn.clauses)
    {σ' : Subst} (hσ' : c.WellSorted cl'.vars σ') : ∃ r, cl'.InstRes c σ' r := by
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)
  obtain ⟨L, hL, -, -, -, -, -, hrhs, hens, -⟩ := clauseOpenFacts_of_sortedOKCl (hpreTop := hpreTop) hok fn (List.mem_append_left _ hfn) cl' hcl'
  obtain ⟨r, hr⟩ := Model.evalTerm_totalCl hsc hov ht hL hσ' hrhs
  cases he : cl'.ens with
  | none => exact ⟨r, .inl ⟨fun t ht => (by rw [he] at ht; cases ht), hr⟩⟩
  | some t =>
    obtain ⟨w, hw⟩ := Model.evalTerm_totalCl hsc hov ht hL hσ' (hens t he)
    by_cases hb : w = some (bool true)
    · subst hb
      exact ⟨r, .inl ⟨fun t' ht' => (by rw [he] at ht'; cases ht'; exact hw), hr⟩⟩
    · exact ⟨none, .inr ⟨t, w, he, hw, hb, rfl⟩⟩

/-- Where every function terminates, each clause instance that decides has a result (`CoDefined`),
for a semantics `sortedOKCl` accepts (`instRes_of_totalCl`). -/
theorem coDefined_of_totalCl (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (ht : FnTerminates c) : CoDefined c :=
  fun fn hfn _ _ _ cl' _ _ hcl' _ hdec' _ => instRes_of_totalCl (hpreTop := hpreTop) hok hsr hov ht hfn hcl'
    ((wellSortedAt_univ
      (Semantics.clausePlainOpen_partsP ((Semantics.sortedOKCl_parts hok).2.1 fn hfn cl' hcl').2).1).mp hdec'.1.1)

/-- **Evaluation solves the equations** where every function has at most one result and a result
at arguments of its sorts, for a semantics `sortedOKCl` accepts, and each clause with existential
variables has a result (`Clause.Res`) at each match under which it decides (`hex`;
`MatchIndependent` holds it). A clause without existential variables has one by the termination,
its right side's predicate being `\top`. -/
theorem fnSolves_of_totalCl (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (hd : FnDet c) (ht : FnTerminates c)
    (hex : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ∀ vs σ, cl.Decides c fn σ vs → ∃ r, cl.Res c σ r) :
    FnSolves c :=
  fnSolves_of_res (fun _ hfn => by
      rw [Semantics.lookupFn_eq]
      exact find?_label (sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)).nodupFns (List.mem_append_left _ hfn))
    hd (prioDecided_of_totalCl (hpreTop := hpreTop) hok hsr hov ht) fun fn hfn cl hcl vs _ σ hdec => by
      by_cases hx : cl.exs = []
      · obtain ⟨r, hr⟩ := instRes_of_totalCl (hpreTop := hpreTop) hok hsr hov ht hfn hcl ((wellSortedAt_univ hx).mp hdec.1.1)
        exact ⟨r, Clause.res_of_instRes hx
          (Semantics.clausePlainOpen_partsP ((Semantics.sortedOKCl_parts hok).2.1 fn hfn cl hcl).2).2.1 hr⟩
      · exact hex fn hfn cl hcl hx vs σ hdec

/-- **One result, and evaluation solves the equations**, for a semantics whose clauses are asked
CN-4's bodies, from the termination of its functions, the agreement of their equations and the
match independence of their clauses. -/
theorem fnModel_ofCl (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (ht : FnTerminates c) (hag : ∀ fn ∈ c.fns, ClausesAgree c fn)
    (hmi : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) : FnDet c ∧ FnSolves c :=
  have hd := fnDet_of_coherent (coherentAll_ofCl hag hmi)
  ⟨hd, fnSolves_of_totalCl (hpreTop := hpreTop) hok hsr hov hd ht fun fn hfn cl hcl hne vs σ hdec =>
    (hmi fn hfn cl hcl).2 hne fn.label fn vs σ (by
      rw [Semantics.lookupFn_eq]
      exact find?_label (sortCtx_of_allCl hok hsr (OvlOK.ovlCase hov)).nodupFns (List.mem_append_left _ hfn))
      hcl hdec⟩

end Faithful

open Faithful

/-- **`FnHyp` gives `FnDet` and `FnSolves`** for a semantics whose clauses are asked CN-4's bodies
(`sortedOKCl`, with `srReady` and `OvlOK`): `fnModel_of_fnHyp`'s conclusion with no hypothesis on
the sorts of the variables the patterns and conditions do not hold. `FnHyp`'s totality conjunct and
its two last are not read. -/
theorem fnModel_of_fnHypCl {c : Semantics} (hpreTop : c.clausesPreTop = true) (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : OvlOK c)
    (hf : FnHyp c) : FnDet c ∧ FnSolves c :=
  fnModel_ofCl (hpreTop := hpreTop) hok hsr hov hf.1 hf.2.2.1 hf.2.2.2.1

end KCore
