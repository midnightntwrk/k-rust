/-
  KCore. The value model satisfies the functions' equations where a clause may hold existential
  variables, with every fact of a clause's existential variables and of its right side's predicate
  given as a hypothesis on the clauses.

  - `ClausePostDecided`: each clause's right-side predicate has a truth value at each well-sorted
    instance. It is to the right side what `ClausePreDecided` is to the premise: the value model
    reads the predicate as `TrueV`, `Clause.Gives` reads `Holds … true`, and the two agree only
    where `Holds` has a truth value. It holds where every such predicate is `\top`
    (`clausePostDecided_of_top`) and where every function has a result
    (`clausePostDecided_of_total`).
  - `eqnFactsEx_of_sorted`: `EqnFactsEx` of a clause with `clauseSortedOpen` and `clauseExOK`.
  - `eqnFactsPre_of_sorted`, `eqnFactsPre_sortPred`: `EqnFactsPre` of a clause with
    `clauseSortedOpen`, no existential variable and the right side's predicate `\top`, and of a
    sort predicate's clause.
  - `AtT.satFnsGoalEx`: `ΓFns` in the value model. Per clause: without existential variables the
    equation `sat_clauseEqPre` / `sat_competingEqPre` read, with them the one `sat_clauseEqEx` /
    `sat_competingEqEx` read; in both the function's values are those `FnSolves` states
    (`eval_of_decides_ex`).

  What `AtT.satFnsGoalEx` reads of a clause is in `hcls`: `clauseSortedOpen`, `clauseExOK`, and the
  predicate `\top` where there is no existential variable. It does not read that an existential
  variable is of a confined sort or fixed by the predicate: in the value model every element of a
  sort is a value's.
-/
import KcoreSpec.ModelFnsEx

set_option autoImplicit false

namespace KCore

/-- **Every clause's right-side predicate has a truth value at each well-sorted instance.** -/
def ClausePostDecided (c : Semantics) : Prop :=
  ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, ∀ σ, c.WellSorted cl.vars σ → ∃ b, Holds c cl.vars.length σ cl.post b

/-- `ClausePostDecided` where every clause's right-side predicate is `\top`. -/
theorem clausePostDecided_of_top {c : Semantics}
    (h : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.post = .top) : ClausePostDecided c := by
  intro fn hfn cl hcl σ _
  exact ⟨true, by rw [h fn hfn cl hcl]; exact Holds.top⟩

/-- `ClausePostDecided` where the check that every clause's right-side predicate is `\top`
holds. -/
theorem clausePostDecided_of_isTop {c : Semantics}
    (h : (c.fns.all fun f => f.clauses.all fun cl => cl.post.isTop) = true) : ClausePostDecided c :=
  clausePostDecided_of_top fun fn hfn cl hcl =>
    Cond.eq_top_of_isTop (List.all_eq_true.mp (List.all_eq_true.mp h fn hfn) cl hcl)

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- **`ClausePostDecided` where every function has a result** at arguments of its sorts and each
clause's right-side predicate is well sorted over the clause's variables. -/
theorem clausePostDecided_of_total (hs : HypSoundCore c) (ht : FnTerminates c)
    (hok : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.condOK cl.vars cl.post = true) : ClausePostDecided c :=
  fun fn hfn cl hcl _ hσ => clausePost_decided_of_total hs ht (hok fn hfn cl hcl) hσ

/-- **`EqnFactsEx` of a clause with `clauseSortedOpen` and `clauseExOK`** over signatures of
functions of the semantics. An existential variable is in no pattern or condition of the left
side, so it occurs in the right-hand side, the `ensures` or the right side's predicate, each
sorted: its sort is numbered. -/
theorem eqnFactsEx_of_sorted (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    {L : List CtorSig} (hL : HeadsOK c L) (hs : c.clauseSortedOpen fn L cl = true)
    (hx : c.clauseExOK cl = true) : EqnFactsEx c fn cl := by
  obtain ⟨hpats, hocc, hreq, hrhs, hens⟩ := Semantics.clauseSortedOpen_parts hs
  have hpreOK := Semantics.clauseSortedOpen_preOK hs
  have hpatsN := Semantics.clauseSortedOpen_pats_nf hs
  simp only [Semantics.clauseSortedOpen, Bool.and_eq_true] at hs
  have hbd := hs.1.2
  simp only [Semantics.clauseExOK, Bool.and_eq_true] at hx
  obtain ⟨⟨⟨hltB, hndB⟩, hleftB⟩, hokQ⟩ := hx
  have hlt : ∀ i ∈ cl.exs, i < cl.vars.length := fun i hi => of_decide_eq_true (List.all_eq_true.mp hltB i hi)
  have hleft : ∀ i ∈ cl.exs, i ∉ cl.leftVars := fun i hi => by
    simpa [List.contains_iff_mem] using List.all_eq_true.mp hleftB i hi
  refine ⟨⟨hpatsN, ⟨L, hL, hreq⟩, hpreOK, hbd.1⟩, hlt, (NamesApart.nodupB_iff _).mp hndB, hleft, fun i hi => ?_,
    hokQ, hbd.2, fun i hi => Or.inr (hocc i hi), ⟨L, hL, hrhs, hens⟩⟩
  have hil := hlt i hi
  have hg : cl.vars[i]? = some (cl.vars.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]; rfl
  have hk : ∀ k ∈ (c.rhsCtx L).heads, k ∈ kernelSyms c := fun k hk => rhsHead_kernel hL hk
  have hsub : ∀ a b, (a, b) ∈ (c.rhsCtx L).subs → (a, b) ∈ c.subsorts := fun _ _ h' => h'
  have hO := hocc i hil
  simp only [List.mem_append] at hO
  rcases hO with (((hl | hR) | hE) | hQ)
  · exact absurd (List.mem_append.mpr hl) (hleft i hi)
  · exact varOccs_numOpen h hk hsub cl.rhs hrhs (h.fnSorts hfn fn.result (List.mem_cons_self ..)) i hR _ hg
  · cases ht : cl.ens with
    | none => rw [ht] at hE; cases hE
    | some t =>
      rw [ht] at hE
      exact varOccs_numOpen h hk hsub t (hens t ht) bool_numbered i hE _ hg
  · exact varOccsCond_numCN h cl.post hokQ i hQ _ hg

/-- **`EqnFactsPre` of a clause with `clauseSortedOpen`, no existential variable and the right
side's predicate `\top`** over signatures of functions of the semantics. -/
theorem eqnFactsPre_of_sorted {fn : Fn} {cl : Clause} {L : List CtorSig} (hL : HeadsOK c L)
    (hs : c.clauseSortedOpen fn L cl = true) (hex : cl.exs = []) (hpost : cl.post = .top) :
    EqnFactsPre c fn cl := by
  obtain ⟨hpats, hocc, hreq, hrhs, hens⟩ := Semantics.clauseSortedOpen_parts hs
  have hpreOK := Semantics.clauseSortedOpen_preOK hs
  have hpatsN := Semantics.clauseSortedOpen_pats_nf hs
  simp only [Semantics.clauseSortedOpen, Bool.and_eq_true] at hs
  refine ⟨⟨hpatsN, ⟨L, hL, hreq⟩, hpreOK, hs.1.2.1⟩, hex, fun i hi => ?_, ⟨L, hL, hrhs, hens⟩⟩
  have h1 := hocc i hi
  simp only [Clause.condVars, List.mem_append] at h1
  rcases h1 with ((((h1 | h1 | h1) | h1) | h1) | h1)
  · exact Or.inl h1
  · cases ht : cl.req with
    | none => rw [ht] at h1; cases h1
    | some t => rw [ht] at h1; exact Or.inr (Or.inl ⟨t, rfl, h1⟩)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · cases ht : cl.ens with
    | none => rw [ht] at h1; cases h1
    | some t => rw [ht] at h1; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl, h1⟩)))
  · rw [hpost] at h1; simp [varOccsCond] at h1

/-- **`EqnFactsPre` of a sort predicate's clause**, by its text. -/
theorem eqnFactsPre_sortPred (H : OvlLaws.OvlFnFacts c) {fn : Fn} (hp : fn ∈ c.sortPreds) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : EqnFactsPre c fn cl := by
  obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
  have hpre := Semantics.sortPreds_pre hp cl hcl
  refine ⟨⟨Semantics.sortPredPats_nf H hp hcl,
    ⟨[], fun k hk => absurd hk List.not_mem_nil, fun t ht => ?_⟩, by rw [hpre]; rfl, by rw [hpre]; rfl⟩,
    Semantics.sortPreds_exs hp cl hcl, fun i hi => ?_, ⟨[], fun k hk => absurd hk List.not_mem_nil, hrhs, fun t ht => ?_⟩⟩
  · rw [ht] at hreq
    simpa [reqOK] using hreq
  · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
    exact Or.inl (hb i hi)
  · rw [ht] at hens
    simpa [reqOK] using hens

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The value model satisfies the functions' equations where a clause may hold existential
variables.** Each clause of a function of the definition has `clauseSortedOpen` and `clauseExOK`,
and the right-side predicate `\top` where it has no existential variable (`hcls`); its premise's
predicate has a truth value wherever its patterns match (`ClausePreDecided`) and its right side's
at each well-sorted instance (`ClausePostDecided`). No fact of a clause's existential variables
or of its right side's predicate is read from `HypModelCore`. -/
theorem satFnsGoalEx (h : HypModelCore c)
    (hcls : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) : (stdI_T c T ⊧ᴵP ΓFns c) := by
  have hL : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  have hE : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclFactsPre c fn cl := fun fn hfn cl hcl => by
    rcases List.mem_append.mp hfn with hu | hs
    · exact (eqnFactsEx_of_sorted h hfn hL (hcls fn hu cl hcl).1 (hcls fn hu cl hcl).2.1).toExclFactsPre
    · exact (eqnFactsPre_sortPred h.ovlHyp.fnFacts hs hcl).toExclFactsPre
  have hdecL : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ σ ws, c.WellSortedAt cl.vars cl.leftVars σ →
      PatVals c σ cl.pats ws → (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) →
      ∃ b, Holds c cl.vars.length σ cl.pre b := fun fn hfn cl hcl σ ws hσ hpv _ => by
    rcases List.mem_append.mp hfn with hu | hs
    · exact hp fn hu cl hcl σ ws hσ hpv
    · exact ⟨true, Clause.holds_preTop (Semantics.sortPreds_pre hs cl hcl) σ⟩
  have hnil : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] → EqnFactsPre c fn cl ∧ cl.post = .top :=
    fun fn hfn cl hcl hex => by
      rcases List.mem_append.mp hfn with hu | hs
      · exact ⟨eqnFactsPre_of_sorted hL (hcls fn hu cl hcl).1 hex ((hcls fn hu cl hcl).2.2 hex),
          (hcls fn hu cl hcl).2.2 hex⟩
      · exact ⟨eqnFactsPre_sortPred h.ovlHyp.fnFacts hs hcl, Semantics.sortPreds_post hs cl hcl⟩
  have hcons : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] →
      EqnFactsEx c fn cl ∧ ∀ σ', c.WellSorted cl.vars σ' → ∃ b, Holds c cl.vars.length σ' cl.post b :=
    fun fn hfn cl hcl hne => by
      rcases List.mem_append.mp hfn with hu | hs
      · exact ⟨eqnFactsEx_of_sorted h hfn hL (hcls fn hu cl hcl).1 (hcls fn hu cl hcl).2.1, hq fn hu cl hcl⟩
      · exact absurd (Semantics.sortPreds_exs hs cl hcl) hne
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨fn, hfn, hit⟩ := List.mem_flatMap.mp hit
  obtain ⟨s, hs, hit⟩ := List.mem_filterMap.mp hit
  unfold fnEquationsK at hs
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  have hdl : ∀ cl' ∈ lowerClauses fn cl, cl' ∈ fn.clauses := fun cl' h' => (List.mem_filter.mp h').1
  by_cases hlow : (lowerClauses fn cl).isEmpty = true
  · rw [show prioEquation c fn cl = clauseEquation c fn cl from if_pos hlow] at hit
    have hdecides : ∀ {σ ws}, cl.AppliesAt c σ ws → cl.DecidesAt c fn σ ws := fun happ =>
      ⟨happ, fun cl' hcl' hna hlt => by
        have : cl' ∈ lowerClauses fn cl := by simp [lowerClauses, hcl', hna, hlt]
        rw [List.isEmpty_iff.mp hlow] at this
        exact absurd this List.not_mem_nil⟩
    by_cases hex : cl.exs = []
    · obtain ⟨F, hpost⟩ := hnil fn hfn cl hcl hex
      refine sat_kernelItem_of hit (clauseEquation_nilPre hex)
        (sat_clauseEqPre h hfn F (fun σ ws hσ hpv hr => hdecL fn hfn cl hcl σ ws (hσ.at _) hpv hr)
          fun σ ws hws happ v => ?_)
      exact (eval_of_decides_ex h hfn hcl hws (hdecides happ) v).trans
        (Clause.gives_iff_noExs hex hpost ((wellSortedAt_univ hex).mp happ.1) v)
    · obtain ⟨F, hpd⟩ := hcons fn hfn cl hcl hex
      exact sat_kernelItem_of hit (clauseEquation_axEx hex F.exLt)
        (sat_clauseEqEx h hfn F (hdecL fn hfn cl hcl) hpd fun σ ws hws happ =>
          eval_of_decides_ex h hfn hcl hws (hdecides happ))
  · rw [show prioEquation c fn cl = competingEquation c fn (lowerClauses fn cl) cl from if_neg hlow] at hit
    have hdecides : ∀ {σ ws}, cl.AppliesAt c σ ws →
        (∀ cl' ∈ lowerClauses fn cl, ∀ σ', c.WellSortedAt cl'.vars cl'.leftVars σ' → PatVals c σ' cl'.pats ws →
          ¬ ((∀ t, cl'.req = some t → EvalTerm c σ' t (some (bool true))) ∧
             Holds c cl'.vars.length σ' cl'.pre true)) → cl.DecidesAt c fn σ ws := fun happ hfails =>
      ⟨happ, fun cl' hcl' hna hlt σ' hw hp' =>
        hfails cl' (List.mem_filter.mpr ⟨hcl', by simp [hna, hlt]⟩) σ' hw hp'⟩
    have hF : ∀ cl' ∈ lowerClauses fn cl, ExclFactsPre c fn cl' := fun cl' hcl' => hE fn hfn cl' (hdl cl' hcl')
    by_cases hex : cl.exs = []
    · obtain ⟨F, hpost⟩ := hnil fn hfn cl hcl hex
      refine sat_kernelItem_of hit (competingEquation_nilPre hex)
        (sat_competingEqPre h hfn F (fun σ ws hσ hpv hr => hdecL fn hfn cl hcl σ ws (hσ.at _) hpv hr) hF
          fun σ ws hws happ hfails v => ?_)
      exact (eval_of_decides_ex h hfn hcl hws (hdecides happ hfails) v).trans
        (Clause.gives_iff_noExs hex hpost ((wellSortedAt_univ hex).mp happ.1) v)
    · obtain ⟨F, hpd⟩ := hcons fn hfn cl hcl hex
      exact sat_kernelItem_of hit (competingEquation_axEx hex F.exLt)
        (sat_competingEqEx h hfn F (hdecL fn hfn cl hcl) hpd hF fun σ ws hws happ hfails =>
          eval_of_decides_ex h hfn hcl hws (hdecides happ hfails))

end AtT

/-- **`SatFnsGoal` where a clause may hold existential variables**: `AtT.satFnsGoalEx` in the value
model. -/
theorem satFnsGoalEx (h : HypModelCore c)
    (hcls : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, c.clauseSortedOpen fn (c.fns.map Fn.sig) cl = true ∧
      c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top))
    (hp : ClausePreDecided c) (hq : ClausePostDecided c) : SatFnsGoal c :=
  AtT.satFnsGoalEx (c := c) (T := StepM c) h hcls hp hq

end Model

end Faithful

end KCore
