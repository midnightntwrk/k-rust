/-
  KCore. Step completeness at one configuration (`complete_at`), for a semantics whose clauses are
  asked CN-4's bodies (`Semantics.sortedOKCl`), with no hypothesis on the sorts of the variables the
  patterns and conditions do not hold.

  `step_successor_at`'s proof, with what it reads of the clauses replaced by what the evaluation
  lemmas read (`evalTerm_den4Cl` with each negated clause's exclusion empty, `neg_of_coreCl`), and
  of the rules by `rule_ctxCl`, `rule_ctx_ensCl` and the hypothesis that their predicates are
  `\top` (the rules are asked the same of `sortedOK` and `sortedOKCl`): the rule-level lemmas it calls are restated over
  `sortedOKCl` (`freeOf_rule_partsCl`, `Model.freeOf_prio_of_sortedCl`, `rule_partsCl`,
  `rhs_sorted_coreCl`, `step_of_apply_coreCl`), and the function-level ones over `ExclEmptyCl`
  (`lhs_req_hold4Cl`, `applies_holdsCl`).
-/
import KcoreSpec.FaithfulFamilies
import KcoreSpec.OpenClauseFn

set_option autoImplicit false

namespace KCore

/-- `step_of_apply_core` from `sortedOKCl`. -/
theorem step_of_apply_coreCl {c : Semantics} (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    {r : Rule} (hr : r ∈ c.rules) {x : Config c} {σ : Subst} (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :
    Step c x ⟨v, rhs_sorted_coreCl hok hsr hov hr hσ he⟩ :=
  .rule r hr σ hσ hm hreq hpre he hens hpost hprio

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics}

/-- `freeOf_rule_parts` from `sortedOKCl`. -/
theorem freeOf_rule_partsCl (hok : c.sortedOKCl = true) {r : Rule} (hr : r ∈ c.rules) {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.lhs) ∨
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))) ∨
      k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.rhs) ∨
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))) :
    ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctxCl hok hr
  have hens := rule_ctx_ensCl hok hr
  rcases hk with hk | hk | hk | hk
  · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.lhs hk
    exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
  · cases hq : r.req with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, varOccs_lt t (hreqs t hq) i hi, rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk
  · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.rhs hk
    exact ⟨i, varOccs_lt r.rhs hrhss i hi, rfl⟩
  · cases hq : r.ens with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, varOccs_lt t (hens t hq) i hi, rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk


end

namespace Model

variable {c : Semantics}

/-- `freeOf_prio_of_sorted` from `sortedOKCl`. -/
theorem freeOf_prio_of_sortedCl (hok : c.sortedOKCl = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) {r : Rule} (hr : r ∈ c.rules) {k : KoreAML.VarKey}
    (hk : k ∈ KoreAML.freeOf [] (prioRuleK c r)) : ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨-, hreqs, -⟩ := rule_ctxCl hok hr
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOKCl_exsNil hok hr (hb r hr)
  rw [prioRuleK_top hex₀ hpre₀ hpost₀] at hk
  dsimp only at hk
  split at hk
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append, List.not_mem_nil,
      or_false] at hk
    rcases hk with (hk | hk | hk) | hk
    · exact freeOf_rule_partsCl hok hr (Or.inl hk)
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inl hk))
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inr hk))
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inr hk))
  · rw [KoreAML.freeOf] at hk
    simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append, List.not_mem_nil,
      or_false] at hk
    rcases hk with (hk | hk | hk | hk) | hk
    · exact freeOf_rule_partsCl hok hr (Or.inl hk)
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inl hk))
    · exfalso
      obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      have hr'm := (List.mem_filter.mp hr').1
      obtain ⟨hlhs', hreqs', -⟩ := rule_ctxCl hok hr'm
      exact freeOf_applies hlhs' (fun t ht i hi => varOccs_lt t (hreqs' t ht) i hi)
        (htop _ hr'm).1 (hb _ hr'm) hk
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inr hk))
    · exact freeOf_rule_partsCl hok hr (Or.inr (Or.inr hk))


end Model

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hsc : SortCtx c)
  (hok : c.sortedOKCl = true) (hph : patHooksApart c = true)
  (hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl)
include hI hnn hsc hok hph hneg

/-- `lhs_req_hold4` for a semantics `sortedOKCl` accepts, each negated clause's exclusion empty
where it fails (`ExclEmptyCl`). -/
theorem lhs_req_hold4Cl {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c r.vars) σ e) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e
        (elemOf c I x.val) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctxCl hok hr
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hxs := elemOf_spec hI x.property e
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC (elemOf c I x.val) := by
    have := hxs.2
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp this
  refine ⟨(patVal_den4 hI hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch hlhs).2 _ |>.mpr
    ((hxs.1 _).mpr rfl), ?_⟩
  cases hq : r.req with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
    exact haC
  | some t =>
    simp only [Option.map_some, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
    refine ⟨haC, fun b _ => ?_⟩
    rw [evalTerm_den4ClPre hI hnn hsc hph (clauseOpenFactsP_of_sortedOKCl hok) hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) (hreq t hq) fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t hq) b,
      KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

/-- `applies_holds` for a semantics `sortedOKCl` accepts, each negated clause's exclusion empty
where it fails (`ExclEmptyCl`). -/
theorem applies_holdsCl {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) (hb : binds r.vars.length (varOccs r.lhs) = true) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) (e : Valuation M) :
    (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := by
  have hD := defOK hI
  let vs := canonVars c r.vars
  obtain ⟨hnd, hsrt⟩ := canon_binders hkeys
  have hag := overV_agrees hI hkeys hσ (e := e)
  have h := lhs_req_hold4Cl hI hnn hsc hok hph hneg hr hσ hmatch hreq hag
  rw [applies_top _ hpre hb]
  show (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll (srtOf c topCellSort) (vs.map KoreAML.Var.kore)
      (.and (srtOf c topCellSort) [Term.kore c vs r.lhs, reqPat (srtOf c topCellSort) (r.req.map (Term.kore c vs))]))).interpret
        I e _
  refine existsAll_intro_at hD _ e (overV c I tbl r.vars σ e) _ hnd hsrt (fun z hz => ?_) rfl (fun b hb n hn => ?_) ?_
  · refine overV_off fun i hi he => hz _ ?_ he
    have hlt : i < vs.length := by rw [canonVars_length]; exact hi
    show ((canonVars c r.vars).getD i default).kore ∈ vs.map KoreAML.Var.kore
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact List.mem_map_of_mem (List.getElem_mem hlt)
  · obtain ⟨i, hi, rfl⟩ := canonVars_kore_mem hb
    have hs : ((canonVars c r.vars).getD i default).kore.sort = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
      rw [canonVars_getD c hi]; rfl
    rw [hs] at hn
    rw [← srt_inj hn]
    show InS I _ ((overV c I tbl r.vars σ e).evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [overV_at hkeys hi]
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    rw [hw]
    exact (inS_iff e).mp (elemOf_spec hI hsw e).2
  · rw [tr_and2, KoreAML.interp_sAnd]
    exact h


end

section
variable {c : Semantics}

/-- `rule_parts` from `sortedOKCl`. -/
theorem rule_partsCl {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hok : c.sortedOKCl = true)
    (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    {r : Rule} (hr : r ∈ c.rules) :
    ∃ L, prioRuleK c r = .rewrites (srtOf c topCellSort) L
        (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
          reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.freeOf [] L) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ i < r'.vars.length, canonKey c r'.vars i ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.tr ⟨tbl, []⟩ L).interpret I e a →
        (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e a ∧
        (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret
          I e a ∧
        ∀ r' ∈ c.rules, r'.prio < r.prio →
          ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r' (canonRulePres r'))).interpret I e a := by
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOKCl_exsNil hok hr (hb r hr)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  have hfree : ∀ (ps : List Kore.Pattern), ∀ i < r.vars.length,
      canonKey c r.vars i ∈ KoreAML.freeOf [] (.and C (Term.kore c vs r.lhs :: ps)) :=
    fun ps i hi => Model.freeOf_and_lhs (Model.kore_freeOf c vs r.lhs (hbinds i hi))
  have hvars : ∀ (ps : List Kore.Pattern), ∀ i < r.vars.length,
      canonKey c r.vars i ∈ KoreAML.varsOf (.and C (Term.kore c vs r.lhs :: ps)) :=
    fun ps i hi => Model.varsOf_and_mem (List.mem_cons_self ..) (varsOf_kore c vs r.lhs (hbinds i hi))
  by_cases hce : comps.isEmpty
  · have hnone : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio := fun r' hr' hlt => by
      have := hcomp r' hr' hlt
      rw [List.isEmpty_iff.mp hce] at this
      exact absurd this List.not_mem_nil
    refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce], hfree _, hvars _,
      fun r' hr' hlt => absurd hlt (hnone r' hr'), fun tbl e a h => ?_⟩
    rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
    exact ⟨h.1, h.2.1, fun r' hr' hlt => absurd hlt (hnone r' hr')⟩
  · refine ⟨.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)), .not C (anyOfC C comps),
        .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])],
      by rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce], hfree _, hvars _, fun r' hr' hlt i hi => ?_,
      fun tbl e a h => ?_⟩
    · refine Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
      simp only [KoreAML.varsOf]
      exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr' hlt)
        (varsOf_applies (htop _ hr').1 (hb _ hr') hi))
    · rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd] at h
      obtain ⟨h1, h2, h3, -⟩ := h
      rw [KoreAML.tr, KoreAML.interp_sNot] at h3
      exact ⟨h1, h2, fun r' hr' hlt happ => h3.1 (anyOfC_of_mem h3.2 (hcomp r' hr' hlt) happ)⟩

end

section
variable {c : Semantics}

open Classical in
/-- **A successor of a configuration is a step's**, for a semantics whose clauses are asked CN-4's
bodies: with the step's closure axiom, in every model of `Γc c`, a successor of
the element of `x` that lies in a pattern ψ is the element of a configuration y with `Step c x y`,
where the evaluations the step at `x` reads have results (`StepDecided`). `step_successor_at` with
`sortedOKCl` and the conjuncts of `HypSoundCore` other than `sortedOK`, from `faithCoreOK`. -/
theorem step_successor_atCl (hok : c.sortedOKCl = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hsr : c.srReady = true) [hno : OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : patHooksApart c = true)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    (x : Config c) (hd : StepDecided c x.val)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ y : Config c, Step c x y ∧ ψ.interpret I e (elemOf c I y.val) := by
  obtain ⟨hnn, hg, hcso, hcs, hph', -, -⟩ := faithCoreOK_parts hfa
  have hnn := namesNumbered_spec hnn
  have hsc := sortCtx_of_allCl hok hsr (OvlOK.ovlCase hno)
  have hIc : I ⊧ᴵP Γc c := fun φ hφ => hI φ (Or.inl hφ)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hD := defOK hIΓ
  -- every negated clause's exclusion is empty where it fails, as for soundness
  have hneg := neg_of_coreCl hIc hok hsr hfa hph hc (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok))
  have hnext := hs
  unfold KoreAML.sNext at hnext
  rw [KoreAML.interp_app] at hnext
  obtain ⟨n0, b, hn0, hnb, happ⟩ := hnext
  -- the closure axiom, at `y := b`
  have hcl := hI _ (Or.inr rfl) e (elemOf c I x.val)
  rw [Model.stepClosure_pat] at hcl
  dsimp only at hcl
  generalize hy : (⟨Model.tablesLen (c.rules.map (prioRuleK c)) 0 + 1⟩ : EVar) = y at hcl
  let e1 : Valuation M := ⟨Function.update e.evalEvar y b, e.evalSvar⟩
  have hψ : (KoreAML.sNext (.evar y) ⊆⊆
      KoreAML.disjList ((c.rules.map (prioRuleK c)).foldl (Model.stepF y) ([], [], 0)).2.1).interpret I e1
        (elemOf c I x.val) := by
    unfold Pattern.universal at hcl
    rw [interpret_neg, interpret_exists] at hcl
    exact Classical.byContradiction fun hc => hcl ⟨b, by rw [interpret_neg]; exact hc⟩
  rw [KoreAML.interp_included hD] at hψ
  have hdisj := hψ (elemOf c I x.val) (by
    unfold KoreAML.sNext
    rw [KoreAML.interp_app]
    exact ⟨n0, b, hn0, by show b = Function.update e.evalEvar y b y; simp, happ⟩)
  obtain ⟨φ, hφ, hφm⟩ := disjList_mem hdisj
  rcases stepF_cases y _ _ φ hφ with hφ | ⟨p, hp, off, hoff, rfl⟩
  · exact absurd hφ List.not_mem_nil
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctxCl hok hr
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨L, hPL, hLfree, hLvars, hLcomp, hLread⟩ := rule_partsCl (I := I) hok hb htop hr
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_of_sortedCl hok hb htop hr (by rw [hPL]; exact hk)
  rw [hPL] at hφm hoff
  rw [closureDisjunct_rewrites] at hφm
  -- the table of the disjunct
  let tbl : VarTable := List.replicate off (.sortVar "#pad") ++ KoreAML.tableOf [] (.rewrites C L R)
  have hin_tbl : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk =>
    List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_append_right _ (by
      simp only [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ hk))))
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hin_tbl _ (hLvars i hi)
  have hy_ne : ∀ k ∈ tbl, y ≠ tbl.ev k := by
    intro k hk he
    have h1 := Model.index_le hk
    have hoff' : off + (KoreAML.tableOf [] (.rewrites C L R)).length ≤ Model.tablesLen (c.rules.map (prioRuleK c)) 0 :=
      hoff
    rw [← he, ← hy] at h1
    have h2 : tbl.length = off + (KoreAML.tableOf [] (.rewrites C L R)).length := by simp [tbl]
    simp only at h1
    omega
  -- the binders of the disjunct are the rule's variables
  let free := Model.evarsOf (KoreAML.freeOf [] (.rewrites C L R)).eraseDups
  have hfree : ∀ ks ∈ free, ∃ i < r.vars.length, ks.1 = canonKey c r.vars i ∧
      ks.2 = KoreAML.srt (c.sortName (r.vars.getD i 0)) := by
    intro ks hks
    obtain ⟨hk1, n, hn⟩ := Model.mem_filterMap_evar hks
    obtain ⟨i, hi, he⟩ := hfreeP _ (List.mem_eraseDups.mp hk1)
    refine ⟨i, hi, he, ?_⟩
    rw [he, canonKey_eq c hi] at hn
    injection hn with _ h2
    exact h2.symm
  obtain ⟨e2, he2, hguard, hbody⟩ := sExists_foldr_elim hD free e1 _
    (fun ks hks ks' hks' heq => by
      obtain ⟨i, hi, h1, h2⟩ := hfree ks hks
      obtain ⟨j, hj, h1', h2'⟩ := hfree ks' hks'
      have hij := canonKey_inj hi hj (by rw [← h1, ← h1']; exact ev_inj (h1 ▸ hkeys i hi) (h1' ▸ hkeys j hj) heq)
      subst hij
      rw [h2, h2'])
    (fun ks hks => by obtain ⟨i, -, -, h2⟩ := hfree ks hks; exact ⟨_, h2⟩) hφm
  have he2y : e2.evalEvar y = b := by
    rw [he2 y (fun ks hks => by
      obtain ⟨i, hi, h1, -⟩ := hfree ks hks
      rw [h1]; exact hy_ne _ (hkeys i hi))]
    show Function.update e.evalEvar y b y = b
    simp
  rw [interpret_conj] at hbody
  obtain ⟨hL, hRm⟩ := hbody
  rw [KoreAML.interp_member hD, he2y] at hRm
  change (KoreAML.tr ⟨tbl, []⟩ (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])).interpret
    I e2 b at hRm
  rw [tr_and2, KoreAML.interp_sAnd] at hRm
  obtain ⟨hl, hreq, hcomp⟩ := hLread tbl e2 _ hL
  -- the valuation of the rule's variables is a well-sorted substitution of values
  have hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0)) (e2.evalEvar (tbl.ev (keyAt vs i))) := by
    intro i hi
    have hk : canonKey c r.vars i ∈ KoreAML.freeOf [] (.rewrites C L R) := by
      rw [KoreAML.freeOf]; exact List.mem_append_left _ (hLfree i hi)
    have hks := Model.evar_mem_filterMap (List.mem_eraseDups.mpr (by rw [canonKey_eq c hi] at hk; exact hk))
    have := hguard _ hks _ rfl
    show InS I _ (e2.evalEvar (tbl.ev (canonKey c r.vars i)))
    rw [canonKey_eq c hi]
    exact this
  obtain ⟨hmatch, hwit⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) hlhs x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  -- no rule of a smaller priority applies, in the sense of `RuleApplies`: the disjunct's negated
  -- competitors hold at the element of x
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt ⟨σ', hσ', hpv', hreq', _⟩ => hcomp r' hr' hlt (applies_holdsCl hIΓ hnn hsc hok hph hneg hr' (htop _ hr').1 (hb _ hr')
      (Rule.wellSorted_of_at (hb _ hr') hσ')
      hpv' hreq' (fun i hi => hin_tbl _ (hLcomp r' hr' hlt i hi)) e2)
  -- so the rule is one `StepDecided` speaks of, at this match
  have hdr := hd r hr hnoapp
  have hdr1 := hdr.1 _ (hσ.at _) hmatch
  -- the `requires` evaluates to `true`
  have hreqT : ∀ t, r.req = some t → EvalTerm c (substOf c I tbl vs r.vars e2) t (some (bool true)) := by
    intro t ht
    obtain ⟨v, hv⟩ := hdr1.1 t ht
    by_cases hvt : v = some (bool true)
    · rw [hvt] at hv; exact hv
    · exfalso
      rw [ht] at hreq
      obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
        hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hreqs t ht) hu)
        (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl hok) hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t ht))
        _ hreq
  have hrest := hdr.2 _ hσ hmatch hreqT ((htop _ hr).1 ▸ .top)
  -- the `ensures` evaluates to `true`
  have hensS := rule_ctx_ensCl hok hr
  have hensT : ∀ t, r.ens = some t → EvalTerm c (substOf c I tbl vs r.vars e2) t (some (bool true)) := by
    intro t ht
    obtain ⟨v, hv⟩ := hrest.2.1 t ht
    by_cases hvt : v = some (bool true)
    · rw [hvt] at hv; exact hv
    · exfalso
      have hE := hRm.2
      rw [ht] at hE
      obtain ⟨σC, hσC1, hσC2⟩ := sortSing hIΓ (top_numbered (c := c))
      exact reqFalse_empty hIΓ (S' := srtOf c topCellSort) (fun a => by unfold srtOf; rw [trSort_srt]; exact hσC1 a) hσC2
        hvt (fun u hu => EvalTerm.sorted hsc hv fns_headsOK hσ (hensS t ht) hu)
        (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl hok) hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) hv fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht))
        _ hE
  -- no rule of a smaller priority applies: each is one `StepDecided` speaks of (the rules of a
  -- smaller priority still do not apply), so its `requires` has a result, which is not `true`
  have hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val := by
    intro r' hr' hlt σ' hσ' hpv'
    have hun : ∀ r'' ∈ c.rules, r''.prio < r'.prio → ¬ RuleApplies c r'' x.val :=
      fun r'' hr'' hlt' => hnoapp r'' hr'' (Nat.lt_trans hlt' hlt)
    have hd' := ((hd r' hr' hun).1 σ' hσ' hpv').1
    have hpre' : Holds c r'.vars.length σ' r'.pre true := (htop _ hr').1 ▸ .top
    cases ht : r'.req with
    | none =>
      exact absurd ⟨σ', hσ', hpv', (fun t h => by rw [ht] at h; cases h), hpre'⟩ (hnoapp r' hr' hlt)
    | some t =>
      obtain ⟨v, hv⟩ := hd' t ht
      by_cases hvt : v = some (bool true)
      · refine absurd ⟨σ', hσ', hpv', fun t' h => ?_, hpre'⟩ (hnoapp r' hr' hlt)
        rw [ht] at h; cases h; rw [hvt] at hv; exact hv
      · exact RuleReqFails.intro ht hv hvt
  -- the right-hand side evaluates to a configuration whose element is `b`
  obtain ⟨v, hv⟩ := hrest.1
  have hbR := (evalTerm_den4ClPre hIΓ hnn hsc hph (clauseOpenFactsP_of_sortedOKCl hok) hneg (preRead_of_allTop (clauseOpenFacts_of_sortedOKCl hok)) hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp
    hRm.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hstep := step_of_apply_coreCl hok hsr (OvlOK.ovlCase inferInstance) hr hσ hmatch hreqT ((htop _ hr).1 ▸ .top) hv hensT
      ((htop _ hr).2 ▸ .top) hprio
    refine ⟨_, hstep, ?_⟩
    have hbe := ((elemOf_spec hIΓ (rhs_sorted_coreCl hok hsr (OvlOK.ovlCase inferInstance) hr hσ hv) e).1 b).mp (((den_closed c yv).interp e2 e b).mp hbR)
    rw [← hbe]
    exact hnb

end

end Faithful

open Faithful

/-- **Completeness at a configuration**, for a semantics whose clauses are asked CN-4's bodies:
`complete_at`'s conclusion with `sortedOKCl` and the conjuncts of `coreOK` the proof reads in place
of `coreOK` (`step_successor_atCl`). No hypothesis on the sorts of the variables the patterns and conditions do not hold. -/
theorem complete_atCl (c : Semantics) (hok : c.sortedOKCl = true) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top) (hsr : c.srReady = true) [OvlOK c]
    (hfa : c.faithCoreOK = true) (hph : Faithful.patHooksApart c = true)
    (x : Config c) (hd : StepDecided c x.val) (os : List Outcome)
    (hval : ∀ (y : Config c) (r : Rule) (σ : Subst), r.opens = [] → StepBy c r σ x y → .val y.val ∈ os)
    (_hfam : ∀ r ∈ c.rules, r.opens ≠ [] → ∀ σ, Unblocked c r σ x.val →
      ∃ σ', (∀ i ∈ varOccs r.lhs, σ'.lookup i = σ.lookup i) ∧ .fam r σ' ∈ os)
    (hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (os.map (Outcome.pat c)))) := by
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  rw [ML.interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [ML.interpret_neg]
  intro hnext
  obtain ⟨y, hy, hψ⟩ := step_successor_atCl hok hb htop hsr hfa hph hc x hd hI e _ hnext
  rw [ML.interpret_neg] at hψ
  obtain ⟨r, σ, hs⟩ := step_iff_by.mp hy
  have hop : r.opens = [] := Rule.opens_of_binds (hb _ hs.mem)
  exact hψ (disjList_of_mem (List.mem_map_of_mem (hval y r σ hop hs))
    (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))

end KCore
