/-
  KCore. Step completeness at one configuration: for a list `ys` holding every successor `Step`
  gives of the configuration `x`, with the step's closure every successor of `x` is one of `ys`,
  `⟦x⟧ → ◦ ⋁_{y ∈ ys} ⟦y⟧` (`step_complete_at`), where the evaluations the step at `x` reads have
  results (`StepDecided c x`, Step.lean). No hypothesis on the functions of the definition is read:
  what the proof reads of the semantics is `HypSoundCore`, what soundness reads.

  The proof is `step_complete`'s (FaithfulComplete.lean), which reads the totality of evaluation
  (`Model.evalTerm_total`) at the chosen rule's `requires`, right-hand side and `ensures`, and at
  the `requires` of each rule of a smaller priority; `StepDecided` gives each of these results,
  once the rules of a smaller priority are known not to apply (`RuleApplies`), which the
  disjunct's negated competitors give. Its one use of `StepIs` is the membership of the successor
  it builds, which `hys` gives.
-/
import KcoreSpec.FaithfulComplete

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics}

open Classical in
/-- **A successor of a configuration is a step's**: with the step's closure axiom, in every model
of `Γ c`, a successor of the element of `x` that lies in a pattern ψ is the element of a
configuration y with `Step c x y`, where the evaluations the step at `x` reads have results
(`StepDecided`). -/
theorem step_successor_at (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (x : Config c) (hd : StepDecided c x.val)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γ c ∪ Γstep c))
    (e : Valuation M) (ψ : KoreAML.P)
    (hs : (KoreAML.sNext ψ).interpret I e (elemOf c I x.val)) :
    ∃ y : Config c, Step c x y ∧ ψ.interpret I e (elemOf c I y.val) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  have hD := defOK hIΓ
  -- every clause's exclusion is empty where it fails, as for soundness
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hIΓ hph hcs hcso hg hsc.trans hnn.1 (clause_preTop hok hfn hcl)
        (Semantics.pats_nf (OvlOK.hyp inferInstance hsc.trans) hfn hcl hp') hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  have hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmpty c I fn cl :=
    fun fn hfn cl hcl _ => hex fn hfn cl hcl
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
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctx hok hr
  have hbinds := Exec.binds_all (hb _ hr)
  obtain ⟨L, hPL, hLfree, hLvars, hLcomp, hLread⟩ := rule_parts (I := I) hok hb htop hr
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let R : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] (.rewrites C L R), ∃ i < r.vars.length, k = canonKey c r.vars i :=
    fun k hk => Model.freeOf_prio_of_sorted hok hb htop hr (by rw [hPL]; exact hk)
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
    (collPat_of_sorted hph' hlhs) (Semantics.lhs_nf OvlOK.ok hr hlhs) x.property hl
  obtain ⟨hσ, hag⟩ := substOf_ok hIΓ hg hsc.trans (canonVars_length c r.vars) (fun i hi => hwit i (hbinds i hi))
  -- no rule of a smaller priority applies, in the sense of `RuleApplies`: the disjunct's negated
  -- competitors hold at the element of x
  have hnoapp : ∀ r' ∈ c.rules, r'.prio < r.prio → ¬ RuleApplies c r' x.val :=
    fun r' hr' hlt ⟨σ', hσ', hpv', hreq', _⟩ => hcomp r' hr' hlt (applies_holds hIΓ hnn hsc hok hbc hph hneg hr' (htop _ hr').1 (hb _ hr')
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
        (evalTerm_den4 hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t ht))
        _ hreq
  have hrest := hdr.2 _ hσ hmatch hreqT ((htop _ hr).1 ▸ .top)
  -- the `ensures` evaluates to `true`
  have hensS := rule_ctx_ens hok hr
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
        (evalTerm_den4 hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht))
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
  have hbR := (evalTerm_den4 hIΓ hnn hsc hok hbc hph hneg hv fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b).mp
    hRm.1
  cases v with
  | none => exact hbR.elim
  | some yv =>
    have hstep := step_of_apply_core hok hsr (OvlOK.ovlCase inferInstance) hr hσ hmatch hreqT ((htop _ hr).1 ▸ .top) hv hensT
      ((htop _ hr).2 ▸ .top) hprio
    refine ⟨_, hstep, ?_⟩
    have hbe := ((elemOf_spec hIΓ (rhs_sorted_core hok hsr (OvlOK.ovlCase inferInstance) hr hσ hv) e).1 b).mp (((den_closed c yv).interp e2 e b).mp hbR)
    rw [← hbe]
    exact hnb

/-- **Step completeness at a configuration**: with the step's closure axiom, in every model of
`Γ c`, every successor of the element of `x` is the element of a value in `ys`, a list holding
every successor `Step` gives of `x`, where the evaluations the step at `x` reads have results
(`StepDecided`): `step_successor_at` at the complement of the values of `ys`. -/
theorem step_complete_at (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (x : Config c) (hd : StepDecided c x.val) (ys : List GroundTerm)
    (hys : ∀ y : Config c, Step c x y → y.val ∈ ys) :
    (Γ c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList (ys.map (den c)))) := by
  intro M _ I hI e m
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  rw [interpret_impl]
  intro hmx
  have hmx' : m = elemOf c I x.val := ((elemOf_spec hIΓ x.property e).1 m).mp hmx
  subst hmx'
  unfold KoreAML.allNext
  rw [interpret_neg]
  intro hnext
  obtain ⟨y, hy, hψ⟩ := step_successor_at h hb htop hbc x hd hI e _ hnext
  rw [interpret_neg] at hψ
  exact hψ (disjList_of_mem (List.mem_map_of_mem (hys y hy)) (((elemOf_spec hIΓ y.property e).1 _).mpr rfl))

end

end Faithful

end KCore
