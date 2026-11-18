/-
  KCore, outside the cone: the guard of W2 for a rule (`TieRulePair.RuleGuard`) at an instance.

  `TieRulePair.rules_w2` states a rule's sentence in a model of Γ at each valuation where the
  conjuncts Γ's axiom (`prioRuleK`) adds to the text's left side hold of every element at which the
  left side and the `requires` hold. Those conjuncts are the `pre`'s patterns, the negation of the
  rules of a smaller priority, and the definedness of the right side with its `ensures`.

  - `ruleGuard_of_stepBy_held`: at the valuation that gives the rule's variables the elements of a
    step's match σ (`overV`), the guard holds: the left side there holds of x's element alone; at
    it the `pre` holds, no rule of a smaller priority applies (`StepBy.hprio`, through
    `not_applies_guarded_held`, for rules with `rulePlainHeldH H` in a model where the symbols of
    H that are no constructors have `HeldBack`) and the right side is defined (it evaluates, `StepBy.heval`, and the
    `ensures` is `true`: `ruleRight_at_pp`, `ceil_right_pp`).
  - `ruleGuard_of_stepBy`, `rules_w2_stepBy`: so, for a semantics meeting `coreOK` whose
    conditions read no confined sort, the guard holds there in every model of Γ, and the text's
    sentence of the rule with it.
  - `stepBy_of_checkStep`: a step the executable check accepts for one rule is a `StepBy` of that
    rule, at a match the executable matcher lists.
-/
import KcoreSpec.TieRulePair
import KcoreSpec.Sound

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK VarTable)
open HoldsShape (hasBinder Reads reads_of_agrees)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The guard of W2 at a step's match.** For rules with `ruleSorted` and `rulePlainHeldH H`, in a
model of `Γc` where each symbol of H that is no constructor has `HeldBack`, at the valuation `overV`
of a step's match σ, every conjunct Γ's axiom of the rule adds to the text's left side and `requires` holds of
every element at which those hold. -/
theorem ruleGuard_of_stepBy_held {H : Sym → Bool} (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (hIc : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hlarger : ∀ r' ∈ c.rules, r'.prio < r.prio → c.rules.any (fun r'' => r'.prio < r''.prio) = true)
    {σ : Subst} {x y : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    (hpre : Holds c r.vars.length σ r.pre true)
    (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c) :
    TieRulePair.RuleGuard (prioRuleK c r) I
      (overV c I (KoreAML.tableOf [] (prioRuleK c r)) r.vars σ (KoreAML.val0 : Valuation M)) := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hIΓ
  obtain ⟨hlhs, hocc, -, -, -, -, -, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  obtain ⟨-, hRv⟩ := Model.ruleRight_keysPP hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let left : List Kore.Pattern := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++
    Cond.conj c vs C r.pre
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  have hceilK : ∀ {k : KoreAML.VarKey}, k ∈ KoreAML.varsOf (ruleRight c r) →
      k ∈ KoreAML.varsOf (.ceil C C (ruleRight c r)) := fun hk => by
    rw [KoreAML.varsOf]; exact List.mem_append_right _ hk
  -- every variable of the rule, and every key of `pre`, is a variable of the left part
  have hkeysL : ∀ {ps : List Kore.Pattern}, (∀ q ∈ left, q ∈ ps) → .ceil C C (ruleRight c r) ∈ ps →
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (.and C ps)) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ KoreAML.varsOf (.and C ps)) := by
    intro ps hsub h3
    have h1 : Term.kore c vs r.lhs ∈ ps := hsub _ (by simp [left])
    have h2 : reqPat C (r.req.map (Term.kore c vs)) ∈ ps := hsub _ (by simp [left])
    have hP : ∀ φ ∈ Cond.conj c vs C r.pre, φ ∈ ps := fun φ hφ => hsub _ (List.mem_append_right _ hφ)
    refine ⟨fun i hi => ?_, fun k hk => Model.varsOf_condConj hP hk⟩
    rcases hocc i hi with hL | ⟨t, ht, hit⟩ | hPr | hR | ⟨t, ht, hit⟩ | hPo
    · exact Model.varsOf_and_mem h1 (varsOf_kore c vs r.lhs hL)
    · rw [ht] at h2
      refine Model.varsOf_and_mem h2 ?_
      simp only [Option.map_some, reqPat]
      rw [KoreAML.varsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (varsOf_kore c vs t hit))
    · exact Model.varsOf_condConj hP (Model.condKore_keys C r.pre (bound := []) hi hPr (by simp)).2
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inl hR))))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inr (Or.inl ⟨t, ht, hit⟩)))))
    · exact Model.varsOf_and_mem h3 (hceilK (hRv i hi (Or.inr (Or.inr (Or.inr hPo)))))
  -- the axiom: `\rewrites(left ++ ext, right)`, `ext` the negated competitors (where there are any)
  -- and the definedness of the right side
  obtain ⟨ext, hpat, hext, hceilm⟩ : ∃ ext : List Kore.Pattern,
      prioRuleK c r = .rewrites C (.and C (left ++ ext)) (ruleRight c r) ∧
      (∀ p ∈ ext, p = .ceil C C (ruleRight c r) ∨ (p = .not C (anyOfC C comps))) ∧
      Kore.Pattern.ceil C C (ruleRight c r) ∈ ext := by
    by_cases hce : comps.isEmpty
    · refine ⟨[.ceil C C (ruleRight c r)], by unfold prioRuleK; dsimp only; rw [if_pos hce], ?_, by simp⟩
      intro p hp; exact Or.inl (List.mem_singleton.mp hp)
    · refine ⟨[.not C (anyOfC C comps), .ceil C C (ruleRight c r)], by unfold prioRuleK; dsimp only; rw [if_neg hce],
        ?_, by simp⟩
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hvarsL : ∀ k ∈ KoreAML.varsOf (.and C (left ++ ext)), k ∈
      KoreAML.tableOf [] (.rewrites C (.and C (left ++ ext)) (ruleRight c r)) := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C (.and C (left ++ ext)) _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hvarsR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈
      KoreAML.tableOf [] (.rewrites C (.and C (left ++ ext)) (ruleRight c r)) := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C (.and C (left ++ ext)) _)
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ hk
  unfold TieRulePair.RuleGuard
  rw [hpat]
  generalize KoreAML.tableOf [] (.rewrites C (.and C (left ++ ext)) (ruleRight c r)) = tbl at hvarsL hvarsR ⊢
  obtain ⟨hLv, hLP⟩ := hkeysL (ps := left ++ ext) (fun q hq => List.mem_append_left _ hq)
    (List.mem_append_right _ hceilm)
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  have hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ tbl := fun k hk => hvarsL _ (hLP k hk)
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.post), k ∈ tbl := fun k hk =>
    hvarsR _ (Model.varsOf_post_ruleRight hs hk)
  generalize hev : overV c I tbl r.vars σ (KoreAML.val0 : Valuation M) = e'
  have hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      elemOf c I ((σ.lookup i).getD default) := fun i hi => by rw [← hev]; exact overV_at hkeys hi
  have hag : Agrees c I tbl vs σ e' := by rw [← hev]; exact overV_agrees hIΓ hkeys hσ
  have htake : (left ++ ext).take 2 = [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] := by
    simp [left]
  have hdrop : (left ++ ext).drop 2 = Cond.conj c vs C r.pre ++ ext := by
    simp [left]
  simp only [TieRulePair.extraOf, TieRulePair.leftOf, htake, hdrop]
  intro p hp a ha
  -- the left side holds of x's element alone
  have hlx := ha (Term.kore c vs r.lhs) (List.mem_cons_self ..)
  have hxa : a = elemOf c I x.val :=
    ((elemOf_spec hIΓ x.property e').1 a).mp
      (((patVal_den4 hIΓ hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch (Semantics.lhs_nf OvlOK.ok hr hlhs)).2 a).mp hlx)
  subst hxa
  rcases List.mem_append.mp hp with hp | hp
  · -- `pre` at x's element: it holds at σ (`holds_entails`)
    have hφ' := Model.mem_condConj hp
    subst hφ'
    have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.pre)
      fun i hi => ⟨varOccsCond_lt_twoT r.pre hokP i hi, hkeys i (varOccsCond_lt_twoT r.pre hokP i hi)⟩
    exact (HoldsShape.holds_entails h hIc hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hr hkP top_numbered
      hpre _ (elemOf_top hIΓ x tbl e')).mpr rfl
  · rcases hext p hp with rfl | rfl
    · -- the right side is defined: it evaluates and the `ensures` is `true`
      have hyR := ruleRight_at_pp h hIc hcw hs hrcQ hσ heval hens hpost hkeys hkQ hval hag
      exact ceil_right_pp h hIΓ hs hσ hkeys (fun i hi _ => hval i hi) hyR (elemOf_top hIΓ x tbl e')
    · -- no rule of a smaller priority applies at x
      have hnot : Kore.Pattern.not C (anyOfC C comps) ∈ left ++ ext := List.mem_append_right _ hp
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨anyOfC_empty hD (by
        show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
        rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
        obtain ⟨hr'm, hlt⟩ := List.mem_filter.mp hr'
        have hlt' : r'.prio < r.prio := by simpa using hlt
        have hrc' : r'.opens.any (fun i => (r'.vars[i]?.map c.confined).getD false) = true →
            c.readsConfined = true := fun hany => by
          obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
          simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
          exact Or.inl ⟨r', hr'm, by simp [List.ne_nil_of_mem hi]⟩
        have hvC : ∀ {k}, k ∈ KoreAML.varsOf (applies c r' (canonRulePres r')) → k ∈ tbl := fun hk =>
          hvarsL _ (Model.varsOf_and_mem hnot (by
            simp only [KoreAML.varsOf]
            exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr'm hlt') hk)))
        exact not_applies_guarded_held h hIc hback hcw (hrules r' hr'm).1 (hrules r' hr'm).2 (hlarger r' hr'm hlt') hrc'
          (readsConfined_of_pre hr'm) (hw r' hr'm hlt') (hprio r' hr'm hlt')
          (fun i hi hil => hvC ((Model.varsOf_applies_pp r').1 i hi hil))
          (fun k hk => hvC ((Model.varsOf_applies_pp r').2 k hk)) e'
      · show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
        rw [trSort_srt]
        exact (elemOf_spec hIΓ x.property e').2

end

end Faithful

namespace TieRulePair

open ML Faithful

/-- **The guard at a step's match**, for a semantics meeting `coreOK` whose conditions read no
confined sort: in a model of Γ, `RuleGuard` of the rule's axiom holds at the valuation that gives
the rule's variables the elements of the match σ of a step by the rule. -/
theorem ruleGuard_of_stepBy {c : Semantics} (hcore : c.coreOK = true) (hrc : c.readsConfined = false)
    {r : Rule} {σ : Subst} {x y : Config c} (hb : StepBy c r σ x y) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) :
    RuleGuard (prioRuleK c r) I (overV c I (KoreAML.tableOf [] (prioRuleK c r)) r.vars σ (KoreAML.val0 : Valuation M)) := by
  have hod := openDecided_of_readsConfined hrc
  have hIc : I ⊧ᴵP Γc c := by rw [Γc_plain hrc]; exact hI
  have hrules := Semantics.ruleFactsHeld_of_core hcore
  exact ruleGuard_of_stepBy_held hcore hrules hIc (heldBackAll_holds hcore I hIc) hod.2 (hrules r hb.mem).1
    (readsConfined_of_pre hb.mem) (readsConfined_of_post hb.mem)
    (fun _ _ hlt => List.any_eq_true.mpr ⟨r, hb.mem, by simpa using hlt⟩) hb.hσ hb.hmatch hb.hpre hb.heval
    hb.hens hb.hpost hb.hprio (fun r' hr' _ hn _ => hod.1 r' hr' hn)

/-- **W2 for a rule at a step's match**: in a model of Γ, the text's sentence of a rule holds at the
valuation that gives the rule's variables the elements of a step's match σ, for a semantics meeting
`coreOK` whose conditions read no confined sort (`ruleGuard_of_stepBy`, `rules_w2`). -/
theorem rules_w2_stepBy {c : Semantics} {R : List KoreAML.P} (hcore : c.coreOK = true) (hrc : c.readsConfined = false)
    (h : rulesTieB c R = true) {j : Nat} {r : Rule} {t : KoreAML.P} (hr : c.rules[j]? = some r) (ht : R[j]? = some t)
    {σ : Subst} {x y : Config c} (hb : StepBy c r σ x y) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) (m : M) :
    t.interpret I (overV c I (KoreAML.tableOf [] (prioRuleK c r)) r.vars σ (KoreAML.val0 : Valuation M)) m :=
  rules_w2 h hr ht hI _ (ruleGuard_of_stepBy hcore hrc hb hI) m

end TieRulePair

namespace Cert

open Exec

variable {c : Semantics}

/-- **A step the executable check accepts for one rule is a `StepBy` of that rule**, at a match the
executable matcher lists with the `requires` `true`. -/
theorem stepBy_of_checkStep (hok : c.ok = true) (hsr : c.srReady = true) (hmr : c.matchReady = true)
    {n : Nat} {r : Rule} (hr : r ∈ c.rules) {x y : Config c} (h : checkStep c n r x.val y.val = true) :
    ∃ σ, (σ, some true) ∈ ruleMatches c n r x.val ∧ StepBy c r σ x y := by
  have hsc := sortCtx_of hok hsr (Exec.ovlCase_of hmr)
  have hcc := clauseCtx_of hok
  have hmc := matchCtx_of hmr
  simp only [checkStep, Bool.and_eq_true] at h
  obtain ⟨hlow, hy⟩ := h
  obtain ⟨y', hmem, hs⟩ := List.any_eq_true.mp hy
  rw [same_iff] at hs
  rw [hs] at hmem
  have hlow' : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x.val, σb.2 = some false := by
    intro r' hr' hlt σb hσb
    have h' := List.all_eq_true.mp hlow r' hr'
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h'
    rcases h' with h' | h'
    · exact absurd hlt h'
    · obtain ⟨σ', b⟩ := σb
      obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
      have hc : (σ', reqValC c n r' σ') ∈ ruleMatchesC c n r' x.val := ruleMatchesC_mem.mpr ⟨hσ', rfl⟩
      have hf : reqValC c n r' σ' = some false := by simpa using List.all_eq_true.mp h' _ hc
      exact reqValC_sound hf
  obtain ⟨σ, hσm', he, -, hen⟩ := ruleSuccs_mem hmem
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσm'
  obtain ⟨hm, hws⟩ := List.mem_filter.mp hσm
  have hσ := wellSorted_iff.mp hws
  obtain ⟨_, hpv⟩ := matchP_sound _ (canonV_of_sortOf x.property) hm
  obtain ⟨_, _, _, hreq, hrhs⟩ := ruleOK_of hok hr
  obtain ⟨-, hpre, hpost, -⟩ := Semantics.ok_rule hok hr
  refine ⟨σ, hσm', ⟨hr, hσ, hpv, fun t ht => ?_, by rw [hpre]; exact .top,
    evalT_sound hsc hcc hmc n he (headsOK_fns _) hσ hrhs, ens_sound hok hsr hmr hr hσ hen,
    by rw [hpost]; exact .top, fun r' hr' hlt σ' hσ' hpv' => ?_⟩⟩
  · rw [ht] at hreq
    unfold reqVal at hb
    rw [ht] at hb
    cases he' : evalT c n σ t with
    | none => simp [he'] at hb
    | some v =>
      simp only [he', Option.map_some, Option.some.injEq] at hb
      rw [isTrue_iff.mp hb.symm] at he'
      exact evalT_sound hsc hcc hmc n he' (headsOK_fns _) hσ (reqOK_some hreq)
  · have hσ' := Rule.wellSorted_of_at (Semantics.ok_rule hok hr').2.2.2 hσ'
    obtain ⟨σ₀, hσ₀m, hag⟩ := rule_match_complete hok hmr hr' hσ' hpv'
    have hσ₀ := wellSorted_iff.mp (List.mem_filter.mp hσ₀m).2
    have hf := hlow' r' hr' hlt (σ₀, reqVal c n r' σ₀) (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩)
    simp only at hf
    unfold reqVal at hf
    cases ht : r'.req with
    | none => simp [ht] at hf
    | some t =>
      rw [ht] at hf
      cases he' : evalT c n σ₀ t with
      | none => simp [he'] at hf
      | some v =>
        simp only [he', Option.map_some, Option.some.injEq] at hf
        refine RuleReqFails.intro ht (req_sound hok hsr hmr hr' ht hσ₀ hσ' hag he') ?_
        intro hv
        rw [hv] at hf
        exact absurd (isTrue_iff.mpr rfl) (by rw [hf]; decide)

end Cert

end KCore
