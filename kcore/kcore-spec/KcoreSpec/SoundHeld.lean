/-
  KCore. Soundness at a step, for rules with `rulePlainHeldH`.

  `not_applies_guarded_held`, `step_sound_held` and `sound_at_held` are the `_pp` statements of
  SoundPP.lean with the per-rule fact `rulePlainHeldH c H`: a competitor that does not apply
  holds x's element in no `applies` by `not_applies_of_notApplies_held`, in a model where each
  symbol of H that is no constructor has `HeldBack`; `sound_at_held` asks it of every model of
  `Γc` (`HeldBackAll c H`).
-/
import KcoreSpec.SoundPP
import KcoreSpec.FamExValuesHeld
import KcoreSpec.CompeteHeld

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML

open KoreAML (DefOK VarTable)

open HoldsShape (hasBinder Reads reads_of_agrees)

section

variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

variable {H : Sym → Bool}

/-- **A competitor that does not apply at x holds x's element in no `applies`**, for a competitor
with a `pre`: `not_applies_of_notApplies_held` with `hw` asking decided conditions only where the
left side matches x (`applies_match_pp`), as `sound_at`'s `hw` gives them. -/
theorem not_applies_guarded_held (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainHeldH H r = true)
    (hlarger : c.rules.any (fun r'' => r.prio < r''.prio) = true)
    (hrc : r.opens.any (fun i => (r.vars[i]?.map c.confined).getD false) = true → c.readsConfined = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    {x : Config c} (hw : r.needsWitness c = true → (∃ σ', PatVal c σ' r.lhs x.val) → r.CondDecided c)
    (hna : NotApplies c r x.val)
    {tbl : VarTable} (hkeys : ∀ i < r.vars.length, i ∈ r.leftVars → canonKey c r.vars i ∈ tbl)
    (hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre), k ∈ tbl)
    (e : Valuation M) :
    ¬ (KoreAML.tr ⟨tbl, []⟩ (applies c r (canonRulePres r))).interpret I e (elemOf c I x.val) := fun hm =>
  not_applies_of_notApplies_held h hI hcw hback hs hp hlarger hrc hrcP
    (fun hn => hw hn (applies_match_pp h (fun φ hφ => hI φ (Or.inl hφ)) hs hkeys e hm)) hna hkeys hkP e hm

/-- **A step has a successor among its instances**, in a model of `Γc` that holds the rule's axiom,
for a rule with a `pre` and a `post`: x's element is in the axiom's left part (the left side,
`⌈req = true⌉`, `pre` by `holds_entails` at `hpre`, no competitor's `applies` by
`not_applies_guarded_held`, the right side defined by `ruleRight_at_pp` and `ceil_right_pp`), so an
element after it is in the right side, and in `famEx c r σ` (`famEx_of_right_pp`). A binder in
`pre` or `post` asks `readsConfined`. The rule's own `rulePlainHeldH` is not read; the competitors'
is, through `hrules`. -/
theorem step_sound_held (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (hIc : I ⊧ᴵP Γc c)
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) {r : Rule}
    (hs : c.ruleSorted r = true) (_hp : c.rulePlainHeldH H r = true)
    (hrcP : hasBinder r.pre = true → c.readsConfined = true)
    (hrcQ : hasBinder r.post = true → c.readsConfined = true)
    (hax : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", { sortVars := [], pattern := prioRuleK c r, attributes := [] }⟩).pat)
    (hlarger : ∀ r' ∈ c.rules, r'.prio < r.prio → c.rules.any (fun r'' => r'.prio < r''.prio) = true)
    {σ : Subst} {x y : Config c} (hσ : c.WellSorted r.vars σ) (hmatch : PatVal c σ r.lhs x.val)
    (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (famEx c r σ)).interpret I e m := by
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hneg := (neg_of_coreCl hIc (Semantics.sortedOKCl_of_sortedOK hok) hsr (Semantics.coreOK_parts h).2.1 hph hcw (HoldsShape.preReadAll_of_core h hIc))
  have hD := defOK hIΓ
  obtain ⟨hlhs, hocc, hreqs, -, -, -, -, hokP, hokQ, hbdP, hbdQ⟩ := Model.ruleSorted_partsPP hs
  obtain ⟨-, hRv⟩ := Model.ruleRight_keysPP hs
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let left : List Kore.Pattern := [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs))] ++
    Cond.conj c vs C r.pre
  have hcomp : ∀ r' ∈ c.rules, r'.prio < r.prio → applies c r' (canonRulePres r') ∈ comps := fun r' hr' hlt =>
    List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩, rfl⟩
  -- the left side and the `requires` at x's element, under a valuation that agrees with σ
  have hlr : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl vs σ e' →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.lhs)).interpret I e' (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat C (r.req.map (Term.kore c vs)))).interpret I e' (elemOf c I x.val) :=
    fun tbl e' hag =>
      ⟨(patVal_den4 hIΓ hnn.1 hph hsc.trans hσ (canonVars_length c r.vars) hag hmatch hlhs).2 _ |>.mpr
        ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl),
       reqPat_holds hIΓ (fun t ht b => evalTerm_den4ClPre hIΓ hnn hsc hph
        (clauseOpenFactsP_of_sortedOKCl (Semantics.sortedOKCl_of_sortedOK hok)) hneg (HoldsShape.preReadAll_of_core h hIc) (hreq t ht) fns_headsOK hσ
        (canonVars_length c r.vars) hag (hreqs t ht) b) (elemOf_top hIΓ x tbl e')⟩
  -- `pre` at x's element: it holds at σ (`holds_entails`)
  have hpreL : ∀ (tbl : VarTable) (e' : Valuation M), (∀ i < r.vars.length, canonKey c r.vars i ∈ tbl) →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ tbl) → Agrees c I tbl vs σ e' →
      ∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' (elemOf c I x.val) := by
    intro tbl e' hkeys hkP hag φ hφ
    have hφ' := Model.mem_condConj hφ
    subst hφ'
    have hr := reads_of_agrees hσ hag (P := fun i => i ∈ varOccsCond r.vars.length r.pre)
      fun i hi => ⟨varOccsCond_lt_twoT r.pre hokP i hi, hkeys i (varOccsCond_lt_twoT r.pre hokP i hi)⟩
    exact (HoldsShape.holds_entails h hIc hcw r.pre hrcP hokP hbdP (fun i hi _ => hi) hr hkP top_numbered
      hpre _ (elemOf_top hIΓ x tbl e')).mpr rfl
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
  -- the axiom: `\rewrites(L, ∃ē. (rhs ∧ ens ∧ post))`, L read at x's element
  obtain ⟨L, hpat, hLv, hLP, hLread⟩ : ∃ L, prioRuleK c r = .rewrites C L (ruleRight c r) ∧
      (∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L) ∧
      (∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ KoreAML.varsOf L) ∧
      ∀ (tbl : VarTable) (e' : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) → Agrees c I tbl vs σ e' →
        (∀ φ ∈ Cond.conj c vs C r.pre, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e' (elemOf c I x.val)) →
        (KoreAML.tr ⟨tbl, []⟩ (.ceil C C (ruleRight c r))).interpret I e' (elemOf c I x.val) →
        (KoreAML.tr ⟨tbl, []⟩ L).interpret I e' (elemOf c I x.val) := by
    by_cases hce : comps.isEmpty
    · obtain ⟨hk1, hk3⟩ := hkeysL (ps := left ++ [.ceil C C (ruleRight c r)])
        (fun q hq => List.mem_append_left _ hq) (by simp)
      refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_pos hce], hk1, hk3, fun tbl e' _ hag hpm hceil => ?_⟩
      rw [interp_and (by simp)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact (hlr tbl e' hag).1
          · exact (hlr tbl e' hag).2
        · exact hpm p hp
      · rw [List.mem_singleton.mp hp]; exact hceil
    · have hnot : Kore.Pattern.not C (anyOfC C comps) ∈
          left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)] := by simp
      obtain ⟨hk1, hk3⟩ := hkeysL (ps := left ++ [.not C (anyOfC C comps), .ceil C C (ruleRight c r)])
        (fun q hq => List.mem_append_left _ hq) (by simp)
      refine ⟨_, by unfold prioRuleK; dsimp only; rw [if_neg hce], hk1, hk3, fun tbl e' hkL hag hpm hceil => ?_⟩
      rw [interp_and (List.ne_nil_of_mem hnot)]
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact (hlr tbl e' hag).1
          · exact (hlr tbl e' hag).2
        · exact hpm p hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · rw [KoreAML.tr, KoreAML.interp_sNot]
          refine ⟨anyOfC_empty hD (by
            show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
            rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
          · -- a competitor with a `pre`: it does not apply in the model (`not_applies_guarded_held`)
            obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
            obtain ⟨hr'm, hlt⟩ := List.mem_filter.mp hr'
            have hlt' : r'.prio < r.prio := by simpa using hlt
            have hrc' : r'.opens.any (fun i => (r'.vars[i]?.map c.confined).getD false) = true →
                c.readsConfined = true := fun hany => by
              obtain ⟨i, hi, -⟩ := List.any_eq_true.mp hany
              simp only [Semantics.readsConfined, Bool.or_eq_true, List.any_eq_true]
              exact Or.inl ⟨r', hr'm, by simp [List.ne_nil_of_mem hi]⟩
            have hvC : ∀ {k}, k ∈ KoreAML.varsOf (applies c r' (canonRulePres r')) → k ∈ tbl := fun hk =>
              hkL _ (Model.varsOf_and_mem hnot (by
                simp only [KoreAML.varsOf]
                exact List.mem_append_right _ (mem_varsOf_anyOfC (hcomp r' hr'm hlt') hk)))
            exact not_applies_guarded_held h hIc hback hcw (hrules r' hr'm).1 (hrules r' hr'm).2 (hlarger r' hr'm hlt') hrc'
              (readsConfined_of_pre hr'm) (hw r' hr'm hlt') (hprio r' hr'm hlt')
              (fun i hi hil => hvC ((Model.varsOf_applies_pp r').1 i hi hil))
              (fun k hk => hvC ((Model.varsOf_applies_pp r').2 k hk)) e'
          · have hxs := elemOf_spec hIΓ x.property e'
            show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
            rw [trSort_srt]
            exact hxs.2
        · exact hceil
  rw [hpat] at hax
  let ax : Kore.Axiom := { sortVars := [], pattern := .rewrites C L (ruleRight c r), attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hvarsR : ∀ k ∈ KoreAML.varsOf (ruleRight c r), k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_right _ hk
  have hkeys : ∀ i < r.vars.length, canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hLv i hi)
  have hkP : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.pre), k ∈ tbl := fun k hk => hvarsL _ (hLP k hk)
  have hkQ : ∀ k ∈ KoreAML.varsOf (Cond.kore c vs C r.post), k ∈ tbl := fun k hk =>
    hvarsR _ (Model.varsOf_post_ruleRight hs hk)
  let e' := overV c I tbl r.vars σ (KoreAML.val0 : Valuation M)
  have hval : ∀ i < r.vars.length, e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      elemOf c I ((σ.lookup i).getD default) := fun i hi => overV_at hkeys hi
  have hag : Agrees c I tbl vs σ e' := overV_agrees hIΓ hkeys hσ
  -- the guards of the axiom's free variables hold at e'
  have hgd : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, -, rfl⟩ := Model.freeOf_prio_pp (fun r' hr' => (hrules r' hr').1) hs (by rw [hpat]; exact hk')
    obtain ⟨w, hw, hsw⟩ := hσ i (r.vars.getD i 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hval i hi, hw, Option.getD_some]
    exact (elemOf_spec hIΓ hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hIΓ x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hIΓ x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hgd a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hyR := ruleRight_at_pp h hIc hcw hs hrcQ hσ heval hens hpost hkeys hkQ hval hag
  have hceil := ceil_right_pp h hIΓ hs hσ hkeys (fun i hi _ => hval i hi) hyR (elemOf_top hIΓ x tbl e')
  have hL' := himp (by rw [← hxa]; exact hLread tbl e' hvarsL hag (hpreL tbl e' hkeys hkP hag) hceil)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  have hbF := famEx_of_right_pp h hIc hs hσ hkeys hkQ (fun i hi _ => hval i hi) hb e
  have hma : m = a := (ha m).mp (((den_closed c x.val).interp e e' m).mp hm)
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, hbF, happ⟩

end

end Faithful

open ML Faithful Faithful.Model

/-- **Soundness at a step by a rule with a `pre` and a `post`**: `sound_at`'s statement from the
per-rule facts `ruleSorted` and `rulePlainHeldH`. The competitors of r whose left side matches x have
decided closed conditions. -/
theorem sound_at_held (c : Semantics) {H : Sym → Bool} (h : c.coreOK = true)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) (hbk : HeldBackAll c H)
    (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y)
    (hw : ∀ r' ∈ c.rules, r'.prio < r.prio → r'.needsWitness c = true →
      (∃ σ', PatVal c σ' r'.lhs x.val) → r'.CondDecided c)
    (hcw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c) :
    (Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧ (Γc c ⊧ (den c y.val ⇒ famEx c r σ)) := by
  obtain ⟨hsr, hpr⟩ := hrules r hs.mem
  refine ⟨?_, ?_⟩
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    exact step_sound_held h hrules hI (hbk I hI) hcw hsr hpr (readsConfined_of_pre hs.mem) (readsConfined_of_post hs.mem)
      (sat_rules hIΓ (Or.inl ⟨_, List.mem_map.mpr ⟨r, hs.mem, rfl⟩, rfl⟩))
      (fun r' _ hlt => List.any_eq_true.mpr ⟨r, hs.mem, by simpa using hlt⟩) hs.hσ hs.hmatch hs.hreq hs.hpre
      hs.heval hs.hens hs.hpost hs.hprio hw e m
  · intro M _ I hI e m
    have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
    rw [interpret_impl]
    intro hm
    rw [((elemOf_spec hIΓ y.property e).1 m).mp hm]
    exact famEx_mem_pp h hsr (readsConfined_of_post hs.mem) hs.hσ hs.heval hs.hens hs.hpost hI hcw e

end KCore
