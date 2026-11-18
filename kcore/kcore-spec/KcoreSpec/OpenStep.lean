/-
  KCore. The evaluations a step reads, for a rule whose left side need not bind every variable.

  - `Semantics.rulePlainOpen`: a rule with `\top` predicates and no existential variable, each
    open variable held by the right side under constructors and injections, of a confined sort, or
    held by closed conditions no variable of which the right side, the `ensures` or `post` holds,
    and a rule that competes with a larger one has open condition variables of confined sorts or
    closed conditions. `rulesPlain` asks `Semantics.rulePlainHO2` of each rule
    (`Semantics.rulesPlain_iff_memHeld`, PredPlain.lean), which is `rulePlainOpen` less `r.exs = []`
    and the `\top` predicates, with the first arm reading also the variables the right side holds
    under the symbols `Semantics.holds` names, and a variable a cut of `pre` holds counted with
    those of a confined sort.
  - A term has a result, and a defined result has the term's sort, under a σ that gives the
    variables the term holds values of their sorts (`evalTerm_total_at`, `EvalTerm.sorted_at`):
    other variables are not read.
  - So where every function has a result at arguments of its sorts, a well-sorted rule with that
    conjunct has the results `StepDecided` asks (`Rule.decided_of_total`): its `requires` under a
    σ that gives the variables of the left side and the conditions values
    (`WellSortedAt r.vars r.leftVars`), the variables of the `requires` being among those; its right
    side and `ensures` under a σ that gives every variable one (`WellSorted r.vars`); its predicates
    are `\top`. No variable is asked to be bound by the left side.
  - `sortedOK` and `coreOK` give each rule `ruleSorted` and `rulePlainHO2`
    (`Semantics.ruleFactsHO2_of_sortedOK`, `Semantics.ruleFactsHO2_of_core`, PredPlain.lean); under
    `coreOK` and `FnHyp` every configuration is `StepDecided` (`stepDecided_of_fnHyp`,
    HoldsDecided.lean, which reads `ruleSorted` only).
-/
import KcoreSpec.ModelPat
import KcoreSpec.HypWf
import KcoreSpec.Obligations

set_option autoImplicit false

namespace KCore

/-- What `rulesPlain` asks of the rule r with the first arm reading constructors and injections
only (`ctorOccs`), with `\top` predicates and no existential variable. -/
def Semantics.rulePlainOpen (c : Semantics) (r : Rule) : Bool :=
  r.exs.isEmpty && r.pre.isTop && r.post.isTop &&
  (let conf := fun i => (r.vars[i]?.map c.confined).getD false
   let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
   let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
   r.opens.all (fun i => (ctorOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
   (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed))

/-- The predicates of a rule with `rulePlainOpen` are `\top`. -/
theorem Semantics.rulePlainOpen_top {c : Semantics} {r : Rule} (h : c.rulePlainOpen r = true) :
    r.exs = [] ∧ r.pre = .top ∧ r.post = .top := by
  simp only [Semantics.rulePlainOpen, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hex, hpre⟩, hpost⟩, -⟩ := h
  exact ⟨List.isEmpty_iff.mp hex, Cond.eq_top_of_isTop hpre, Cond.eq_top_of_isTop hpost⟩

/-- The variables of a rule's `requires` are among those of its left side and its conditions. -/
theorem Rule.req_leftVars {r : Rule} {t : Term} (ht : r.req = some t) : ∀ i ∈ varOccs t, i ∈ r.leftVars :=
  fun i hi => List.mem_append_right _ (List.mem_append_left _ (by rw [ht]; exact hi))

namespace Faithful

open Model

section
variable {c : Semantics}

mutual
  /-- `EvalTerm.sorted` under a σ that gives the variables the term holds values of their sorts. -/
  theorem EvalTerm.sorted_at (hc : SortCtx c) {σ : Subst} {t : Term} {r : Option GroundTerm}
      (h : EvalTerm c σ t r) {L : List CtorSig} {vars : List Srt} {s : Srt}
      (hL : HeadsOK c L) (hσ : c.WellSortedAt vars (varOccs t) σ)
      (ht : sortOfTerm (c.rhsCtx L) vars t = some s) {v : GroundTerm} (hr : r = some v) :
      c.sortOf v = some s :=
    match h with
    | .var (i := i) => by
      obtain ⟨w, hw, hsw⟩ := hσ i (by rw [varOccs]; exact List.mem_singleton_self i) s (sortOfTerm_var.mp ht)
      rw [hw] at hr
      cases hr
      exact hsw
    | .dv => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      cases hr
      exact sortOf_dv.mpr ⟨hok, rfl⟩
    | .inj (a := a) (b := b) h' => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hr
      exact sortOf_injNormal hc.trans hab (EvalTerm.sorted_at hc h' hL (by rw [varOccs] at hσ; exact hσ) ht' hw)
    | .ctor (f := f) hk hts => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hk
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_some hk₀] at hk'
      cases hk'
      exact sortOf_ctor_intro ⟨k, hk₀, EvalTerms.sorted_at hc hts hL (by rw [varOccs] at hσ; exact hσ) hargs hws, rfl⟩
    | .hook (f := f) (rs := rs) hk hhk hts hh hund => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      cases hws : allSome rs with
      | none => rw [hund hws] at hr; cases hr
      | some ws =>
        have hv := hh ws hws
        rw [hr] at hv
        have hnc : lookupSig c.ctorSigs f = none :=
          Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
        obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hhk
        simp only [Semantics.rhsCtx, List.append_assoc] at hk'
        rw [lookupSig_append_of_none hnc, lookupSig_append_of_some hk₀] at hk'
        cases hk'
        exact hookRes_sorted (fun _ => hc.range) hk₀ (EvalTerms.sorted_at hc hts hL (by rw [varOccs] at hσ; exact hσ) hargs hws) hv
    | .param (f := f) (rs := rs) hk hhk hp hts hr' => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnc : lookupSig c.ctorSigs f = none :=
        Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk)] at hk'
      rw [hr'] at hr
      obtain ⟨ws, -, hv⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨k₀, hk₀, hs⟩ := c.paramVal_sorted hv
      rw [lookupSig_append_of_some (l' := c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) (k := k₀.sig)
        (by rw [c.lookupSig_params, hk₀]; rfl)] at hk'
      cases hk'
      exact hs
    | .call (f := f) hk hhk hts hvs hf hp => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      have hnc : lookupSig c.ctorSigs f = none :=
        Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
      simp only [Semantics.rhsCtx, List.append_assoc] at hk'
      rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
        lookupSig_append_of_none (c.lookupSig_params_of_not hp)]
        at hk'
      have hfn0 : ∃ fn0, c.lookupFn f = some fn0 := match hf with
        | .clause hfn' .. => ⟨_, hfn'⟩
        | .rest hfn' _ => ⟨_, hfn'⟩
        | .ensFails hfn' .. => ⟨_, hfn'⟩
        | .clauseEx hfn' .. => ⟨_, hfn'⟩
        | .exNone hfn' .. => ⟨_, hfn'⟩
      obtain ⟨hkL, hkn⟩ := lookupSig_spec (rhs_lookup_fn hc hfn0.choose_spec hk')
      obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
      have hlook : c.lookupFn f = some fn := by
        rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc.nodupFns hfn
      exact Eval.sorted hc hf hlook (EvalTerms.sorted_at hc hts hL (by rw [varOccs] at hσ; exact hσ) hargs hvs) hr
    | .callUndef .. => by cases hr
    | .ovlFn (f := f) (vs := ws) (kg := kg) _ ho hts hws hlo hcov hf => by
      -- the covering function's value, of its result sort, lifted to the symbol's
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hc hL hk' ho
      rw [hlo] at hlo'
      cases hlo'
      obtain ⟨r1, hr1, rfl⟩ := Option.map_eq_some_iff.mp hr
      have H := hc.ovl.resolve_left fun hno => by simp [Semantics.lookupOvl, hno] at hlo
      have HH : OvlLaws.OvlHyp c := ⟨H.1, hc.trans, H.2⟩
      obtain ⟨o2, hlo2, hkg, hb, hcv⟩ := OvlLaws.fnCover_some_parts hcov
      rw [hlo] at hlo2
      cases hlo2
      obtain ⟨fn, -, hfn, hsig⟩ := OvlLaws.byFn_fn hkg hb
      have ha : fn.args = kg.args := by rw [hsig]
      have hres' : fn.result = kg.result := by rw [hsig]
      obtain ⟨hlen, -, hres, -⟩ := OvlLaws.over_ovlF HH.fnFacts hlo hkg
      obtain ⟨-, -, hlies⟩ := OvlLaws.covers_iff.mp hcv
      have hvs := EvalTerms.sorted_at hc hts hL (by rw [varOccs] at hσ; exact hσ) hargs hws
      have hs1 := Eval.sorted hc hf hfn (by rw [ha]; exact OvlLaws.sortsOf_stripAll hlen hvs hlies) hr1
      rw [hres'] at hs1
      exact OvlLaws.sortOf_lift HH hs1 hres
    | .ovl (f := f) (rs := rs) hk ho hts hnf => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hc hL hk' ho
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hr
      have H := hc.ovl.resolve_left fun hno => by simp [Semantics.lookupOvl, hno] at hlo
      have HH : OvlLaws.OvlHyp c := ⟨H.1, hc.trans, H.2⟩
      exact OvlLaws.sortOf_norm_ovlF HH HH.fnFacts hlo
        (EvalTerms.sorted_at hc hts hL (by rw [varOccs] at hσ; exact hσ) hargs hws) (hnf ws hws)
  termination_by structural h
  theorem EvalTerms.sorted_at (hc : SortCtx c) {σ : Subst} {ts : List Term}
      {rs : List (Option GroundTerm)} (h : EvalTerms c σ ts rs) {L : List CtorSig}
      {vars : List Srt} {ss : List Srt} (hL : HeadsOK c L) (hσ : c.WellSortedAt vars (varOccsList ts) σ)
      (hts : sortsOfTerms (c.rhsCtx L) vars ts = some ss) {ws : List GroundTerm}
      (hws : allSome rs = some ws) : c.sortsOf ws = some ss :=
    match h with
    | .nil => by
      rw [sortsOfTerms_nil.mp hts]
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      exact sortsOf_nil
    | .cons h' hs => by
      obtain ⟨s, ss', ht, hts', rfl⟩ := sortsOfTerms_cons.mp hts
      simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
      obtain ⟨w, hw, ws', hws', rfl⟩ := hws
      rw [varOccsList] at hσ
      exact sortsOf_cons.mpr ⟨s, ss', EvalTerm.sorted_at hc h' hL (hσ.mono fun i hi => List.mem_append_left _ hi) ht hw,
        EvalTerms.sorted_at hc hs hL (hσ.mono fun i hi => List.mem_append_right _ hi) hts' hws', rfl⟩
  termination_by structural h
end

mutual
  /-- `evalTerm_total` under a σ that gives the variables the term holds values of their sorts. -/
  theorem evalTerm_total_at (h : HypSoundCore c) (hft : FnTerminates c) {L : List CtorSig} (hL : HeadsOK c L)
      {vars : List Srt} {σ : Subst} : ∀ {t : Term} {s : Srt}, c.WellSortedAt vars (varOccs t) σ →
      sortOfTerm (c.rhsCtx L) vars t = some s → ∃ r, EvalTerm c σ t r
    | .var _, _, _, _ => ⟨_, .var⟩
    | .dv _ _, _, _, _ => ⟨_, .dv⟩
    | .inj _ _ t, _, hσ, ht => by
      obtain ⟨-, ht', -⟩ := sortOfTerm_inj.mp ht
      obtain ⟨r, hr⟩ := evalTerm_total_at h hft hL (by rw [varOccs] at hσ; exact hσ) ht'
      exact ⟨_, .inj hr⟩
    | .as _ _, _, _, ht => absurd ht sortOfTerm_rhs_as
    | .app f ts, _, hσ, ht => by
      rw [varOccs] at hσ
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      obtain ⟨rs, hrs⟩ := evalTerms_total_at h hft hL hσ hargs
      by_cases hc : c.isCtor f = true
      · exact ⟨_, .ctor hc hrs⟩
      have hc' : c.isCtor f = false := by simpa using hc
      by_cases hh : isHook f = true
      · cases has : allSome rs with
        | none => exact ⟨none, .hook hc' hh hrs (fun ws hw => by rw [has] at hw; cases hw) (fun _ => rfl)⟩
        | some ws =>
          obtain ⟨o, ho⟩ := Semantics.hookRes_some (c := c) hh ws
          exact ⟨o, .hook hc' hh hrs (fun ws' hw => by rw [has] at hw; cases hw; exact ho)
            (fun hn => by rw [has] at hn; cases hn)⟩
      have hh' : isHook f = false := by simpa using hh
      by_cases hp : c.isParam f = true
      · exact ⟨_, .param hc' hh' hp hrs rfl⟩
      have hp' : c.isParam f = false := by simpa using hp
      cases hov : c.isOvl f with
      | true =>
        have hsc := sortCtx_of_all h.1 h.2.1 (OvlOK.ovlCase h.2.2.2.2.2.2.2.2)
        obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk hov
        exact EvalTerm.ovl_result (h.2.2.2.2.2.2.2.2.hyp hsc.trans).fnFacts hc' hov hrs hlo
          (fun ws has => EvalTerms.sorted_at hsc hrs hL hσ hargs has)
          (fun kg _ _ fn hfn _ hn vs hvs => hn ▸ hft fn hfn vs hvs)
      | false =>
      cases has : allSome rs with
      | none => exact ⟨none, .callUndef hc' hh' hrs has hp'⟩
      | some ws =>
        subst hkn
        obtain ⟨fn, hfn, rfl⟩ := rhsHead_fn h.2.2.2.2.2.2.2.2.ok hL hkm hc' hh' hp' hov
        have hws : c.sortsOf ws = some fn.args :=
          EvalTerms.sorted_at (sortCtx_of_all h.1 h.2.1 (OvlOK.ovlCase h.2.2.2.2.2.2.2.2)) hrs hL hσ hargs has
        obtain ⟨r, hr⟩ := fn_total h hft hfn hws
        exact ⟨r, .call hc' hh' hrs has hr hp'⟩
    termination_by structural t _ _ _ => t
  theorem evalTerms_total_at (h : HypSoundCore c) (hft : FnTerminates c) {L : List CtorSig} (hL : HeadsOK c L)
      {vars : List Srt} {σ : Subst} : ∀ {ts : List Term} {ss : List Srt}, c.WellSortedAt vars (varOccsList ts) σ →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → ∃ rs, EvalTerms c σ ts rs
    | [], _, _, _ => ⟨[], .nil⟩
    | t :: ts, _, hσ, hs => by
      rw [varOccsList] at hσ
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨r, hr⟩ := evalTerm_total_at h hft hL (hσ.mono fun i hi => List.mem_append_left _ hi) h1
      obtain ⟨rs, hrs⟩ := evalTerms_total_at h hft hL (hσ.mono fun i hi => List.mem_append_right _ hi) h2
      exact ⟨r :: rs, .cons hr hrs⟩
    termination_by structural ts _ _ _ => ts
end

/-- **The evaluations a step by a rule reads have results**, for a well-sorted rule with
`rulePlainOpen` (its left side need not bind every variable), where every function has a result
at arguments of its sorts: its `requires` under a σ that gives the variables of the left side and
the conditions values; its right side and `ensures` under a σ that gives every variable one; its
predicates, `\top`. These are the two conjuncts `StepDecided` asks of each rule. The rule need not
be one of `c`'s. -/
theorem Rule.decided_of_total (h : HypSoundCore c) (hft : FnTerminates c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b) := by
  obtain ⟨-, hreq, hens, hrhs⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hpre, hpost⟩ := Semantics.rulePlainOpen_top hp
  have hreqs : ∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hreq; simpa [reqOK] using hreq
  have hensS : ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
    fun t ht => by rw [ht] at hens; simpa [reqOK] using hens
  refine ⟨fun σ hσ _ => ⟨fun t ht => evalTerm_total_at h hft fns_headsOK
      (hσ.mono (Rule.req_leftVars ht)) (hreqs t ht), true, hpre ▸ .top⟩,
    fun σ hσ _ _ _ => ⟨evalTerm_total h hft fns_headsOK hσ hrhs,
      fun e he => evalTerm_total h hft fns_headsOK hσ (hensS e he), true, hpost ▸ .top⟩⟩

/-- Every configuration is `StepDecided` where every function has a result at arguments of its
sorts and every rule is well sorted with `rulePlainOpen`. -/
theorem stepDecided_of_rules (h : HypSoundCore c) (hft : FnTerminates c)
    (hr : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainOpen r = true) (x : GroundTerm) :
    StepDecided c x :=
  fun r hmem _ => Rule.decided_of_total h hft (hr r hmem).1 (hr r hmem).2 x

end

end Faithful

open Faithful

/-- `Rule.decided_of_total` under `coreOK` and `FnHyp`: for a rule r with `ruleSorted` and
`rulePlainOpen`, the evaluations a step by r reads have results. -/
theorem Rule.decided_of_fnHyp {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) {r : Rule}
    (hs : c.ruleSorted r = true) (hp : c.rulePlainOpen r = true) (x : GroundTerm) :
    (∀ σ, c.WellSortedAt r.vars r.leftVars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → ∃ v, EvalTerm c σ t v) ∧ ∃ b, Holds c r.vars.length σ r.pre b) ∧
    (∀ σ, c.WellSorted r.vars σ → PatVal c σ r.lhs x →
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) → Holds c r.vars.length σ r.pre true →
        (∃ v, EvalTerm c σ r.rhs v) ∧ (∀ e, r.ens = some e → ∃ w, EvalTerm c σ e w) ∧
        ∃ b, Holds c r.vars.length σ r.post b) :=
  Faithful.Rule.decided_of_total (hypSound_of_core h) hf.1 hs hp x

end KCore
