/-
  KCore, checked layer: the executable evaluation is sound (toward `Exec.step_iff`, Exec.lean).

  `evalT_sound`: a result the executable evaluation computes is the `EvalTerm` result, for a
  well-sorted term under a well-sorted σ in a core that `ok`, `srReady` and `matchReady` accept.
  A clause the executable step skips fails (`Fails`): every well-sorted σ under which its patterns
  denote the arguments is above one the matcher found (`matchL_complete`), with the same
  values on the clause's variables, and the `requires` evaluated there is not `true`
  (`EvalTerm.congr`: a term's result depends on σ only through its variables).
-/
import KcoreSpec.MatchMap

set_option autoImplicit false

namespace KCore.Exec

open KCore GroundTerm

variable {c : Semantics}

/-! ## The variables of a well-sorted term are declared -/

mutual
  theorem sortOfTerm_vars {x : TermCtx} {vars : List Srt} : ∀ {t : Term} {s : Srt},
      sortOfTerm x vars t = some s → ∀ i ∈ varOccs t, i < vars.length
    | .var j, s, h, i, hi => by
      simp only [varOccs, List.mem_singleton] at hi
      subst hi
      exact (List.getElem?_eq_some_iff.mp (sortOfTerm_var.mp h)).1
    | .dv _ _, _, _, i, hi => by simp [varOccs] at hi
    | .app f ts, s, h, i, hi => by
      obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp h
      exact sortsOfTerms_vars hargs i (by simpa [varOccs] using hi)
    | .inj a b t, s, h, i, hi => by
      obtain ⟨_, ht, _⟩ := sortOfTerm_inj.mp h
      exact sortOfTerm_vars ht i (by simpa [varOccs] using hi)
    | .as t j, s, h, i, hi => by
      obtain ⟨hj, ht⟩ := sortOfTerm_as h
      simp only [varOccs, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact sortOfTerm_vars ht i hi
      · exact (List.getElem?_eq_some_iff.mp hj).1
  theorem sortsOfTerms_vars {x : TermCtx} {vars : List Srt} : ∀ {ts : List Term} {ss : List Srt},
      sortsOfTerms x vars ts = some ss → ∀ i ∈ varOccsList ts, i < vars.length
    | [], _, _, i, hi => by simp [varOccsList] at hi
    | t :: ts, ss, h, i, hi => by
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp h
      simp only [varOccsList, List.mem_append] at hi
      rcases hi with hi | hi
      · exact sortOfTerm_vars h1 i hi
      · exact sortsOfTerms_vars h2 i hi
end

/-! ## A term's result depends on σ only through its variables -/

mutual
  theorem EvalTerm.congr {σ σ' : Subst} : ∀ {t : Term} {r : Option GroundTerm},
      EvalTerm c σ t r → (∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) → EvalTerm c σ' t r
    | .var i, r, h, ha => by
      have hr := EvalTerm.var_inv h
      rw [hr, ha i (by simp [varOccs])]
      exact .var
    | .dv s l, r, h, _ => by cases h; exact .dv
    | .inj a b t, r, h, ha => by
      cases h with
      | inj h' => exact .inj (EvalTerm.congr h' (fun i hi => ha i (by simpa [varOccs] using hi)))
    | .as t i, r, h, _ => by cases h
    | .app f ts, r, h, ha => by
      have ha' : ∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i :=
        fun i hi => ha i (by simpa [varOccs] using hi)
      cases h with
      | ctor hk hts => exact .ctor hk (EvalTerms.congr hts ha')
      | hook hk hhk hts hh hund => exact .hook hk hhk (EvalTerms.congr hts ha') hh hund
      | param hk hhk hp hts hr => exact .param hk hhk hp (EvalTerms.congr hts ha') hr
      | call hk hhk hts hvs hf hp => exact .call hk hhk (EvalTerms.congr hts ha') hvs hf hp
      | callUndef hk hhk hts hvs hp => exact .callUndef hk hhk (EvalTerms.congr hts ha') hvs hp
      | ovl hk ho hts hnf => exact .ovl hk ho (EvalTerms.congr hts ha') hnf
      | ovlFn hk ho hts hvs hlo hcov hf => exact .ovlFn hk ho (EvalTerms.congr hts ha') hvs hlo hcov hf
  termination_by structural t => t
  theorem EvalTerms.congr {σ σ' : Subst} : ∀ {ts : List Term} {rs : List (Option GroundTerm)},
      EvalTerms c σ ts rs → (∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i) → EvalTerms c σ' ts rs
    | [], rs, h, _ => by cases h; exact .nil
    | t :: ts, rs, h, ha => by
      cases h with
      | cons h1 h2 =>
        exact .cons (EvalTerm.congr h1 (fun i hi => ha i (by simp [varOccsList, hi])))
          (EvalTerms.congr h2 (fun i hi => ha i (by simp [varOccsList, hi])))
  termination_by structural ts => ts
end

/-- σ' below τ agrees with it where it is defined. -/
theorem agree_of_ext {σ τ : Subst} {is : List Nat} (hx : Ext σ τ) (hb : Binds σ is) :
    ∀ i ∈ is, σ.lookup i = τ.lookup i := fun i hi => by
  obtain ⟨w, hw⟩ := hb i hi
  rw [hw, hx i w hw]

/-! ## What evaluation reads of a well-formed core -/

/-- Where every clause of the definition has the predicate `\top` (`clausesPreTop`), each clause of
each function evaluation reads (the definition's and the generated sort predicates) has it. -/
theorem _root_.KCore.Semantics.allFns_preTop {c : Semantics} (hp : c.clausesPreTop = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top := by
  intro fn hfn' cl hcl
  rcases List.mem_append.mp hfn' with hfn | hfn
  · exact Semantics.clausesPreTop_spec hp hfn hcl
  · exact Semantics.sortPreds_pre hfn cl hcl

/-- Where the clauses are plain (`clausesPlain`), each clause of each function evaluation reads has
no existential variable and the right side's predicate `\top`. -/
theorem _root_.KCore.Semantics.allFns_plainCl {c : Semantics} (hp : c.clausesPlain = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top := by
  intro fn hfn' cl hcl
  rcases List.mem_append.mp hfn' with hfn | hfn
  · simp only [Semantics.clausesPlain, Bool.and_eq_true, List.all_eq_true] at hp
    exact ⟨List.isEmpty_iff.mp (hp fn hfn cl hcl).1.1.1, Cond.eq_top_of_isTop (hp fn hfn cl hcl).1.2⟩
  · exact ⟨Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩

/-- `allFns_plainCl` from `sortedOK`, which holds `clausesPlain`. -/
theorem _root_.KCore.Semantics.sortedOK_plainCl {c : Semantics} (h : c.sortedOK = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = [] ∧ cl.post = .top := by
  simp only [Semantics.sortedOK, Bool.and_eq_true] at h
  exact Semantics.allFns_plainCl h.1.2

/-- Where the clauses are plain (`clausesPlain`), no clause of a function of the definition has an
existential variable. -/
theorem _root_.KCore.Semantics.fnsNoExs_of_clausesPlain {c : Semantics} (hp : c.clausesPlain = true) :
    c.FnsNoExs :=
  fun fn hfn cl hcl => (Semantics.allFns_plainCl hp fn (List.mem_append_left _ hfn) cl hcl).1

/-- `fnsNoExs_of_clausesPlain` from `sortedOK`, which holds `clausesPlain`. -/
theorem _root_.KCore.Semantics.fnsNoExs_of_sortedOK {c : Semantics} (h : c.sortedOK = true) : c.FnsNoExs := by
  simp only [Semantics.sortedOK, Bool.and_eq_true] at h
  exact Semantics.fnsNoExs_of_clausesPlain h.1.2

/-- A clause whose right side's predicate is `\top` has it true under every substitution. -/
theorem _root_.KCore.Clause.holds_postTop {c : Semantics} {cl : Clause} (h : cl.post = .top) (σ : Subst) :
    Holds c cl.vars.length σ cl.post true := by
  rw [h]; exact .top

/-- A clause whose predicate is `\top` has it true under every substitution. -/
theorem _root_.KCore.Clause.holds_preTop {c : Semantics} {cl : Clause} (h : cl.pre = .top) (σ : Subst) :
    Holds c cl.vars.length σ cl.pre true := by
  rw [h]; exact .top

/-- The clauses of every function, as `fnOK` checks them, each with the predicates `\top` and no
existential variable: the executable evaluation reads a clause's patterns, its `requires`, its
right-hand side and its `ensures`, not its predicates. -/
def ClauseCtx (c : Semantics) : Prop :=
  ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧
    (∀ cl ∈ fn.clauses, sortsOfTerms c.patCtx cl.vars cl.pats = some fn.args ∧
      noMapInList cl.pats = true ∧
      binds cl.vars.length (varOccsList cl.pats) = true ∧
      reqOK (c.rhsCtx L) cl.vars cl.req = true ∧
      sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
      reqOK (c.rhsCtx L) cl.vars cl.ens = true ∧
      cl.pre = .top ∧ cl.exs = [] ∧ cl.post = .top)

/-- A clause of a function under `ClauseCtx` has no existential variable and the right side's
predicate `\top`. -/
theorem ClauseCtx.plainCl (hcc : ClauseCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : cl.exs = [] ∧ cl.post = .top :=
  let ⟨_, _, h⟩ := hcc fn hfn
  (h cl hcl).2.2.2.2.2.2.2

theorem ClauseCtx.fnsNoExs (hcc : ClauseCtx c) : c.FnsNoExs :=
  fun _ hfn _ hcl => (hcc.plainCl (List.mem_append_left _ hfn) hcl).1

theorem clauseCtx_of_okM (hok : c.okM = true) : ClauseCtx c := by
  simp only [Semantics.okM, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨_, ⟨⟨_, hpl⟩, _⟩⟩, _⟩, hfns⟩, _⟩, _⟩ := hok
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  rotate_left
  · exact ⟨[], fun k hk => (nomatch hk), fun cl hcl =>
      let ⟨h1, h2, h3, h4, h5, h6⟩ := sortPreds_ctx hfn cl hcl
      ⟨h1, h2, h3, h4, h5, h6, Semantics.sortPreds_pre hfn cl hcl, Semantics.sortPreds_exs hfn cl hcl,
        Semantics.sortPreds_post hfn cl hcl⟩⟩
  have hok := (List.all_eq_true.mp hfns) fn hfn
  simp only [Semantics.fnOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hcls, _⟩ := hok
  refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · have := hcls cl hcl
    simp only [Semantics.clauseOK, Bool.and_eq_true, beq_iff_eq] at this
    have htop : cl.pre = .top := Semantics.allFns_preTop hpl.2 fn hfn' cl hcl
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2, htop,
      Semantics.allFns_plainCl hpl.1 fn hfn' cl hcl⟩

theorem clauseCtx_of (hok : c.ok = true) : ClauseCtx c := clauseCtx_of_okM (Semantics.okM_of_ok hok)

/-- No clause of a function of a definition `ok` accepts has an existential variable. -/
theorem _root_.KCore.Semantics.fnsNoExs_of_ok {c : Semantics} (hok : c.ok = true) : c.FnsNoExs :=
  (clauseCtx_of hok).fnsNoExs

theorem binds_all {n : Nat} {occs : List Nat} (h : binds n occs = true) : ∀ i < n, i ∈ occs := by
  simp only [binds, List.all_eq_true] at h
  exact fun i hi => List.contains_iff_mem.mp (h i (List.mem_range.mpr hi))

theorem reqOK_some {x : TermCtx} {vars : List Srt} {t : Term} (h : reqOK x vars (some t) = true) :
    sortOfTerm x vars t = some Srt.bool := by
  simpa [reqOK] using h

theorem mapM_mem {α β : Type} {g : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM g = some l' → ∀ a ∈ l, ∃ b, g a = some b ∧ b ∈ l'
  | [], _, _, a, ha => nomatch ha
  | x :: l, l', h, a, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, hb, List.mem_cons_self ..⟩
    · obtain ⟨b', hb', hm⟩ := mapM_mem hbs a ha
      exact ⟨b', hb', List.mem_cons_of_mem _ hm⟩

theorem mapM_mem' {α β : Type} {g : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM g = some l' → ∀ b ∈ l', ∃ a ∈ l, g a = some b
  | [], l', h, b, hb => by simp at h; subst h; nomatch hb
  | x :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self .., hb₀⟩
    · obtain ⟨a, ha, hg⟩ := mapM_mem' hbs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hg⟩

/-- A well-sorted σ found by the matcher from its clause's patterns. -/
theorem wellSorted_of_below {vars : List Srt} {occs : List Nat} {σ τ : Subst}
    (hτ : c.WellSorted vars τ) (hx : Ext σ τ) (hb : Binds σ occs) (hcov : ∀ i < vars.length, i ∈ occs) :
    c.WellSorted vars σ := fun i s hs => by
  obtain ⟨w, hw⟩ := hb i (hcov i (List.getElem?_eq_some_iff.mp hs).1)
  obtain ⟨w', hw', hsw⟩ := hτ i s hs
  rw [hx i w hw] at hw'
  cases hw'
  exact ⟨w, hw, hsw⟩

/-- A clause all of whose listed matches have a `requires` evaluating to something other than
`true` fails: every well-sorted σ under which its patterns denote the arguments is above one the
matcher found, with the same values on the clause's variables. -/
theorem fails_of_false (hmc : MatchCtx c) {vs : List GroundTerm} {cl : Clause} {n : Nat}
    {L : List CtorSig} {args : List Srt} (hvs : c.sortsOf vs = some args)
    (hpt : sortsOfTerms c.patCtx cl.vars cl.pats = some args) (hmf : noMapInList cl.pats = true)
    (hlc : binds cl.vars.length (varOccsList cl.pats) = true)
    (hreq : reqOK (c.rhsCtx L) cl.vars cl.req = true)
    (hev : ∀ σ t r, evalT c n σ t = some r → c.WellSorted cl.vars σ →
      sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool → EvalTerm c σ t r)
    (hf : ∀ σ ∈ clauseMatches c cl vs, clauseReq c n cl σ = some false) : Fails c vs cl :=
  .intro fun τ hτ' hpv => by
    have hτ := Clause.wellSorted_of_at hlc hτ'
    have hcov := binds_all hlc
    have hn : 4 * termSizeList cl.pats + 1 ≤ patFuel cl.pats := by unfold patFuel; omega
    obtain ⟨σ₀, hm₀, hx₀, _, hb₀⟩ := matchL_complete hmc hτ (patFuel cl.pats) (σ := []) hn hmf hpv hpt
      (fun _ _ h => by simp [List.lookup] at h)
    have hσ₀ := wellSorted_of_below hτ hx₀ hb₀ hcov
    have hb := hf σ₀ (List.mem_filter.mpr ⟨hm₀, wellSorted_iff.mpr hσ₀⟩)
    unfold clauseReq at hb
    cases hrq : cl.req with
    | none => simp [hrq] at hb
    | some t =>
      simp only [hrq, Option.map_eq_some_iff] at hb
      rw [hrq] at hreq
      obtain ⟨r₀, h₀, he⟩ := hb
      have hev' := hev σ₀ t r₀ h₀ hσ₀ (reqOK_some hreq)
      have hvars := sortOfTerm_vars (reqOK_some hreq)
      have hagree : ∀ i ∈ varOccs t, σ₀.lookup i = τ.lookup i := fun i hi =>
        agree_of_ext hx₀ hb₀ i (hcov i (hvars i hi))
      exact .intro hrq (EvalTerm.congr hev' hagree) (fun he' => by
        rw [he', isTrue_iff.mpr rfl] at he; cases he)

/-! ## Soundness of the executable evaluation -/

section
set_option linter.unusedSectionVars false
variable (hsc : SortCtx c) (hcc : ClauseCtx c) (hmc : MatchCtx c)
include hsc hcc hmc

mutual
  theorem evalT_sound : ∀ (n : Nat) {σ : Subst} {t : Term} {r : Option GroundTerm}
      {vars : List Srt} {L : List CtorSig} {s : Srt},
      evalT c n σ t = some r → HeadsOK c L → c.WellSorted vars σ →
      sortOfTerm (c.rhsCtx L) vars t = some s → EvalTerm c σ t r
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [evalT] at h
    | n + 1, σ, .var i, r, _, _, _, h, _, _, _ => by
      simp only [evalT, Option.some.injEq] at h; subst h; exact .var
    | n + 1, σ, .dv s l, r, _, _, _, h, _, _, _ => by
      simp only [evalT, Option.some.injEq] at h; subst h; exact .dv
    | n + 1, σ, .as t i, r, _, _, _, h, _, _, _ => by simp [evalT] at h
    | n + 1, σ, .inj a b t, r, vars, L, s, h, hL, hσ, ht => by
      simp only [evalT, Option.map_eq_some_iff] at h
      obtain ⟨r₀, h₀, rfl⟩ := h
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      exact .inj (evalT_sound n h₀ hL hσ ht')
    | n + 1, σ, .app f ts, r, vars, L, s, h, hL, hσ, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      simp only [evalT, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rs, hrs, hk⟩ := h
      have hts := evalTs_sound n hrs hL hσ hargs
      by_cases hc : c.isCtor f = true
      · simp only [hc, ↓reduceIte, Option.pure_def, Option.some.injEq] at hk
        subst hk
        exact .ctor hc hts
      · have hc' : c.isCtor f = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte] at hk
        by_cases hh : isHook f = true
        · simp only [hh, ↓reduceIte] at hk
          refine .hook hc' hh hts (fun vs hvs => by rw [hvs] at hk; exact hk) (fun hn => ?_)
          rw [hn] at hk; simpa using hk.symm
        · have hh' : isHook f = false := by simpa using hh
          simp only [hh', Bool.false_eq_true, ↓reduceIte] at hk
          by_cases hp : c.isParam f = true
          · simp only [hp, ↓reduceIte, Option.pure_def, Option.some.injEq] at hk
            exact .param hc' hh' hp hts hk.symm
          · have hp' : c.isParam f = false := by simpa using hp
            simp only [hp', Bool.false_eq_true, ↓reduceIte] at hk
            cases hall : allSome rs with
            | none =>
              rw [hall] at hk
              simp only [Option.pure_def, Option.some.injEq] at hk
              subst hk
              exact .callUndef hc' hh' hts hall hp'
            | some vs =>
              rw [hall] at hk
              have hnc : lookupSig c.ctorSigs f = none :=
                Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc')
              simp only [Semantics.rhsCtx, List.append_assoc] at hk'
              rw [lookupSig_append_of_none hnc,
                lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hh'),
                lookupSig_append_of_none (c.lookupSig_params_of_not hp')] at hk'
              obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (by simp [Semantics.lookupOvl, hmc.noOvl]) hk')
              obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
              have hlook : c.lookupFn f = some fn := by
                rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
              have hvs := EvalTerms.sorted hsc hts hL hσ hargs hall
              exact .call hc' hh' hts hall (evalF_sound n hk hlook hvs) hp'
  theorem evalTs_sound : ∀ (n : Nat) {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}
      {vars : List Srt} {L : List CtorSig} {ss : List Srt},
      evalTs c n σ ts = some rs → HeadsOK c L → c.WellSorted vars σ →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → EvalTerms c σ ts rs
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [evalTs] at h
    | n + 1, σ, [], rs, _, _, _, h, _, _, _ => by
      simp only [evalTs, Option.some.injEq] at h; subst h; exact .nil
    | n + 1, σ, t :: ts, rs, vars, L, ss, h, hL, hσ, hts => by
      simp only [evalTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, rs', hrs', rfl⟩ := h
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
      exact .cons (evalT_sound n hr hL hσ h1) (evalTs_sound n hrs' hL hσ h2)
  theorem evalF_sound : ∀ (n : Nat) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
      {fn : Fn}, evalF c n f vs = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      Eval c f vs r
    | 0, _, _, _, _, h, _, _ => by simp [evalF] at h
    | n + 1, f, vs, r, fn, h, hfn, hvs => by
      simp only [evalF, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨fn', hfn', h⟩ := h
      rw [hfn] at hfn'
      cases hfn'
      exact firstClause_sound n h hfn hvs (pre := []) rfl (fun _ h => nomatch h)
  /-- The evaluator tries the clauses in order of priority (`byPrio`): where it returns from a
  clause, every clause before it failed, among them every clause of a smaller priority
  (`byPrio_lt`). -/
  theorem firstClause_sound : ∀ (n : Nat) {fn : Fn} {vs : List GroundTerm} {cls : List Clause}
      {r : Option GroundTerm} {f : Sym} {pre : List Clause},
      firstClause c n vs (c.fnRest fn vs) cls = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      byPrio fn.clauses = pre ++ cls → (∀ cl ∈ pre, Fails c vs cl) → Eval c f vs r
    | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [firstClause] at h
    | n + 1, fn, vs, [], r, f, pre, h, hfn, hvs, hcls, hpre => by
      have hall : ∀ cl ∈ fn.clauses, Fails c vs cl := fun cl hcl =>
        hpre cl (by rw [← List.append_nil pre, ← hcls]; exact mem_byPrio.mpr hcl)
      simp only [firstClause, Option.some.injEq] at h
      subst h
      exact .rest hfn hall
    | n + 1, fn, vs, cl :: rest, r, f, pre, h, hfn, hvs, hcls, hpre => by
      obtain ⟨L, hL, hclk⟩ := hcc fn (lookupFn_spec hfn).1
      have hin : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), x ∈ fn.clauses ∧ x.prio = cl.prio :=
        fun x hx => ⟨mem_byPrio.mp (by rw [hcls]; exact List.mem_append_right _ (List.takeWhile_subset _ hx)),
          prio_of_mem_takeWhile hx⟩
      rw [firstClause_cons] at h
      split at h
      · rename_i r' hfind
        cases h
        obtain ⟨⟨cl', σ, b⟩, hmem, hres⟩ := List.exists_of_findSome?_eq_some hfind
        obtain ⟨hcl', hσm, rfl⟩ := mem_candidates.mp hmem
        obtain ⟨hcf, hpr⟩ := hin cl' hcl'
        obtain ⟨_, _, _, hreq, hrhs, hensOK, htop, hexs, hpostT⟩ := hclk cl' hcf
        obtain ⟨hmL, hws⟩ := List.mem_filter.mp hσm
        have hσw := wellSorted_iff.mp hws
        obtain ⟨_, hpv⟩ := matchL_sound _ (canonVs_of_sortsOf hvs) hmL
        unfold candResult at hres
        simp only at hres
        split at hres
        · rename_i hb
          have hreqE : ∀ t, cl'.req = some t → EvalTerm c σ t (some (bool true)) := fun t ht => by
            have hb' : clauseReq c n cl' σ = some true := by simpa using hb
            unfold clauseReq at hb'
            rw [ht] at hb' hreq
            obtain ⟨r₀, h₀, he⟩ := Option.map_eq_some_iff.mp hb'
            rw [← isTrue_iff.mp he]
            exact evalT_sound n h₀ hL hσw (reqOK_some hreq)
          have hpreE : Holds c cl'.vars.length σ cl'.pre true := by rw [htop]; exact .top
          have hprioE : ∀ x ∈ fn.clauses, x.aside = false → x.prio < cl'.prio → Fails c vs x :=
            fun x hx _ hlt => hpre x (byPrio_lt hcls hx (by omega))
          unfold candBody at hres
          split at hres
          · rename_i he
            refine .clause hfn hcf hσw hpv hreqE hpreE hprioE hexs (evalT_sound n hres hL hσw hrhs) (fun t ht => ?_)
              (Clause.holds_postTop hpostT σ)
            unfold clauseEns at he
            rw [ht] at he hensOK
            obtain ⟨r₀, h₀, he'⟩ := Option.map_eq_some_iff.mp he
            rw [← isTrue_iff.mp he']
            exact evalT_sound n h₀ hL hσw (reqOK_some hensOK)
          · rename_i he
            cases hres
            unfold clauseEns at he
            split at he
            · cases he
            · rename_i t ht
              rw [ht] at hensOK
              obtain ⟨r₀, h₀, he'⟩ := Option.map_eq_some_iff.mp he
              exact .ensFails hfn hcf hσw hpv hreqE hpreE hprioE hexs ht (evalT_sound n h₀ hL hσw (reqOK_some hensOK))
                (fun h => by rw [isTrue_iff.mpr h] at he'; cases he')
          · cases hres
        · cases hres
      · split at h
        · rename_i hall
          refine firstClause_sound n h hfn hvs (pre := pre ++ (cl :: rest).takeWhile (·.prio == cl.prio))
            (by rw [hcls, List.append_assoc, List.takeWhile_append_dropWhile]) (fun x hx => ?_)
          rcases List.mem_append.mp hx with hx | hx
          · exact hpre x hx
          · obtain ⟨hxf, _⟩ := hin x hx
            obtain ⟨hpt, hmf, hlc, hreq, _⟩ := hclk x hxf
            exact fails_of_false hmc hvs hpt hmf hlc hreq
              (fun σ t r h hσ ht => evalT_sound n h hL hσ ht) (fun σ hσ => by
                have := List.all_eq_true.mp hall (x, σ, clauseReq c n x σ) (mem_candidates.mpr ⟨hx, hσ, rfl⟩)
                simpa using this)
        · cases h
end

/-- Where every candidate of the clauses `cls` (`candidates`) has a `requires` that is not `true`,
every clause of `cls` fails. -/
theorem class_fails {f : Sym} {fn : Fn} {vs : List GroundTerm} {n : Nat} {cls : List Clause}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (hin : ∀ x ∈ cls, x ∈ fn.clauses)
    (hall : (candidates c n vs cls).all (·.2.2 == some false) = true) : ∀ x ∈ cls, Fails c vs x := by
  intro x hx
  obtain ⟨L, hL, hclk⟩ := hcc fn (lookupFn_spec hfn).1
  obtain ⟨hpt, hmf, hlc, hreq, _⟩ := hclk x (hin x hx)
  exact fails_of_false hmc hvs hpt hmf hlc hreq
    (fun σ t r h hσ ht => evalT_sound hsc hcc hmc n h hL hσ ht) (fun σ hσ => by
      have := List.all_eq_true.mp hall (x, σ, clauseReq c n x σ) (mem_candidates.mpr ⟨hx, hσ, rfl⟩)
      simpa using this)

end

end KCore.Exec
