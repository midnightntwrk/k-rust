/-
  KCore. Step soundness for the third stage: the functions a rule or a clause calls may be
  partial. Every pattern is plain, as in the first two stages.

  A function has its result at an argument list in two ways (`Eval`): a clause applies (`Eval.clause`,
  the result `none` where its right-hand side is undefined), or every clause fails (`Eval.rest`,
  the interpretation's value, `fnRest`). The first is read through the clause's equation, as in the
  second stage: the equation says `f(X̄) = rhs` where its premise holds, and the right-hand side
  denotes what its result denotes. The second is read through the rest's graph in `ΓFallback`
  (`rest_den`).
-/
import KcoreSpec.FaithfulStage2

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## The third stage -/

/-- **The third stage's scope.** The second stage's (`Stage2`) without its restriction on the
functions called: a rule's or a clause's right-hand side or `requires` may call any function,
defined or not at the arguments. What stays: every rule's
left-hand side and every clause's patterns are plain, and the values are generated (`genWf`,
decidable on the data). -/
def Stage3 (c : Semantics) : Prop :=
  genWf c = true ∧
  (∀ r ∈ c.rules, plainPat c r.lhs = true) ∧
  (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, plainPats c cl.pats = true)

/-- The second stage is inside the third. -/
theorem stage3_of_stage2 {c : Semantics} (h : Stage2 c) : Stage3 c :=
  ⟨h.1, fun r hr => (h.2.1 r hr).1, fun fn hfn cl hcl => (h.2.2 fn hfn cl hcl).1⟩

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) (hst : Stage3 c) [OvlOK c]
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
include hI hnn hsc hst hok hbc

/-- A clause that decides, read in a model: from its right side's reading `ihright` (for the
result `r`), `f` applied to the arguments' elements is what `r` denotes, through `plain_eq` or
`compete_eq`. -/
theorem clause_den3 (hpreTop : c.clausesPreTop = true) {f : Sym} {fn : Fn} {cl : Clause} {ws : List GroundTerm} {σ' : Subst}
    {L : List CtorSig} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses)
    (hws : c.sortsOf ws = some fn.args) (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ' t (some (bool true)))
    (hprio : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c ws cl')
    (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats) (hL : HeadsOK c L)
    (hreqs : ∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hrhss : sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result)
    (henss : ∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)
    (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihright : ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e' m' ↔ Res c I e' r m')
    (ihreq : ∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m')
    (hfails : ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → ModelFails c I cl' ws)
    (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m := by
  have hplain := hst.2.2 fn hmem cl hcl
  have hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (hreqs t ht)
  have hrhsv := varOccs_lt _ hrhss
  have hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length := fun t ht => varOccs_lt t (henss t ht)
  have ihreq' := fun tbl e' hag t ht m' => ihreq t ht tbl e' hag m'
  by_cases hlow : lowerClauses fn cl = []
  · exact plain_eq hI hnn hsc.trans hfn (clauseEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl) (clause_exsNil hok hmem hcl) hws hσ' hmatch hplain hpats
      hbinds hreqv hrhsv hensv hr ihreq' ihright e m
  · refine compete_eq hI hnn hst.1 hsc.trans hfn (competingEquation_mem hcl hlow) (clause_preTop (hpreTop := hpreTop) hok hmem hcl)
          (clause_exsNil hok hmem hcl)
          (fun cl' hcl' => clause_preTop (hpreTop := hpreTop) hok hmem (mem_lowerClauses.mp hcl').1) hws (fun cl' hcl' => ?_) hσ' hmatch hplain hpats
      hbinds hreqv hrhsv hensv hr ihreq' ihright e m
    obtain ⟨hcl'', hna'', hlt⟩ := mem_lowerClauses.mp hcl'
    obtain ⟨hp', hb', L', hL', hrq', -⟩ := clause_ctx hok hbc hmem hcl''
    exact ⟨hp', hb', fun t ht => varOccs_lt t (hrq' t ht), hst.2.2 fn hmem cl' hcl'', hfails cl' hcl'' hna'' hlt⟩

mutual
  /-- **L3, functions, third stage.** A function of the semantics, at arguments of its sorts,
  applied to their elements, is what its result denotes, defined or not: through its clause's
  equation (whose right-hand side may denote nothing), the clauses of a smaller priority it negates
  failing at the arguments; or, where every clause fails, through its rest's graph
  (`rest_den`). -/
  theorem eval_den3 (hpreTop : c.clausesPreTop = true) : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq _ hprio _ hrhs hens _,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      exact clause_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hfn hmem hcl hws hσ' hmatch hreq hprio hpats hbinds hL hreqs hrhss
        henss hr (fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den3 (hpreTop := hpreTop) hrhs hL hσ' (canonVars_length c cl.vars) hag hrhss m')
          (fun t ht m' => evalTerm_den3 (hpreTop := hpreTop) (hens t ht) hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den3 (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => fails_den3 (hpreTop := hpreTop) (hprio cl' hcl'' hna'' hlt) hmem hcl'') e m
    | _, _, _, .ensFails (fn := fn') (cl := cl) (σ := σ') (t := t) hfn' hcl hσ' hmatch hreq _ hprio _ ht he hw,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      exact clause_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc hfn hmem hcl hws hσ' hmatch hreq hprio hpats hbinds hL hreqs hrhss
        henss (fun v hv => by cases hv) (fun tbl e' hag => right_empty hI hnn hmem ht hw
          (fun v hv => EvalTerm.sorted hsc he hL hσ' (henss t ht) hv)
          (fun m' => evalTerm_den3 (hpreTop := hpreTop) he hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den3 (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => fails_den3 (hpreTop := hpreTop) (hprio cl' hcl'' hna'' hlt) hmem hcl'') e m
    | _, ws, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
    | _, _, _, .clauseEx (fn := fn') hfn' hcl _ _ _ _ _ hne _ _ _ _, fn, hfn, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok (lookupFn_spec hfn).1 hcl) hne
    | _, _, _, .exNone (fn := fn') hfn' hcl hne _ _ _ _ _ _ _, fn, hfn, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok (lookupFn_spec hfn).1 hcl) hne
  termination_by structural _ _ _ h => h
  /-- A clause that fails at arguments of its function's sorts fails in the model. -/
  theorem fails_den3 (hpreTop : c.clausesPreTop = true) : ∀ {ws : List GroundTerm} {cl : Clause}, Fails c ws cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ModelFails c I cl ws
    | _, _, .intro h, fn, hfn, hcl => fun σ hσ hpv tbl e hag => reqFails_den3 (hpreTop := hpreTop) (h σ (hσ.at _) hpv) hfn hcl hσ tbl e hag
  termination_by structural _ _ h => h
  theorem reqFails_den3 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → c.WellSorted cl.vars σ →
      ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
      ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
        ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m
    | _, cl, .pre h, fn, hfn, hcl, hσ, tbl, e, hag => by
      rw [clause_preTop (hpreTop := hpreTop) hok hfn hcl] at h; exact absurd h.top_eq (by simp)
    | _, cl, .intro (t := t) (r := r) ht he hr, fn, hfn, hcl, hσ, tbl, e, hag => by
      obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctx hok hbc hfn hcl
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ (hreqs t ht) hv,
        evalTerm_den3 (hpreTop := hpreTop) he hL hσ (canonVars_length c cl.vars) hag (hreqs t ht)⟩
  termination_by structural _ _ h => h
  /-- **L3, terms, third stage.** A well-sorted right-hand side or `requires`, at a valuation that
  agrees with a well-sorted σ, translates to what its result under σ denotes: the value's element,
  or nothing where it is undefined. -/
  theorem evalTerm_den3 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortOfTerm (c.rhsCtx L) vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m
    | _, _, _, .var (i := i), L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨v, hv, -⟩ := hσ i s hi
      rw [hv, tr_var]
      exact hag i v hlt hv m
    | _, _, _, .dv (s := s') (lit := lit), _, _, vs, tbl, e, _, _, _, _, _, _, m => by
      show _ ↔ (den c (.dv s' lit)).interpret I e m
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, _, .inj (a := a) (b := b) (t := t) (r := r) h', L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      have ih := evalTerm_den3 (hpreTop := hpreTop) h' hL hσ hvs hag ht'
      rw [Term.kore, KoreAML.tr_injP]
      cases r with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact injApp_empty (fun m h => ((ih m).mp h)) m
      | some w =>
        have hw := EvalTerm.sorted hsc h' hL hσ ht' rfl
        simp only [Option.map_some, Res]
        rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
        · rw [hn]
          obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp hw
          obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
          rw [injApp_congr ih m]
          show (KoreAML.appList _ [_, _, den c (.inj a' a w')]).interpret I e m ↔ _
          rw [den_inj, den_inj]
          exact coh_at hI h1 hab hx hxs m
        · rw [hn, den_inj]
          exact injApp_congr ih m
    | _, _, _, .ctor (f := f) (ts := ts) (rs := rs) hk hts, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app_plain hnn.1 hk0]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        simp only [Option.map_some, Res]
        rw [den_ctor]
        exact ih.1 ws hall _ _ (fun _ => Iff.rfl) m
    | _, _, _, .hook (f := f) (rs := rs) (r := r) hk hhk hts hh hund, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hks, hkn⟩ := rhs_lookup_hook hk hhk hk'
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hund hall]
        simp only [Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hv := hh ws hall
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_hookRes hI hks hws (by rw [hkn]; exact hv)
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr]
        cases r with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .param (f := f) (rs := rs) (r := r) hk hhk hp hts hr, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨kp, hkp, rfl, hkn⟩ := rhs_lookup_param hk hhk hp hk'
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hr, hall]
        simp only [Option.bind_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkp, hws, rfl⟩))
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr, hr, hall]
        simp only [Option.bind_some]
        cases c.paramVal f ws with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .call (f := f) (rs := rs) (vs := ws) hk hh hts hvs' hf hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨fn, hfnm, rfl, hlook⟩ := rhs_lookup_call hsc hL hk hh hp (Eval.lookupFn_ne hf) hk'
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den3 (hpreTop := hpreTop) hf hlook hws e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovlFn (f := f) (rs := rs) (vs := ws) (o := o) (kg := kg) (r := r) hk ho hts hvs' hlo hcov hf,
        L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [hlo] at hlo'; cases hlo'
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ :=
        OvlLaws.fnCover_fn_ovlF ((inferInstance : OvlOK c).hyp hsc.trans).fnFacts hlo hws hcov
      have hname : kg.name = fn.label := by rw [hsig]
      have hres : kg.result = fn.result := by rw [hsig]
      have hgd := eval_den3 (hpreTop := hpreTop) hf hlook hus e
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := covDen_of hI hsc.trans hlo hws hcov (by rw [hname]; exact hnn.2.1 fn (List.mem_append_left _ hfn))
        (fun v hv => by rw [hres]; exact Eval.sorted hsc hf hlook hus hv) e hgd m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts hnf, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      have ih := evalTerms_den3 (hpreTop := hpreTop) hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := (normDen_of hI hsc.trans).1 hlo hws (hnf ws hall) e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den3 (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss →
      (∀ ws, allSome rs = some ws → ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome rs = none → ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m)
    | _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ => by
      refine ⟨fun ws hws acc acc' hacc m => ?_, fun h => by simp [allSome] at h⟩
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | _, _, _, .cons (t := t) (ts := ts) (r := r) (rs := rs) h hs, L, vars, vs, tbl, e, ss, hL, hσ, hvs, hag, ht => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp ht
      have ih1 := evalTerm_den3 (hpreTop := hpreTop) h hL hσ hvs hag h1
      have ih2 := evalTerms_den3 (hpreTop := hpreTop) hs hL hσ hvs hag h2
      constructor
      · intro ws hws acc acc' hacc m
        simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, rfl, ws', hws', rfl⟩ := hws
        rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact ih2.1 ws' hws' _ _ (KoreAML.interp_app_congr hacc ih1) m
      · intro hn acc m
        rw [Term.koreList, KoreAML.trArgs_cons]
        cases r with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            exact (ih1 b).mp hb) _ m
        | some w =>
          cases hrs : allSome rs with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [allSome, hrs] at hn
  termination_by structural _ _ _ h => h
end

end

/-! ## L4, third stage: a rule's step, its competitors negated -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) (hst : Stage3 c) [OvlOK c]
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
include hI hnn hsc hst hok hbc

/-- A rule that does not apply to a configuration (`NotApplies`) does not apply in the model, its
`requires` read whether defined or not. -/
theorem notApplies_model3 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) (hpre : r.pre = .top) {x : GroundTerm} (h : NotApplies c r x) :
    ModelNotApplies c I r x := by
  intro σ hσ hpv tbl e hag
  obtain ⟨-, hreqs, -⟩ := rule_ctx hok hr
  obtain ⟨_, _, ht, he, hv⟩ := (h σ (hσ.at _) hpv).req_of_top hpre
  · exact ⟨_, _, ht, hv, fun u hu => EvalTerm.sorted hsc he fns_headsOK hσ (hreqs _ ht) hu,
      evalTerm_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc he fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs _ ht)⟩

/-- **A rule's axiom, read in a model**, whatever its left-hand part `L` (`rule_at`, with the
right-hand side read by `evalTerm_den3`). -/
theorem rule_at3 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {L : Kore.Pattern}
    (hpat : prioRuleK c r = .rewrites (srtOf c topCellSort) L
      (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))]))
    (hVin : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf L)
    (hfree : ∀ k ∈ KoreAML.freeOf [] L, ∃ i < r.vars.length, k = canonKey c r.vars i)
    {σ : Subst} (hσ : c.WellSorted r.vars σ) {x y : Config c} (heval : EvalTerm c σ r.rhs (some y.val))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hL : ∀ (tbl : VarTable) (e : Valuation M), (∀ k ∈ KoreAML.varsOf L, k ∈ tbl) →
      Agrees c I tbl (canonVars c r.vars) σ e →
      (∀ b, (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
        reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))])).interpret I e b ↔ (den c y.val).interpret I e b) →
      (KoreAML.tr ⟨tbl, []⟩ L).interpret I e (elemOf c I x.val))
    (e : Valuation M) (m : M) (hm : (den c x.val).interpret I e m) :
    (KoreAML.sNext (den c y.val)).interpret I e m := by
  have hD := defOK hI
  obtain ⟨-, -, hrhss⟩ := rule_ctx hok hr
  have hax := sat_rules hI (Or.inl ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩)
  rw [hpat] at hax
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let ax : Kore.Axiom :=
    { sortVars := [], pattern := .rewrites C L (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]),
      attributes := [] }
  let tbl : VarTable := KoreAML.tableOf ax.sortVars ax.pattern
  let e' : Valuation M := valOf tbl (ruleVal c I r.vars.length σ)
  have hvarsL : ∀ k ∈ KoreAML.varsOf L, k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    show k ∈ KoreAML.varsOf (.rewrites C L _)
    rw [KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hVmem : ∀ i, i < r.vars.length → canonKey c r.vars i ∈ tbl := fun i hi => hvarsL _ (hVin i hi)
  have hVv : ∀ i, i < r.vars.length → e'.evalEvar (tbl.ev (canonKey c r.vars i)) =
      (match σ.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [ruleVal]
    rw [varIdx_eq hi]
    all_goals rfl
  have hvsort : ∀ i, i < r.vars.length → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some (r.vars.getD i 0) :=
    fun i hi => hσ i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c r.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hfree' : ∀ k, k ∈ KoreAML.freeOf [] ax.pattern → ∃ i, i < r.vars.length ∧ k = canonKey c r.vars i := by
    intro k hk
    change k ∈ KoreAML.freeOf [] (.rewrites C L _) at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, h⟩ := hfree k hk; exact ⟨i, hi, h⟩
    · obtain ⟨i, hi, h⟩ := freeOf_right hok hr hk; exact ⟨i, hi, h⟩
  have hg : ∀ k ∈ (ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] ax.pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    have hk' : k ∈ KoreAML.freeOf [] ax.pattern := by simpa [ax] using List.mem_eraseDups.mp hk
    obtain ⟨i, hi, rfl⟩ := hfree' k hk'
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar hD, trSort_srt, ← hkk, hVv i hi, hw]
    exact (elemOf_spec hI hsw e').2
  obtain ⟨a, ha, has⟩ := den_single hI x.property e'
  have hxa : elemOf c I x.val = a := (ha _).mp ((elemOf_spec hI x.property e').1 _ |>.mpr rfl)
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e' a
    unfold srtOf; rw [trSort_srt]; exact has)
  have hP' : (KoreAML.tr ⟨tbl, []⟩ ax.pattern).interpret I e' a := hP
  change (KoreAML.tr ⟨tbl, []⟩ (.rewrites C L _)).interpret I e' a at hP'
  rw [KoreAML.tr] at hP'
  unfold KoreAML.sRewrites at hP'
  rw [KoreAML.interp_sImp] at hP'
  obtain ⟨-, himp⟩ := hP'
  have hrhsR : ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs r.rhs)).interpret I e' b ↔ (den c y.val).interpret I e' b :=
    fun b => evalTerm_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc heval fns_headsOK hσ (canonVars_length c r.vars) hag hrhss b
  have hensS := rule_ctx_ens hok hr
  have hrightR := right_den hI hrhsR (fun a' ha' => reqPat_holds hI (fun t ht b =>
    evalTerm_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc (hens t ht) fns_headsOK hσ (canonVars_length c r.vars) hag (hensS t ht) b) ha')
  have hL' := himp (by rw [← hxa]; exact hL tbl e' hvarsL hag hrightR)
  obtain ⟨n, b, hn, hb, happ⟩ := KoreAML.interp_app.mp hL'
  rw [tr_and2, KoreAML.interp_sAnd] at hb
  have hby := (hrhsR b).mp hb.1
  have hma : m = a := by
    have := ((den_closed c x.val).interp e e' m).mp hm
    exact (ha m).mp this
  rw [hma]
  exact KoreAML.interp_app.mpr ⟨n, b, hn, ((den_closed c y.val).interp e' e b).mp hby, happ⟩

/-- The left-hand side and the `requires` of a rule's axiom hold of the configuration it
matches, at a valuation that agrees with the match. -/
theorem lhs_req_hold3 (hpreTop : c.clausesPreTop = true) {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {x : Config c}
    (hmatch : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    {tbl : VarTable} {e : Valuation M} (hag : Agrees c I tbl (canonVars c r.vars) σ e) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val) ∧
      (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars))))).interpret I e
        (elemOf c I x.val) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hok hr
  have hplain := hst.2.1 r hr
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hxs := elemOf_spec hI x.property e
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC (elemOf c I x.val) := by
    have := hxs.2
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp this
  refine ⟨(patVal_den hI hnn.1 hsc.trans hσ (canonVars_length c r.vars) hag hmatch hplain hlhs).2 _ |>.mpr
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
    rw [evalTerm_den3 (hpreTop := hpreTop) hI hnn hsc hst hok hbc (hreq t hq) fns_headsOK hσ (canonVars_length c r.vars) hag (hreqs t hq) b,
      KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

end

/-- **L4, third stage.** Every step of `Step` is a consequence of `Γ`, for a semantics in the
third stage: in every model, the configuration `x` has the configuration `y` as a successor. The
functions a step reads may be partial: where one is undefined, `Γ` makes its application empty
(its equations where a clause applies, its rest's graph where none does, `eval_den3`), so a
`requires` that calls it there denotes nothing, as `Step` reads it. -/
theorem step_sound_stage3 (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage3 c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  have hpreTop := Semantics.preTop_of_okAll hy.1
  have hy : HypCore c := hy.core
  have hnn : NamesNumbered c := hy.2.2.2.2.2.2
  intro x y hstep M _ I hI e m hm
  obtain ⟨r, hr, σ, hσ, hmatch, hreq, -, heval, hens, -, hprio⟩ := hstep
  obtain ⟨hpre₀, hpost₀⟩ := htop _ hr
  have hex₀ : r.exs = [] := Semantics.sortedOK_exsNil hy.1 hr (hb r hr)
  have hD := defOK hI
  have hsc := sortCtx_of_all hy.1 hy.2.1 (OvlOK.ovlCase inferInstance)
  obtain ⟨hlhs, hreqs, -⟩ := rule_ctx hy.1 hr
  have hbinds := Exec.binds_all (hb _ hr)
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let comps := (c.rules.filter (·.prio < r.prio)).map fun r' => applies c r' (canonRulePres r')
  let L0 : Kore.Pattern := .and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
    .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])]
  have hV0 : ∀ i < r.vars.length, canonKey c r.vars i ∈ KoreAML.varsOf (Term.kore c vs r.lhs) :=
    fun i hi => varsOf_kore c vs r.lhs (hbinds i hi)
  have hfree0 : ∀ k ∈ KoreAML.freeOf [] (Term.kore c vs r.lhs) ++ KoreAML.freeOf [] (reqPat C (r.req.map (Term.kore c vs))),
      ∃ i < r.vars.length, k = canonKey c r.vars i := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs r.lhs hk
      exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
    · cases hq : r.req with
      | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
      | some t =>
        rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
        rw [KoreAML.freeOf] at hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
          exact ⟨i, varOccs_lt t (hreqs t hq) i hi, rfl⟩
        · rw [KoreAML.freeOf] at hk; cases hk
  by_cases hce : comps.isEmpty
  · -- no competitor: the rule's axiom as written
    have hpat : prioRuleK c r = .rewrites C L0
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_pos hce]
    refine rule_at3 (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' _ hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      exact freeOf_rule_parts hy.1 hr hk
    · have h := lhs_req_hold3 (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and3, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      exact ⟨h.1, h.2, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
  · -- competitors: the axiom with their `applies` negated
    have hpat : prioRuleK c r = .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
        .not C (anyOfC C comps), .ceil C C (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))])])
        (.and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]) := by
      rw [prioRuleK_top hex₀ hpre₀ hpost₀]; dsimp only; rw [if_neg hce]
    have hcomp : ∀ φ ∈ comps, ∃ r' ∈ c.rules, r'.prio < r.prio ∧ φ = applies c r' (canonRulePres r') := by
      intro φ hφ
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hφ
      obtain ⟨hr'm, hp⟩ := List.mem_filter.mp hr'
      exact ⟨r', hr'm, by simpa using hp, rfl⟩
    refine rule_at3 (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hr hpat (fun i hi => ?_) (fun k hk => ?_) hσ heval hens
      (fun tbl e' hkeys hag hrhsR => ?_) e m hm
    · show _ ∈ KoreAML.varsOf (.and C _)
      rw [KoreAML.varsOf, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (hV0 i hi))
    · change k ∈ KoreAML.freeOf [] (.and C _) at hk
      simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
      rcases hk with hk | hk | hk | hk
      · exact freeOf_rule_parts hy.1 hr (Or.inl hk)
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inl hk))
      · exfalso
        obtain ⟨φ, hφ, hk⟩ := mem_freeOf_anyOfC hk
        obtain ⟨r', hr', -, rfl⟩ := hcomp φ hφ
        obtain ⟨hlhs', hreqs', -⟩ := rule_ctx hy.1 hr'
        exact freeOf_applies hlhs' (fun t ht => varOccs_lt t (hreqs' t ht)) (htop _ hr').1 (hb _ hr') hk
      · exact freeOf_rule_parts hy.1 hr (Or.inr (Or.inr hk))
    · have h := lhs_req_hold3 (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hr hσ hmatch hreq hag
      show (KoreAML.tr ⟨tbl, []⟩ (.and C _)).interpret I e' _
      rw [tr_and4, KoreAML.interp_sAnd, KoreAML.interp_sAnd, KoreAML.interp_sAnd]
      refine ⟨h.1, h.2, ?_, ceil_rhs_at hI hrhsR (elemOf_top hI x tbl e')⟩
      rw [KoreAML.tr, KoreAML.interp_sNot]
      refine ⟨anyOfC_empty hD (by
        show (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort))).isFreeEvar KoreAML.topVar = false
        rw [trSort_srt]; rfl) comps (fun φ hφ => ?_), ?_⟩
      · obtain ⟨r', hr', hp, rfl⟩ := hcomp φ hφ
        obtain ⟨hlhs', -, -⟩ := rule_ctx hy.1 hr'
        have hbinds' := Exec.binds_all (hb _ hr')
        refine applies_empty hI hs.1 hsc.trans hnn.1 hlhs' hbinds' (hs.2.1 r' hr') (htop _ hr').1 x.property
          (fun i hi => hkeys _ ?_) e' (notApplies_model3 (hpreTop := hpreTop) hI hnn hsc hs hy.1 hbc hr' (htop _ hr').1 (hprio r' hr' hp))
        rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOf]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (mem_varsOf_anyOfC hφ (varsOf_applies (htop _ hr').1 (hb _ hr') hi))))))
      · have hxs := elemOf_spec hI x.property e'
        show (KoreAML.inhOf (KoreAML.trSort tbl (KoreAML.srt (c.sortName topCellSort)))).interpret I e' _
        rw [trSort_srt]
        exact hxs.2

/-- **The second stage as a corollary of the third**: `Stage2` is `Stage3` with every called
function total (`stage3_of_stage2`). -/
theorem step_sound_stage2_of_stage3 (c : Semantics) [OvlOK c] (hy : Hyp c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hs : Stage2 c) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  have hpreTop := Semantics.preTop_of_okAll hy.1
  step_sound_stage3 c hy hb htop hbc (stage3_of_stage2 hs)

end Faithful

end KCore
