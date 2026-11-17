/-
  KCore. L3 at the fourth stage for a semantics whose clauses' patterns need not bind every
  variable: `eval_den4`'s block with the clause facts asked of each clause (`ClauseOpenFacts`, which
  `clauseSortedOpen` and `clausePlainOpen` give, and `sortedOK` gives today:
  `clauseOpenFacts_of_sortedOK`) in place of `sortedOK`, and each negated clause's exclusion empty
  where it fails (`ExclEmptyCl`). A clause that fails fails in the model at the substitutions of
  values on its patterns and conditions (`fails_den4Cl`, `ModelFailsCl`), which is what
  `ExclEmptyCl` reads. `eval_den4`, and `eval_den2`, `eval_den3` (their scopes inside), for such
  semantics.
-/
import KcoreSpec.OpenClauseEval

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-- What the evaluation lemmas read of a clause of a function: its patterns have the argument sorts,
its predicates are `\top`, each variable occurs in it, its `requires` and `ensures` are Bools and its
right side has the result sort, over the signatures `L`; and it has no existential variable. -/
def ClauseOpenFacts (c : Semantics) (fn : Fn) (L : List CtorSig) (cl : Clause) : Prop :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ cl.pre = .top ∧ cl.post = .top ∧
    (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) ∧
    (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
    sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
    (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧ cl.exs = []

/-- `clauseSortedOpen` and `clausePlainOpen` give `ClauseOpenFacts`. -/
theorem clauseOpenFacts_of {c : Semantics} {fn : Fn} {L : List CtorSig} {cl : Clause}
    (hs : c.clauseSortedOpen fn L cl = true) (hp : c.clausePlainOpen cl = true) : ClauseOpenFacts c fn L cl := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Semantics.clauseSortedOpen_parts hs
  obtain ⟨hexs, hpre, hpost, -⟩ := Semantics.clausePlainOpen_parts hp
  exact ⟨h1, hpre, hpost, h2, h3, h4, h5, hexs⟩

/-- The generated sort predicates' clauses have `\top` predicates. -/
theorem sortPreds_topCl {c : Semantics} {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    ∀ cl ∈ fn.clauses, cl.pre = .top ∧ cl.post = .top := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl; exact ⟨rfl, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **`sortedOK` gives `ClauseOpenFacts` of every clause of every function** (the user's and the sort
predicates'). -/
theorem clauseOpenFacts_of_sortedOK {c : Semantics} (hok : c.sortedOK = true) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFacts c fn L cl := by
  intro fn hfn cl hcl
  obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxOccE hok hfn hcl
  have hpp : cl.pre = .top ∧ cl.post = .top := by
    rcases List.mem_append.mp hfn with hu | hp
    · exact Semantics.sortedOK_clause hok hu hcl
    · exact sortPreds_topCl hp cl hcl
  exact ⟨L, hL, hpats, hpp.1, hpp.2, hbinds, hreqs, hrhss, henss, clause_exsNil hok hfn hcl⟩

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
  (hph : patHooksApart c = true)
  (hcls : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFacts c fn L cl)
  (hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl)
include hI hnn hsc hph hcls hneg

/-- A clause of a smaller priority, failing, with what `clause_den4Cl` reads of it. -/
theorem lowCl {fn : Fn} {cl cl' : Clause} {ws : List GroundTerm} (hmem : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses)
    (hcl' : cl' ∈ fn.clauses) (hlt : cl'.prio < cl.prio) (hf : Fails c ws cl') (hm : ModelFailsCl c I cl' ws) :
    cl'.pre = .top ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws := by
  obtain ⟨L, -, hpats, hpre, -, -, hreqs, -⟩ := hcls fn hmem cl' hcl'
  exact ⟨hpre, hpats, fun t ht => varOccs_lt t (hreqs t ht), hneg fn hmem cl' hcl' ⟨cl, hcl, hlt⟩, hf, hm⟩

mutual
  /-- **L3, functions, fourth stage.** A function of the semantics, at arguments of its sorts,
  applied to their elements, is what its result denotes, defined or not: through its clause's
  equation (whose right-hand side may denote nothing), the clauses of a smaller priority it negates
  failing at the arguments; or, where every clause fails, through its rest's graph
  (`rest_den`). -/
  theorem eval_den4Cl : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq _ hprio hrhs hens,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, hpats, hpre, hpost, hocc, hreqs, hrhss, henss, hexs⟩ := hcls fn' hmem cl hcl
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      exact clause_den4Cl hI hnn hsc hph hfn hcl hws hσ' hmatch hpats hpre hpost hexs hocc hreqs hrhss
        henss hr (fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den4Cl hrhs hL hσ' (canonVars_length c cl.vars) hag hrhss m')
          (fun t ht m' => evalTerm_den4Cl (hens t ht) hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4Cl (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => lowCl hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4Cl (hprio cl' hcl'' hna'' hlt) hmem hcl'')) e m
    | _, _, _, .ensFails (fn := fn') (cl := cl) (σ := σ') (t := t) hfn' hcl hσ' hmatch hreq _ hprio ht he hw,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, hpats, hpre, hpost, hocc, hreqs, hrhss, henss, hexs⟩ := hcls fn' hmem cl hcl
      exact clause_den4Cl hI hnn hsc hph hfn hcl hws hσ' hmatch hpats hpre hpost hexs hocc hreqs hrhss
        henss (fun v hv => by cases hv) (fun tbl e' hag => right_empty hI hnn hmem ht hw
          (fun v hv => EvalTerm.sorted hsc he hL hσ' (henss t ht) hv)
          (fun m' => evalTerm_den4Cl he hL hσ' (canonVars_length c cl.vars) hag (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4Cl (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht) m')
        (fun cl' hcl'' hna'' hlt => lowCl hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4Cl (hprio cl' hcl'' hna'' hlt) hmem hcl'')) e m
    | _, ws, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
  termination_by structural _ _ _ h => h
  /-- A clause that fails at arguments of its function's sorts fails in the model. -/
  theorem fails_den4Cl : ∀ {ws : List GroundTerm} {cl : Clause}, Fails c ws cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ModelFailsCl c I cl ws
    | _, _, .intro h, fn, hfn, hcl => fun vars hlen hagl σ hσ hpv tbl e hag =>
      reqFails_den4Cl (h σ (fun i hi s hs => hσ i s (by rw [hagl i hi]; exact hs)) hpv) hfn hcl hlen hagl hσ tbl e hag
  termination_by structural _ _ h => h
  theorem reqFails_den4Cl : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ∀ {vars : List Srt}, vars.length = cl.vars.length →
      (∀ i ∈ cl.leftVars, vars[i]? = cl.vars[i]?) → c.WellSorted vars σ →
      ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
      ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
        ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m
    | _, cl, .pre h, fn, hfn, hcl, vars, hlen, hagl, hσ, tbl, e, hag => by
      obtain ⟨L, hL, -, hpre, -⟩ := hcls fn hfn cl hcl
      rw [hpre] at h; exact absurd h.top_eq (by simp)
    | _, cl, .intro (t := t) (r := r) ht he hr, fn, hfn, hcl, vars, hlen, hagl, hσ, tbl, e, hag => by
      obtain ⟨L, hL, -, -, -, -, hreqs, -⟩ := hcls fn hfn cl hcl
      have htS : sortOfTerm (c.rhsCtx L) vars t = some Srt.bool := by
        rw [sortOfTerm_congr t fun i hi => hagl i (Clause.req_leftVars ht i hi)]; exact hreqs t ht
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ htS hv,
        evalTerm_den4Cl he hL hσ (by rw [canonVars_length, hlen]) hag htS⟩
  termination_by structural _ _ h => h
  /-- **L3, terms, fourth stage.** A well-sorted right-hand side or `requires`, at a valuation that
  agrees with a well-sorted σ, translates to what its result under σ denotes: the value's element,
  or nothing where it is undefined. -/
  theorem evalTerm_den4Cl : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
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
      have ih := evalTerm_den4Cl h' hL hσ hvs hag ht'
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
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
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
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
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
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
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
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den4Cl hf hlook hws e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      have ih := evalTerms_den4Cl hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := normDen_of hI hsc.trans hlo hws e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den4Cl : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
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
      have ih1 := evalTerm_den4Cl h hL hσ hvs hag h1
      have ih2 := evalTerms_den4Cl hs hL hσ hvs hag h2
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

end Faithful

end KCore
