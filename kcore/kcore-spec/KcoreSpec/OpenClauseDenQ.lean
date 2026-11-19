/-
  KCore. L3 at the fourth stage for clauses with existential variables: `eval_den4ClPre`'s block
  (OpenClauseDen.lean) with the facts every clause has asked of each clause (`ClauseOpenFactsQ`:
  `ClauseOpenFactsP` without `cl.exs = []`, with `cl.post = .top` asked only of a clause without
  existential variables), and the reading of a clause with existential variables asked of the model
  for that clause (`ClauseExRead`, `hexR`), as `hpreR` asks the reading of a premise's predicate.

  `Eval.clauseEx` is read at its match σ, which is well sorted on all the clause's variables;
  `Eval.exNone` at the instance σ₀ its premises give, which is σ on the variables of the left side,
  so its `requires` and its predicate, evaluated at σ, are read at σ₀ through the variables they
  read (`evalTerm_den4ClQOcc`, `HoldsReadT.congr_NIR`). Each instance's reading is the block's
  (`instIs_den4ClQ`), so `ClauseExRead` asks nothing of the evaluation.
-/
import KcoreSpec.OpenClauseDen
import KcoreSpec.OpenCompete
import KcoreSpec.HoldsCongr

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-- What the evaluation lemmas read of every clause of a function: its patterns have the argument
sorts, its premise's predicate is well sorted, its right side's predicate is `\top` where it has no
existential variable, each variable occurs in it, its `requires` and `ensures` are Bools and its
right side has the result sort, over the signatures `L`. -/
def ClauseOpenFactsQ (c : Semantics) (fn : Fn) (L : List CtorSig) (cl : Clause) : Prop :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ c.condOK cl.vars cl.pre = true ∧
    (cl.exs = [] → cl.post = .top) ∧
    (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
      (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) ∧
    (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
    sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
    (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool)

/-- `ClauseOpenFactsP` gives `ClauseOpenFactsQ`. -/
theorem ClauseOpenFactsP.toQ {c : Semantics} {fn : Fn} {L : List CtorSig} {cl : Clause}
    (h : ClauseOpenFactsP c fn L cl) : ClauseOpenFactsQ c fn L cl := by
  obtain ⟨h1, h2, hpost, h4, h5, h6, h7, -⟩ := h
  exact ⟨h1, h2, fun _ => hpost, h4, h5, h6, h7⟩

/-- **A clause with existential variables that decides, read in the model**: at a match σ₀ of the
clause at arguments of its function's sorts (σ₀ well sorted on all its variables), where its
`requires` and its premise's predicate are read at σ₀ (`ihreq`, `ihpre`), the clauses of a smaller
priority it negates fail, every instance that is σ₀ off the existential variables the left side
does not hold is decided and gives `r` or nothing with the readings of the terms it evaluates, and
where `r` is `some v` the instance at σ₀ gives `v`, the function applied to the arguments'
elements is what `r` denotes. `eval_den_exRead`'s statement after the clause's facts. -/
def ClauseExRead (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (fn : Fn) (cl : Clause) :
    Prop :=
  ∀ {f : Sym} {ws : List GroundTerm} {σ₀ : Subst} {r : Option GroundTerm},
    c.lookupFn f = some fn → c.sortsOf ws = some fn.args →
    c.WellSorted cl.vars σ₀ → PatVals c σ₀ cl.pats ws →
    (∀ t, cl.req = some t → ∀ (tbl : VarTable) (e' : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ₀ e' →
      ∀ m', (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e' m' ↔
        (den c (bool true)).interpret I e' m') →
    (cl.pre.isTop = false → ∀ (tbl : VarTable) (e : Valuation M) (σr m0 : M),
      Agrees c I tbl (canonVars c cl.vars) σ₀ e →
      (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre), k ∈ tbl) →
      VarKey.sortVar "R" ∈ tbl → (∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) → IsSort I σr →
      Inh I σr m0 → (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c cl.vars) KoreAML.R cl.pre)).interpret I e m0) →
    (∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio →
      c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
      (∀ t, cl'.req = some t → ∀ i ∈ varOccs t, i < cl'.vars.length) ∧
      ExclEmptyCl c I fn cl' ∧ Fails c ws cl' ∧ ModelFailsCl c I cl' ws) →
    (∀ σ', AgreeOff cl.exsFree σ₀ σ' → c.WellSorted cl.vars σ' → HoldsShape.InstIsRead c I σ' cl r) →
    (∀ v, r = some v → EvalTerm c σ₀ cl.rhs (some v) ∧ HoldsShape.TermAt c I σ₀ cl.rhs (some v) ∧
      (∀ t, cl.ens = some t → HoldsShape.TermAt c I σ₀ t (some (bool true))) ∧
      HoldsShape.HoldsRead c I cl.vars.length σ₀ cl.post true) →
    ∀ (e : Valuation M) (m : M),
      (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m

/-- Where no clause has existential variables, `ClauseExRead` is asked of none. -/
theorem clauseExRead_of_noExs {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs = []) :
    ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ClauseExRead c I fn cl :=
  fun fn hfn cl hcl hne => absurd (h fn hfn cl hcl) hne

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) (hnn : NamesNumbered c) (hsc : SortCtx c) [OvlOK c]
  (hph : patHooksApart c = true)
  (hcls : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∃ L, HeadsOK c L ∧ ClauseOpenFactsQ c fn L cl)
  (hneg : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ClauseNeg c fn cl → ExclEmptyCl c I fn cl)
  (hpreR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre ≠ .top → HoldsShape.PreRead c I cl)
  (hexR : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ClauseExRead c I fn cl)

include hI hnn hsc hph hcls hneg hpreR hexR

omit hpreR hexR in
/-- A clause of a smaller priority, failing, with what `clause_den4Cl` reads of it. -/
theorem lowClQ {fn : Fn} {cl cl' : Clause} {ws : List GroundTerm} (hmem : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses)
    (hcl' : cl' ∈ fn.clauses) (hlt : cl'.prio < cl.prio) (hf : Fails c ws cl') (hm : ModelFailsCl c I cl' ws) :
    c.condOK cl'.vars cl'.pre = true ∧ sortsOfTerms c.patCtxAll cl'.vars cl'.pats = some fn.args ∧
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
  theorem eval_den4ClQ : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq hpreH hprio hexs hrhs hens _,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, hpats, hpre, hpostE, hocc, hreqs, hrhss, henss⟩ := hcls fn' hmem cl hcl
      have hpost := hpostE hexs
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      exact clause_den4Cl hI hnn hsc hph hfn hcl hws hσ' hmatch hpats hpre hpost hexs hocc hreqs hrhss
        henss hr (fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den4ClQOcc hrhs hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) hrhss m')
          (fun t ht m' => evalTerm_den4ClQOcc (hens t ht) hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4ClQOcc (hreq t ht) hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) (hreqs t ht) m')
        (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
          have hR := hpreR fn' hmem cl hcl (HoldsShape.ne_top_of_isTop_false hpt)
          (preRead_agreesCl hR hpre (holdsRead_den4ClQ hpreH) hσ' hag hkp hRk hRv hσr hm0).mpr rfl)
        (fun cl' hcl'' hna'' hlt => lowClQ hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4ClQ (hprio cl' hcl'' hna'' hlt) hmem hcl'')) e m
    | _, _, _, .ensFails (fn := fn') (cl := cl) (σ := σ') (t := t) hfn' hcl hσ' hmatch hreq hpreH hprio hexs ht he hw,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, hpats, hpre, hpostE, hocc, hreqs, hrhss, henss⟩ := hcls fn' hmem cl hcl
      have hpost := hpostE hexs
      exact clause_den4Cl hI hnn hsc hph hfn hcl hws hσ' hmatch hpats hpre hpost hexs hocc hreqs hrhss
        henss (fun v hv => by cases hv) (fun tbl e' hag => right_empty hI hnn hmem ht hw
          (fun v hv => EvalTerm.sorted hsc he hL hσ' (henss t ht) hv)
          (fun m' => evalTerm_den4ClQOcc he hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) (henss t ht) m'))
        (fun t ht tbl e' hag m' => evalTerm_den4ClQOcc (hreq t ht) hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) (hreqs t ht) m')
        (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
          have hR := hpreR fn' hmem cl hcl (HoldsShape.ne_top_of_isTop_false hpt)
          (preRead_agreesCl hR hpre (holdsRead_den4ClQ hpreH) hσ' hag hkp hRk hRv hσr hm0).mpr rfl)
        (fun cl' hcl'' hna'' hlt => lowClQ hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4ClQ (hprio cl' hcl'' hna'' hlt) hmem hcl'')) e m
    | _, ws, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
    | _, _, _, .clauseEx (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq hpreH hprio hne hrhs hens hpost hall,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, -, hpre, -, -, hreqs, -, -⟩ := hcls fn' hmem cl hcl
      exact hexR fn' hmem cl hcl hne hfn hws hσ' hmatch
        (fun t ht tbl e' hag m' => evalTerm_den4ClQOcc (hreq t ht) hL (hσ'.at _) (canonVars_length c cl.vars) (Agrees.on hag _) (hreqs t ht) m')
        (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
          have hR := hpreR fn' hmem cl hcl (HoldsShape.ne_top_of_isTop_false hpt)
          (preRead_agreesCl hR hpre (holdsRead_den4ClQ hpreH) hσ' hag hkp hRk hRv hσr hm0).mpr rfl)
        (fun cl' hcl'' hna'' hlt => lowClQ hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4ClQ (hprio cl' hcl'' hna'' hlt) hmem hcl''))
        (fun σ'' ha hw => instIs_den4ClQ (hall σ'' ha hw))
        (fun v' hv' => by
          cases hv'
          exact ⟨hrhs, HoldsShape.termAt_of_all hI
              fun hσ hag ht m => evalTerm_den4ClQOcc hrhs fns_headsOK hσ (canonVars_length c _) hag ht m,
            fun t ht => HoldsShape.termAt_of_all hI
              fun hσ hag ht' m => evalTerm_den4ClQOcc (hens t ht) fns_headsOK hσ (canonVars_length c _) hag ht' m,
            holdsRead_den4ClQ hpost⟩) e m
    | _, _, _, .exNone (fn := fn') (cl := cl) (σ := σ) hfn' hcl hne _ hmatch hreq hpreH hprio hsome hall,
        fn, hfn, hws, e, m => by
      rw [hfn] at hfn'; cases hfn'
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨L, hL, -, hpre, -, -, hreqs, -, -⟩ := hcls fn' hmem cl hcl
      obtain ⟨σ₀, hag0, hσ₀⟩ := hsome
      have hl : ∀ i ∈ cl.leftVars, σ₀.lookup i = σ.lookup i := fun i hi =>
        hag0 i (by simp [Clause.exsFree, hi])
      exact hexR fn' hmem cl hcl hne hfn hws hσ₀
        (PatVals.congr_lookup hmatch fun j hj => hl j (List.mem_append_left _ hj))
        (fun t ht tbl e' hag m' => evalTerm_den4ClQOcc (hreq t ht) hL
          (fun i hi s hs => by
            obtain ⟨v, hv, hsv⟩ := hσ₀ i s hs
            exact ⟨v, by rw [← hl i (Clause.req_leftVars ht i hi)]; exact hv, hsv⟩)
          (canonVars_length c cl.vars)
          (fun i hi v hil hv => hag i v hil (by rw [hl i (Clause.req_leftVars ht i hi)]; exact hv))
          (hreqs t ht) m')
        (fun hpt tbl e' σr m0 hag hkp hRk hRv hσr hm0 =>
          have hR := hpreR fn' hmem cl hcl (HoldsShape.ne_top_of_isTop_false hpt)
          (preRead_agreesCl hR hpre ((holdsRead_den4ClQ hpreH).congr_NIR
            (fun hT ha => hT.congr_occ fun i hi => (ha i hi).symm) σ₀
            fun i hi => (hl i (Clause.pre_leftVarsRH i hi)).symm) hσ₀ hag hkp hRk hRv hσr hm0).mpr rfl)
        (fun cl' hcl'' hna'' hlt => lowClQ hI hnn hsc hph hcls hneg hmem hcl hcl'' hlt (hprio cl' hcl'' hna'' hlt)
          (fails_den4ClQ (hprio cl' hcl'' hna'' hlt) hmem hcl''))
        (fun σ'' ha hw => instIs_den4ClQ (hall σ'' (hag0.trans ha) hw))
        (fun v' hv' => by cases hv') e m
  termination_by structural _ _ _ h => h
  /-- A clause that fails at arguments of its function's sorts fails in the model: its `requires`
  denotes a result other than `true`, or its predicate has the truth value `false` with its terms'
  readings. -/
  theorem fails_den4ClQ : ∀ {ws : List GroundTerm} {cl : Clause}, Fails c ws cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ModelFailsCl c I cl ws
    | _, _, .intro h, fn, hfn, hcl => fun vars hlen hagl σ hσ hpv =>
      reqFails_den4ClQ (h σ (fun i hi s hs => hσ i s (by rw [hagl i hi]; exact hs)) hpv) hfn hcl hlen hagl hσ
  termination_by structural _ _ h => h
  theorem reqFails_den4ClQ : ∀ {σ : Subst} {cl : Clause}, ReqFails c σ cl →
      ∀ {fn : Fn}, fn ∈ c.allFns → cl ∈ fn.clauses → ∀ {vars : List Srt}, vars.length = cl.vars.length →
      (∀ i ∈ cl.leftVars, vars[i]? = cl.vars[i]?) → c.WellSorted vars σ →
      (∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ e →
        ∃ t r, cl.req = some t ∧ r ≠ some (bool true) ∧ (∀ v, r = some v → c.sortOf v = some Srt.bool) ∧
          ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔ Res c I e r m) ∨
      (cl.pre ≠ .top ∧ HoldsShape.HoldsRead c I cl.vars.length σ cl.pre false)
    | _, cl, .pre h, fn, hfn, hcl, vars, hlen, hagl, hσ =>
      (Classical.em (cl.pre = .top)).elim (fun hne => absurd (hne ▸ h).top_eq (by simp))
        fun hne => Or.inr ⟨hne, holdsRead_den4ClQ h⟩
    | _, cl, .intro (t := t) (r := r) ht he hr, fn, hfn, hcl, vars, hlen, hagl, hσ => Or.inl fun tbl e hag => by
      obtain ⟨L, hL, -, -, -, -, hreqs, -⟩ := hcls fn hfn cl hcl
      have htS : sortOfTerm (c.rhsCtx L) vars t = some Srt.bool := by
        rw [sortOfTerm_congr t fun i hi => hagl i (Clause.req_leftVars ht i hi)]; exact hreqs t ht
      exact ⟨t, r, ht, hr, fun v hv => EvalTerm.sorted hsc he hL hσ htS hv,
        evalTerm_den4ClQOcc he hL (hσ.at _) (by rw [canonVars_length, hlen]) (Agrees.on hag _) htS⟩
  termination_by structural _ _ h => h
  /-- **The Holds lemma along an evaluation.** A truth value `Holds` gives a condition is read in
  the model (`HoldsAt`): each term the derivation evaluates is read by `evalTerm_den4ClQOcc` at that
  evaluation, and each constructor of `Holds` by its lemma (HoldsNode.lean). Asked of the model:
  the constructors' facts, and the binders' where the condition holds a binder. -/
  theorem holds_den4ClQ : ∀ {n : Nat} {σ : Subst} {p : Cond} {b : Bool}, Holds c n σ p b →
      HoldsShape.NodeFacts c I → (HoldsShape.hasBinder p = true → HoldsShape.BinderFacts c I) →
      HoldsShape.HoldsAt c I n σ p b
    | _, _, _, _, .top, F, _ => HoldsShape.holdsAt_top F
    | _, _, _, _, .bot, F, _ => HoldsShape.holdsAt_bot F
    | _, _, _, _, .not h, F, G => HoldsShape.holdsAt_not (holds_den4ClQ h F G)
    | _, _, _, _, .and h h', F, G => HoldsShape.holdsAt_and
        (holds_den4ClQ h F fun hp => G (by rw [HoldsShape.hasBinder, hp, Bool.true_or]))
        (holds_den4ClQ h' F fun hq => G (by rw [HoldsShape.hasBinder, hq, Bool.or_true]))
    | _, _, _, _, .or h h', F, G => HoldsShape.holdsAt_or
        (holds_den4ClQ h F fun hp => G (by rw [HoldsShape.hasBinder, hp, Bool.true_or]))
        (holds_den4ClQ h' F fun hq => G (by rw [HoldsShape.hasBinder, hq, Bool.or_true]))
    | _, _, _, _, .implies h h', F, G => HoldsShape.holdsAt_implies
        (holds_den4ClQ h F fun hp => G (by rw [HoldsShape.hasBinder, hp, Bool.true_or]))
        (holds_den4ClQ h' F fun hq => G (by rw [HoldsShape.hasBinder, hq, Bool.or_true]))
    | _, _, _, _, .ceil h, F, _ => HoldsShape.holdsAt_ceil F h (HoldsShape.termAt_of_all hI
        fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .equals h h', F, _ => HoldsShape.holdsAt_equals F
        h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        h' (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h' fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .mem h h', F, _ => HoldsShape.holdsAt_mem F
        h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        h' (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h' fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .exNone h, F, G => HoldsShape.holdsAt_exMatch F (G rfl) h (HoldsShape.termAt_of_all hI
        fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m) (Or.inl ⟨rfl, rfl⟩)
    | _, _, _, _, .exSome g h hb hr, F, G => HoldsShape.holdsAt_exMatch F (G rfl) h (HoldsShape.termAt_of_all hI
        fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        (Or.inr ⟨_, g, rfl, fun σ' hx hpv => holds_den4ClQ (hb σ' hx hpv) F fun _ => G rfl, hr⟩)
    | _, _, _, _, .ex g hb hr, F, G => HoldsShape.holdsAt_ex F (G rfl) g
        (fun σ' hx => holds_den4ClQ (hb σ' hx) F fun _ => G rfl) hr
    | _, _, _, _, .all g hb hr, F, G => HoldsShape.holdsAt_all F (G rfl) g
        (fun σ' hx => holds_den4ClQ (hb σ' hx) F fun _ => G rfl) hr
  termination_by structural _ _ _ _ h => h
  /-- **A truth value with the readings of its terms.** A truth value `Holds` gives a condition
  comes with the reading in the model of each term the derivation evaluates (`HoldsRead`), which
  `evalTerm_den4ClQOcc` gives at that evaluation. Nothing is asked of the model. -/
  theorem holdsRead_den4ClQ : ∀ {n : Nat} {σ : Subst} {p : Cond} {b : Bool}, Holds c n σ p b →
      HoldsShape.HoldsRead c I n σ p b
    | _, _, _, _, .top => .top
    | _, _, _, _, .bot => .bot
    | _, _, _, _, .not h => .not (holdsRead_den4ClQ h)
    | _, _, _, _, .and h h' => .and (holdsRead_den4ClQ h) (holdsRead_den4ClQ h')
    | _, _, _, _, .or h h' => .or (holdsRead_den4ClQ h) (holdsRead_den4ClQ h')
    | _, _, _, _, .implies h h' => .implies (holdsRead_den4ClQ h) (holdsRead_den4ClQ h')
    | _, _, _, _, .ceil h => .ceil h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .equals h h' => .equals
        h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        h' (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h' fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .mem h h' => .mem
        h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        h' (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h' fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .exNone h => .exNone h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
    | _, _, _, _, .exSome g h hb hr => .exSome g h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
        (fun σ' hx hpv => holdsRead_den4ClQ (hb σ' hx hpv)) hr
    | _, _, _, _, .ex g hb hr => .ex g (fun σ' hx => holdsRead_den4ClQ (hb σ' hx)) hr
    | _, _, _, _, .all g hb hr => .all g (fun σ' hx => holdsRead_den4ClQ (hb σ' hx)) hr
  termination_by structural _ _ _ _ h => h
  /-- An instance of a clause's right side that gives nothing, with the readings of the terms it
  evaluates. -/
  theorem instFails_den4ClQ : ∀ {σ : Subst} {cl : Clause}, InstFails c σ cl → HoldsShape.InstFailsRead c I σ cl
    | _, _, .ens ht he hw => .ens ht he (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc he fns_headsOK hσ (canonVars_length c _) hag ht m) hw
    | _, _, .post h => .post (holdsRead_den4ClQ h)
    | _, _, .rhs h => .rhs h (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc h fns_headsOK hσ (canonVars_length c _) hag ht m)
  termination_by structural _ _ h => h
  /-- **A decided instance of a clause's right side, with the readings of the terms it evaluates**
  (`InstIsRead`): its right-hand side's and its `ensures`' by `evalTerm_den4ClQOcc`, its predicate's
  by `holdsRead_den4ClQ`. -/
  theorem instIs_den4ClQ : ∀ {σ : Subst} {cl : Clause} {r : Option GroundTerm}, InstIs c σ cl r →
      HoldsShape.InstIsRead c I σ cl r
    | _, _, _, .fails hp h => .fails (holdsRead_den4ClQ hp) (instFails_den4ClQ h)
    | _, _, _, .gives hrhs hens hpost => .gives hrhs (HoldsShape.termAt_of_all hI
          fun hσ hag ht m => evalTerm_den4ClQOcc hrhs fns_headsOK hσ (canonVars_length c _) hag ht m)
        (fun t ht => ⟨hens t ht, HoldsShape.termAt_of_all hI
          fun hσ hag ht' m => evalTerm_den4ClQOcc (hens t ht) fns_headsOK hσ (canonVars_length c _) hag ht' m⟩)
        (holdsRead_den4ClQ hpost)
  termination_by structural _ _ _ h => h
  /-- **L3, terms, fourth stage.** A well-sorted right-hand side or `requires`, at a valuation that
  agrees with σ on the term's variables, σ well sorted on them, translates to what its result under
  σ denotes: the value's element, or nothing where it is undefined. -/
  theorem evalTerm_den4ClQOcc : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt},
      HeadsOK c L → c.WellSortedAt vars (varOccs t) σ → vs.length = vars.length →
      AgreesOn c I tbl vs (varOccs t) σ e →
      sortOfTerm (c.rhsCtx L) vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m
    | _, _, _, .var (i := i), L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      have hmem : i ∈ varOccs (.var i) := by rw [varOccs]; exact List.mem_singleton_self i
      obtain ⟨v, hv, -⟩ := hσ i hmem s hi
      rw [hv, tr_var]
      exact hag i hmem v hlt hv m
    | _, _, _, .dv (s := s') (lit := lit), _, _, vs, tbl, e, _, _, _, _, _, _, m => by
      show _ ↔ (den c (.dv s' lit)).interpret I e m
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, _, .inj (a := a) (b := b) (t := t) (r := r) h', L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      rw [varOccs] at hσ hag
      have ih := evalTerm_den4ClQOcc h' hL hσ hvs hag ht'
      rw [Term.kore, KoreAML.tr_injP]
      cases r with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact injApp_empty (fun m h => ((ih m).mp h)) m
      | some w =>
        have hw := EvalTerm.sorted_at hsc h' hL hσ ht' rfl
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
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
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
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hund hall]
        simp only [Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hv := hh ws hall
        have hws := EvalTerms.sorted_at hsc hts hL hσ hargs hall
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
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hr, hall]
        simp only [Option.bind_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted_at hsc hts hL hσ hargs hall
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
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted_at hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den4ClQ hf hlook hws e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovlFn (f := f) (rs := rs) (vs := ws) (o := o) (kg := kg) (r := r) hk ho hts hvs' hlo hcov hf,
        L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [hlo] at hlo'; cases hlo'
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      have hws := EvalTerms.sorted_at hsc hts hL hσ hargs hvs'
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ :=
        OvlLaws.fnCover_fn_ovlF ((inferInstance : OvlOK c).hyp hsc.trans).fnFacts hlo hws hcov
      have hname : kg.name = fn.label := by rw [hsig]
      have hres : kg.result = fn.result := by rw [hsig]
      have hgd := eval_den4ClQ hf hlook hus e
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := covDen_of hI hsc.trans hlo hws hcov (namesNumbered_cover hnn hlo hcov)
        (fun v hv => by rw [hres]; exact Eval.sorted hsc hf hlook hus hv) e hgd m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts hnf, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [varOccs] at hσ hag
      have ih := evalTerms_den4ClQOcc hts hL hσ hvs hag hargs
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted_at hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := (normDen_of hI hsc.trans).1 hlo hws (hnf ws hall) e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den4ClQOcc : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt},
      HeadsOK c L → c.WellSortedAt vars (varOccsList ts) σ → vs.length = vars.length →
      AgreesOn c I tbl vs (varOccsList ts) σ e →
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
      rw [varOccsList] at hσ hag
      have ih1 := evalTerm_den4ClQOcc h hL (hσ.mono fun i hi => List.mem_append_left _ hi) hvs
        (hag.mono fun i hi => List.mem_append_left _ hi) h1
      have ih2 := evalTerms_den4ClQOcc hs hL (hσ.mono fun i hi => List.mem_append_right _ hi) hvs
        (hag.mono fun i hi => List.mem_append_right _ hi) h2
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

/-- **L3, terms, fourth stage** (`evalTerm_den4ClQOcc`), at a valuation that agrees with a σ
well sorted on every variable in scope. -/
theorem evalTerm_den4ClQ {σ : Subst} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r)
    {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt}
    (hL : HeadsOK c L) (hσ : c.WellSorted vars σ) (hvs : vs.length = vars.length) (hag : Agrees c I tbl vs σ e)
    (ht : sortOfTerm (c.rhsCtx L) vars t = some s) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m :=
  evalTerm_den4ClQOcc hI hnn hsc hph hcls hneg hpreR hexR h hL (hσ.at _) hvs (Agrees.on hag _) ht

theorem evalTerms_den4ClQ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)} (h : EvalTerms c σ ts rs)
    {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt}
    (hL : HeadsOK c L) (hσ : c.WellSorted vars σ) (hvs : vs.length = vars.length) (hag : Agrees c I tbl vs σ e)
    (hts : sortsOfTerms (c.rhsCtx L) vars ts = some ss) :
    (∀ ws, allSome rs = some ws → ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
      ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
        (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
    (allSome rs = none → ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m) :=
  evalTerms_den4ClQOcc hI hnn hsc hph hcls hneg hpreR hexR h hL (hσ.at _) hvs (Agrees.on hag _) hts

end
end Faithful

end KCore
