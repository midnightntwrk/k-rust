/-
  KCore, checked layer: the `functional` sentence of a function with a value at every argument list
  of its sorts, and of a sort predicate, holds at values in every model of `Γc`
  (`EntailsAtValuesΓc`), whatever the clauses' predicates.

  The denotation step `eval_den4_coreCl` reads a clause's predicate through `PreRead`
  (`HoldsShape.preReadAll_of_core`), so the predicate need not be `\top`. What the statement reads
  of the function itself is its lookup by its label, which holds of every member of `c.allFns`
  because the labels are distinct (`SortCtx.nodupFns`, `find?_label`), and, for a sort predicate,
  that its clauses have no existential variable and the right-side predicate `\top`, which its
  clauses' text gives (`Semantics.sortPreds_exs`, `Semantics.sortPreds_post`).
  - `LibEv.sortPreds_total_pre`: a sort predicate is `Total` in a semantics meeting `SortCtx`.
  - `LibEv.fnFun_evC_pre`: the sentence `funPat c fn.sig` of a function `fn` with a value at every
    argument list of its sorts, over the one sort variable `R`, translated, holds in every model of
    `Γc c` at every valuation sending its free element variables to values.
  - `LibEv.sortPredFun_evC_pre`: the same for a sort predicate, from its evaluation's values.
  - `LibEv.sortPredFun_evC_pre_withHooks`, `LibEv.fnFun_evC_pre_withHooks`: the same under every
    interpretation of the hooks, the latter for a function of the text declared total, under an
    interpretation where `FnHyp` holds, which gives it those values.
-/
import KcoreSpec.LibEvSortPred

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- A member of `c.allFns` is what `c.lookupFn` gives at its label, the labels being distinct. -/
theorem lookupFn_of_mem_pre {c : Semantics} (hsc : SortCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) :
    c.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn

/-- **The sort predicates are total** in a semantics meeting `SortCtx`: their clauses have no
`requires`, no existential variable, the right-side predicate `\top` and Bool literals as right-hand
sides, and each has a clause over a variable of sort K, which applies at every K. -/
theorem sortPreds_total_pre {c : Semantics} (hsc : SortCtx c) {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    Total c fn.label := by
  have hmem : fn ∈ c.allFns := List.mem_append_right _ hfn
  have hlook := lookupFn_of_mem_pre hsc hmem
  intro fn' hfn' vs hvs
  rw [hlook] at hfn'
  cases hfn'
  have hfacts : fn.args = [Srt.k] ∧ (∀ cl ∈ fn.clauses, cl.req = none ∧ ∃ s l, cl.rhs = .dv s l) ∧
      ∃ cl ∈ fn.clauses, cl.vars = [Srt.k] ∧ cl.pats = [.var 0] ∧ cl.req = none := by
    simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_filterMap, Option.map_eq_some_iff] at hfn
    rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool true), ens := none, prio := 50 },
        List.mem_singleton_self _, rfl, rfl, rfl⟩
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
    · refine ⟨rfl, fun cl hcl => ?_, { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 },
        by simp, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
  obtain ⟨hargs, hshape, cl₀, hcl₀, hv₀, hp₀, hr₀⟩ := hfacts
  rw [hargs] at hvs
  obtain ⟨w, rfl, hw⟩ := sortsOf_one hvs
  have hσ : c.WellSorted cl₀.vars [(0, w)] := by
    rw [hv₀]
    intro i s hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨w, lookup_cons_self _ _ _, hw⟩
    | succ i => simp at hi
  refine eval_defined hlook (fun cl hcl => ⟨Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩)
    (fun cl hcl => Semantics.heldAt_of_bindsRH (Semantics.sortPreds_binds hfn cl hcl))
    (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(hshape cl hcl).1] at ht; cases ht), true,
      Clause.holds_preTop (Semantics.sortPreds_pre hfn cl hcl) σ⟩)
    (fun cl hcl _ _ => by obtain ⟨_, s, l, h⟩ := hshape cl hcl; rw [h]; exact ⟨_, EvalTerm.dv⟩)
    ⟨cl₀, hcl₀, hr₀, [(0, w)], hσ.at _, by rw [hp₀]; exact .cons (.var (lookup_cons_self _ _ _)) .nil,
      (fun t ht => by rw [hr₀] at ht; cases ht), Clause.holds_preTop (Semantics.sortPreds_pre hfn cl₀ hcl₀) _⟩ (sortPreds_ens hfn)

/-- **The `functional` sentence of a function with a value at every argument list of its sorts
holds at values in every model of `Γc`, whatever the clauses' predicates.** For a semantics meeting
`coreOK`, whose functions bind no variable by `\exists`, and whose clauses' conditions are decided
where `needsWitness` holds: for a function `fn` of the semantics (a user's or a sort predicate) whose
evaluation has a value at every argument list of its argument sorts, the translation of an axiom
declaration whose pattern is `funPat c fn.sig`, over the one sort variable `R`, holds in every model
of `Γc c` at every valuation that sends the axiom's free element variables to values. A clause's
predicate is read in the model through `PreRead` (`HoldsShape.preReadAll_of_core`). -/
theorem fnFun_evC_pre {c : Semantics} (h : c.coreOK = true) (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {fn : Fn} (hfn : fn ∈ c.allFns)
    (htot : ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    (hr : predFunRegS c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  intro M _ I hIc e hat m
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  haveI hov : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨hok, hsr, -, -, hph, -, -, -, -⟩ := hypSound_of_core h
  have hokCl : c.sortedOKCl = true := Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx
  have hfa : c.faithCoreOK = true := (Semantics.coreOK_parts h).2.1
  have hsc : SortCtx c := sortCtx_of_allCl hokCl hsr (OvlOK.ovlCase hov)
  have hlook : c.lookupFn fn.label = some fn := lookupFn_of_mem_pre hsc hfn
  generalize hk : fn.sig = k at hr hp
  have hkn : k.name = fn.label := by rw [← hk]; rfl
  have hka : k.args = fn.args := by rw [← hk]; rfl
  have hkr : k.result = fn.result := by rw [← hk]; rfl
  have hr' := hr
  simp only [predFunRegS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hr'
  obtain ⟨⟨hsR, hvR⟩, hvars⟩ := hr'
  have hmemv : ∀ i, i < (funVars k).length → (funVars k).getD i ("", 0) ∈ funVars k := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨σ, hσ, hel⟩ := subst_of_atValuesS h hI hat (funVars k) hvR (fun i hi => by
    rw [hp]
    exact List.mem_of_elem_eq_true (hvars _ (hmemv i hi)).1.1)
  unfold KoreAML.trAxiom
  dsimp only
  have htbl : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = KoreAML.tableOf [KoreAML.Rv] (funPat c k) := by
    rw [hsv, hp]
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hel htbl ⊢
  rw [interpret_impl]
  intro hgd
  have hRt : KoreAML.VarKey.sortVar "R" ∈ t := by
    rw [htbl]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_singleton.mpr rfl))
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hlen := funVars_length k
  have hsrts : srts? c (funVars k) (argVars 0 k.args.length) = some k.args := by
    rw [srts_argVars c (funVars k) k.args.length 0 (by omega), List.drop_zero]
    exact congrArg some (funVarsFrom_sorts 0 k.args)
  obtain ⟨ws, hws⟩ := vals_argVars c hσ k.args.length 0 (by omega)
  -- under the binder
  let ex : M → Valuation M := fun x =>
    ⟨Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) x, e.evalSvar⟩
  have hexR : ∀ x, (ex x).evalEvar (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun x =>
    Function.update_noteq (ev_ne hRt (by unfold valKey; exact fun hh => by cases hh)) _ _
  have hexK : ∀ x i, i < (funVars k).length →
      (ex x).evalEvar (t.ev (vkey c (funVars k) i)) = e.evalEvar (t.ev (vkey c (funVars k) i)) := fun x i hi =>
    Function.update_noteq (ev_ne (by
        rw [htbl]
        exact List.mem_of_elem_eq_true (hvars _ (hmemv i hi)).1.2)
      (by
        unfold vkey valKey
        intro hh
        injection hh with hh _
        exact (hvars _ (hmemv i hi)).2 hh)) _ _
  have hag : ∀ x i v, i < (funVars k).length → σ.lookup i = some v →
      ∀ m, m = (ex x).evalEvar (t.ev (vkey c (funVars k) i)) ↔ (den c v).interpret I (ex x) m := by
    intro x i v hi hv m'
    obtain ⟨h1, h2⟩ := hel i v hi hv
    rw [(elemOf_spec hI h1 (ex x)).1 m', h2, hexK x i hi]
  have hDA := fun x => (den_vals (tbl := t) (e := ex x) h hI hσ (hag x) (argVars 0 k.args.length) hsrts).1 ws hws
  have hwss : c.sortsOf ws = some fn.args := hka ▸ (hDA default).1
  -- the function's value at the arguments, and the model's reading of its application
  obtain ⟨v, hev⟩ := htot ws hwss
  have hvs : c.sortOf v = some k.result := hkr ▸ Eval.sorted hsc hev hlook hwss rfl
  have hDV : ∀ x b, (KoreAML.tr ⟨t, []⟩ (kore c (funVars k) (funTerm k))).interpret I (ex x) b ↔
      (den c v).interpret I (ex x) b := fun x b => by
    have hden := eval_den4_coreCl hIc hokCl hsr hfa hph hw (HoldsShape.preReadAll_of_core h hIc) hev hlook hwss
      (ex x) b
    unfold KoreAML.den at hden
    rw [tr_symApp] at hden
    unfold funTerm
    rw [kore, tr_symApp, hkn, (hDA x).2 _ _ (fun _ => Iff.rfl) b]
    exact hden
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI hsR
  have hRv : ∀ x b, (KoreAML.trSort t KoreAML.R).interpret I (ex x) b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun x b => by rw [trSort_R, KoreAML.interp_evar, hexR]
  have hRv0 : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  rw [hp]
  unfold funPat
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sExists, KoreAML.interp_inhOf_of hRv0]
  constructor
  · rintro ⟨x, -, hx⟩
    rw [KoreAML.tr] at hx
    have hx' : (KoreAML.sEquals (KoreAML.trSort t (srtOf c k.result)) (KoreAML.trSort t KoreAML.R) _ _).interpret I
      (ex x) a := hx
    rw [KoreAML.interp_sEquals hD hc (hτ t (ex x)) (hRv x) hτsort hR] at hx'
    exact hx'.1
  · intro ha
    refine ⟨elemOf c I v, ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      show (KoreAML.inhOf (KoreAML.trSort t (srtOf c k.result))).interpret I (ex (elemOf c I v))
        (Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) (elemOf c I v) (t.ev (valKey (srtOf c k.result))))
      rw [Function.update_same, trSort_srtOf_twoT]
      exact (elemOf_spec hI hvs _).2
    · rw [KoreAML.tr]
      show (KoreAML.sEquals (KoreAML.trSort t (srtOf c k.result)) (KoreAML.trSort t KoreAML.R) _ _).interpret I
        (ex (elemOf c I v)) a
      rw [KoreAML.interp_sEquals hD hc (hτ t (ex (elemOf c I v))) (hRv (elemOf c I v)) hτsort hR]
      refine ⟨ha, fun b _ => ?_⟩
      rw [hDV (elemOf c I v) b, KoreAML.tr]
      show b = Function.update e.evalEvar (t.ev (valKey (srtOf c k.result))) (elemOf c I v)
        (t.ev (valKey (srtOf c k.result))) ↔ (den c v).interpret I (ex (elemOf c I v)) b
      rw [Function.update_same]
      exact ((elemOf_spec hI hvs _).1 b).symm

/-- **The `functional` sentence of a sort predicate holds at values in every model of `Γc`,
whatever the clauses' predicates.** For a semantics meeting `coreOK`, whose functions bind no
variable by `\exists`, and whose clauses' conditions are decided where `needsWitness` holds: the
translation of an axiom declaration whose pattern is `funPat c fn.sig` for a sort predicate `fn`,
over the one sort variable `R`, holds in every model of `Γc c` at every valuation that sends the
axiom's free element variables to values. Evaluation gives a sort predicate a value at every K
(`sortPreds_total_pre`). -/
theorem sortPredFun_evC_pre {c : Semantics} (h : c.coreOK = true) (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c)
    {fn : Fn} (hfn : fn ∈ c.sortPreds) (hr : predFunReg c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc c ad (KoreAML.trAxiom [] [] ad).pat := by
  haveI hov : OvlOK c := ovlOK_of_core h
  obtain ⟨hok, hsr, -, -, -, -, -, -, -⟩ := hypSound_of_core h
  have hsc : SortCtx c :=
    sortCtx_of_allCl (Semantics.sortedOKCl_of_sortedOK_noExs hok hnoEx) hsr (OvlOK.ovlCase hov)
  have hmem : fn ∈ c.allFns := List.mem_append_right _ hfn
  exact fnFun_evC_pre h hnoEx hw hmem
    (fun vs hvs => sortPreds_total_pre hsc hfn fn (lookupFn_of_mem_pre hsc hmem) vs hvs)
    (predFunRegS_of_reg hr) ad hp hsv

/-! ## Under every interpretation of the hooks -/

/-- **`sortPredFun_evC_pre` under every interpretation of the hooks**, from the facts of `c`: the
sort predicates, their sentences and the conditions it reads do not read the interpretation. -/
theorem sortPredFun_evC_pre_withHooks {c : Semantics} (H : HookParams) (h : c.coreOK = true)
    (hnoEx : c.FnsNoExs)
    (hw : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness (c.withHooks H) = true →
      cl.CondDecided (c.withHooks H))
    {fn : Fn} (hfn : fn ∈ c.sortPreds) (hr : predFunReg c fn.sig = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  sortPredFun_evC_pre (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans h) hnoEx hw hfn
    ((predFunReg_withHooksSP c H _).trans hr) ad (hp.trans (funPat_withHooksSP c H _).symm) hsv

/-- **The `functional` sentence of a function of `c` declared total holds at values in every model
of `Γc`, under every interpretation of the hooks where `FnHyp` holds, whatever the clauses'
predicates**: `FnHyp` gives the function a value at every argument list of its sorts and decides
the clauses' conditions where `needsWitness` holds, which `fnFun_evC_pre` reads. -/
theorem fnFun_evC_pre_withHooks {c : Semantics} (H : HookParams) (h : c.coreOK = true)
    (hnoEx : c.FnsNoExs) (hf : FnHyp (c.withHooks H))
    {fn : Fn} (hfn : fn ∈ c.fns) (ht : fn.total = true) (hr : predFunRegS c fn.sig = true)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = funPat c fn.sig) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValuesΓc (c.withHooks H) ad (KoreAML.trAxiom [] [] ad).pat :=
  fnFun_evC_pre (c := c.withHooks H) ((Semantics.coreOK_withHooks c H).trans h) hnoEx hf.2.2.2.2.1.2
    (List.mem_append_left (c.withHooks H).sortPreds hfn) (hf.2.1 fn hfn ht)
    ((predFunRegS_withHooksSP c H _).trans hr) ad (hp.trans (funPat_withHooksSP c H _).symm) hsv

end LibEv

end KCore
