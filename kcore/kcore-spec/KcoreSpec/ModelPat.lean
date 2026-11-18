/-
  KCore. The model-side reading of patterns and premises, beside the reading of terms
  (ModelRead.lean).

  - A pattern of a left-hand side or a clause, under a valuation reading each variable as its
    value in σ, denotes exactly the values it denotes under σ (`tr_pat`, `PatVal`): a constructor
    builds its term, a map pattern symbol and a collection pattern symbol are interpreted as the
    hooks and parameters `PatVal` reads, an injection is `injNormal`, `p as X` is `p` and `X`.
  - Every well-sorted term under a well-sorted σ has a result (`evalTerm_total`) where every
    function of the definition has a result at arguments of its sorts (`FnTerminates`), a sort
    predicate having one because its clauses have no `requires`: either some σ matches one, or
    every σ fails it. The value model does not read it; it gives `FnSolves` (`fnSolves_of_total`)
    and is what completeness under `FnHyp` reads.
  - `⌈req = true⌉` holds exactly where `req` evaluates to `true` (`reqPat_iff`): the term denotes
    the values of its results (`tr_term`), and it has one result (`FnDet`,
    `EvalTerm.functional_of_fnDet`).
  - The reading of the top cell sort and of a competitor's sort predicates (`srtOf_top_den`,
    `top_isSort`); a configuration is in a rule's `applies` pattern exactly where the rule applies
    (`applies_iff_open`, OpenModel.lean).
-/
import KcoreSpec.ModelRead
import KcoreSpec.Terminates
import KcoreSpec.ModelConsFn

set_option autoImplicit false

namespace KCore

mutual
  /-- A term's sort reads the sorts of its own variables only. -/
  theorem sortOfTerm_congr {x : TermCtx} {vs vs' : List Srt} :
      ∀ (t : Term), (∀ i ∈ varOccs t, vs[i]? = vs'[i]?) → sortOfTerm x vs t = sortOfTerm x vs' t
    | .var i, h => by
      rw [sortOfTerm, sortOfTerm]; exact h i (by simp [varOccs])
    | .dv _ _, _ => by rw [sortOfTerm, sortOfTerm]
    | .app f ts, h => by
      rw [sortOfTerm, sortOfTerm, sortsOfTerms_congr ts (fun i hi => h i (by rw [varOccs]; exact hi))]
    | .inj a b t, h => by
      rw [sortOfTerm, sortOfTerm, sortOfTerm_congr t (fun i hi => h i (by rw [varOccs]; exact hi))]
    | .as t i, h => by
      rw [sortOfTerm, sortOfTerm, sortOfTerm_congr t (fun j hj => h j (by simp [varOccs, hj])),
        h i (by simp [varOccs])]
    termination_by structural t => t
  theorem sortsOfTerms_congr {x : TermCtx} {vs vs' : List Srt} :
      ∀ (ts : List Term), (∀ i ∈ varOccsList ts, vs[i]? = vs'[i]?) → sortsOfTerms x vs ts = sortsOfTerms x vs' ts
    | [], _ => by rw [sortsOfTerms, sortsOfTerms]
    | t :: ts, h => by
      rw [sortsOfTerms, sortsOfTerms, sortOfTerm_congr t (fun i hi => h i (by simp [varOccsList, hi])),
        sortsOfTerms_congr ts (fun i hi => h i (by simp [varOccsList, hi]))]
    termination_by structural ts => ts
end

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## Patterns -/

/-- The patterns the reading covers: variables in `P`, literals of their sorts, injections between
numbered sorts, `p as X` for `X` in `P`, and applications of a symbol with a signature that is a
constructor, a map pattern symbol, a collection pattern symbol or an overloading symbol, to as many
arguments as it takes; the symbol is no function-overloaded symbol (`fnOvlSyms`: a pattern of one
denotes its normal forms, the model the function's values at covered arguments). -/
inductive PatOK (c : Semantics) (P : Nat → Prop) : Term → Prop where
  | var {i : Nat} (h : P i) : PatOK c P (.var i)
  | dv {s : Srt} {lit : Lit} (h : dvOK c.lib s lit = true) : PatOK c P (.dv s lit)
  | inj {a b : Srt} {t : Term} (ha : a < nRegSorts + c.sortNames.length) (hb : b < nRegSorts + c.sortNames.length)
      (h : PatOK c P t) : PatOK c P (.inj a b t)
  | as {t : Term} {i : Nat} (h : PatOK c P t) (hi : P i) : PatOK c P (.as t i)
  | app {f : Sym} {ts : List Term} {k : CtorSig} (hk : k ∈ kernelSyms c) (hkn : k.name = f)
      (hl : ts.length = k.args.length)
      (hkind : c.isCtor f = true ∨ patternHooks.contains f = true ∨ c.isCollPat f = true ∨ c.isOvl f = true)
      (hnf : f ∉ c.fnOvlSyms)
      (h : ∀ t ∈ ts, PatOK c P t) : PatOK c P (.app f ts)

theorem patVal_var_inv {σ : Subst} {i : Nat} {v : GroundTerm} (h : PatVal c σ (.var i) v) :
    σ.lookup i = some v := by
  cases h; assumption

theorem patVal_dv_inv {σ : Subst} {s : Srt} {lit : Lit} {v : GroundTerm} (h : PatVal c σ (.dv s lit) v) :
    v = .dv s lit := by
  cases h; rfl

theorem patVal_inj_inv {σ : Subst} {a b : Srt} {t : Term} {v : GroundTerm} (h : PatVal c σ (.inj a b t) v) :
    ∃ w, PatVal c σ t w ∧ v = injNormal a b w := by
  cases h with
  | inj h' => exact ⟨_, h', rfl⟩

theorem patVal_as_inv {σ : Subst} {t : Term} {i : Nat} {v : GroundTerm} (h : PatVal c σ (.as t i) v) :
    PatVal c σ t v ∧ σ.lookup i = some v := by
  cases h with
  | as h' hi => exact ⟨h', hi⟩

section
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem pargs_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ PatVals c σ ts ws := by
  induction ts with
  | nil => intro bs h; cases h; exact ⟨[], rfl, .nil⟩
  | cons t ts iht =>
    intro bs h
    cases h with
    | cons hb hbs =>
      obtain ⟨v, hv, rfl⟩ := (ih t (List.mem_cons_self ..) _).mp hb
      obtain ⟨ws, rfl, hws⟩ := iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hbs
      exact ⟨v :: ws, rfl, .cons hv hws⟩

end AtT

theorem pargs_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI c) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI c) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ PatVals c σ ts ws :=
  AtT.pargs_read (c := c) (T := StepM c) (ts := ts) (ih := ih)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem pargs_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {ws : List GroundTerm}, PatVals c σ ts ws →
      All2 (fun φ b => φ.interpret (stdI_T c T) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) := by
  induction ts with
  | nil => intro ws h; cases h; exact .nil
  | cons t ts iht =>
    intro ws h
    cases h with
    | cons ht hts =>
      exact .cons ((ih t (List.mem_cons_self ..) _).mpr ⟨_, ht, rfl⟩)
        (iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hts)

end AtT

theorem pargs_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI c) e m ↔
      ∃ v, PatVal c σ t v ∧ m = .val v) :
    ∀ {ws : List GroundTerm}, PatVals c σ ts ws →
      All2 (fun φ b => φ.interpret (stdI c) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) :=
  AtT.pargs_read' (c := c) (T := StepM c) (ts := ts) (ih := ih)

theorem patVals_length : ∀ {ts : List Term} {ws : List GroundTerm}, PatVals c σ ts ws → ts.length = ws.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [patVals_length hs]

end

/-- The map pattern symbols are interpreted hooks. -/
theorem patternHooks_hook {f : Sym} (h : patternHooks.contains f = true) : isHook f = true := by
  simp only [patternHooks, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with rfl | rfl | rfl <;> decide

/-- A collection pattern symbol that is not a hook is a parameter. -/
theorem collPat_param {f : Sym} (h : c.isCollPat f = true) (hh : isHook f = false) : c.isParam f = true := by
  unfold Semantics.isCollPat at h
  rw [hh] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
  unfold Semantics.isParam
  cases hp : c.lookupParam f with
  | none => rw [hp] at h; simp at h
  | some _ => rfl

theorem collVal_hook {f : Sym} (hh : isHook f = true) (vs : List GroundTerm) :
    c.collVal f vs = (hook f vs).join := by
  unfold Semantics.collVal; rw [if_pos hh]

theorem collVal_param {f : Sym} (hh : isHook f = false) (vs : List GroundTerm) :
    c.collVal f vs = c.paramVal f vs := by
  unfold Semantics.collVal; simp [hh]

theorem join_eq_some {o : Option (Option GroundTerm)} {v : GroundTerm} : o.join = some v ↔ o = some (some v) := by
  cases o with
  | none => simp
  | some o' => cases o' <;> simp

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of a pattern**: under a valuation that reads each variable as its value in σ, a
pattern denotes exactly the values it denotes under σ. -/
theorem tr_pat (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {p : Term} (hp : PatOK c P p) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret (stdI_T c T) e m ↔
      ∃ v, PatVal c σ p v ∧ m = .val v := by
  have hn := h.namesK
  induction hp with
  | @var i hi =>
    intro m
    rw [Term.kore, hvar i hi m]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, .var hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, patVal_var_inv hv, rfl⟩
  | @dv s lit hd =>
    intro m
    have := tr_term (T := T) h (P := fun _ => False) (vs := vs) (tbl := tbl) (e := e) (σ := σ) (fun _ hf => hf.elim)
      (TermOK.dv hd) m
    rw [this]
    constructor
    · rintro ⟨v, hv, rfl⟩; cases evalTerm_dv_inv hv; exact ⟨_, .dv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; cases patVal_dv_inv hv; exact ⟨_, .dv, rfl⟩
  | @inj a b t ha hb _ ih =>
    intro m
    rw [Term.kore, KoreAML.tr_injP]
    rw [interp_appList]
    simp only [KoreAML.interp_sym, stdI_symb, evalSymb_inj]
    constructor
    · rintro ⟨a0, rfl, bs, hbs, happ⟩
      cases hbs with
      | cons h1 hbs =>
        cases hbs with
        | cons h2 hbs =>
          cases hbs with
          | cons h3 hbs =>
            cases hbs
            rename_i x1 x2 x3
            have e1 : x1 = .srt a := (sort_den hn ha e x1).mp h1
            have e2 : x2 = .srt b := (sort_den hn hb e x2).mp h2
            subst e1 e2
            obtain ⟨w, hw, rfl⟩ := (ih x3).mp h3
            simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left] at happ
            subst happ
            exact ⟨injNormal a b w, .inj hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := patVal_inj_inv hv
      refine ⟨_, rfl, [.srt a, .srt b, .val w], .cons ((sort_den hn ha e _).mpr rfl)
        (.cons ((sort_den hn hb e _).mpr rfl) (.cons ((ih _).mpr ⟨w, hw, rfl⟩) .nil)), ?_⟩
      simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left]
  | @as t i _ hi ih =>
    intro m
    rw [Term.kore, tr_and2, KoreAML.interp_sAnd, ih m, hvar i hi m]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, ⟨v', hv', he⟩⟩
      cases he
      exact ⟨v, .as hv hv', rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨h1, h2⟩ := patVal_as_inv hv
      exact ⟨⟨v, h1, rfl⟩, ⟨v, h2, rfl⟩⟩
  | @app f ts k hk hkn hl hkind hnf _ ih =>
    intro m
    subst hkn
    rw [kore_app_tr, interp_appList]
    constructor
    · rintro ⟨a, ha, bs, hbs, happ⟩
      obtain ⟨ws, rfl, hws⟩ := pargs_read (T := T) ih hbs
      have hlw : ws.length = k.args.length := by
        rw [← hl, patVals_length hws]
      have hr := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw m).mp ⟨a, ha, happ⟩
      unfold result at hr
      by_cases hc : c.isCtor k.name = true
      · rw [if_pos hc] at hr
        subst hr
        exact ⟨_, .ctor hc hws, rfl⟩
      rw [if_neg hc] at hr
      have hc' : c.isCtor k.name = false := by simpa using hc
      by_cases hh : isHook k.name = true
      · rw [if_pos hh] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        by_cases hph : patternHooks.contains k.name = true
        · rw [Semantics.hookRes_of_notKey (silentKey_of_patternHook hph)] at hv
          exact ⟨v, .hook hph hws hv, rfl⟩
        · have hcp : c.isCollPat k.name = true := by
            rcases hkind with h1 | h1 | h1 | h1
            · exact absurd h1 hc
            · exact absurd h1 hph
            · exact h1
            · rw [(c.isOvl_parts h1).2.1] at hh; cases hh
          have hcs : silentKey k.name = false := by
            unfold Semantics.isCollPat at hcp
            simp only [hh, if_true, Bool.and_eq_true] at hcp
            exact silentKey_of_collPatternHook hcp.2
          rw [Semantics.hookRes_of_notKey hcs] at hv
          exact ⟨v, .coll hc' hcp hws (by rw [collVal_hook hh, hv]; rfl), rfl⟩
      rw [if_neg hh] at hr
      have hh' : isHook k.name = false := by simpa using hh
      by_cases ho : c.isOvl k.name = true
      · have hp' := (c.isOvl_parts ho).2.2.1
        simp only [hp', ho, Bool.false_eq_true, ↓reduceIte] at hr
        rw [ovlRes_none (OvlLaws.fnCover_none_of_not_fnOvl hnf _)] at hr
        subst hr
        exact ⟨_, .ovl hc' ho hws rfl, rfl⟩
      have hcp : c.isCollPat k.name = true := by
        rcases hkind with h1 | h1 | h1 | h1
        · exact absurd h1 hc
        · exact absurd (patternHooks_hook h1) hh
        · exact h1
        · exact absurd h1 ho
      have hp := collPat_param hcp hh'
      rw [if_pos hp] at hr
      obtain ⟨v, rfl, hv⟩ := hr
      exact ⟨v, .coll hc' hcp hws (by rw [collVal_param hh', hv]), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have key : ∀ (ws : List GroundTerm), PatVals c σ ts ws → result c k ws (.val v) →
          ∃ a, (match iteSort? (c.symName k.name) with
            | some X => KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))
            | none => KoreAML.sym (.symbol (c.symName k.name))).interpret (stdI_T c T) e a ∧
            ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
              ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs ∧ AppE (stdI_T c T) a bs (.val v) := by
        intro ws hts hres
        have hlw : ws.length = k.args.length := by rw [← hl, patVals_length hts]
        obtain ⟨a, ha, happ⟩ := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw _).mpr hres
        exact ⟨a, ha, _, pargs_read' ih hts, happ⟩
      generalize hf : k.name = f at hv
      cases hv with
      | ctor hc hts =>
        subst hf
        exact key _ hts ((result_ctor hc _).mpr rfl)
      | hook hph hts hv' =>
        subst hf
        have hh := patternHooks_hook hph
        have hc : c.isCtor k.name = false := by
          cases hcb : c.isCtor k.name with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨k', hk'⟩ := lookupSig_hookSigs_of_isHook hh
            have hk'm := (lookupSig_spec hk').1
            have := h.hookNotCtor hk'm
            rw [(lookupSig_spec hk').2, hcb] at this
            cases this
        exact key _ hts ((result_hook hc hh _).mpr ⟨v, rfl, Semantics.hookRes_of_value hv'⟩)
      | coll hc hcp hts hv' =>
        subst hf
        by_cases hh : isHook k.name = true
        · rw [collVal_hook hh, join_eq_some] at hv'
          exact key _ hts ((result_hook hc hh _).mpr ⟨v, rfl, Semantics.hookRes_of_value hv'⟩)
        · have hh' : isHook k.name = false := by simpa using hh
          rw [collVal_param hh'] at hv'
          exact key _ hts ((result_param hc hh' (collPat_param hcp hh') _).mpr ⟨v, rfl, hv'⟩)
      | ovl _ ho hts hnv =>
        subst hf
        exact key _ hts ((result_ovl ho (OvlLaws.fnCover_none_of_not_fnOvl hnf _) _).mpr (by rw [hnv]))

end AtT

/-- **The reading of a pattern**: under a valuation that reads each variable as its value in σ, a
pattern denotes exactly the values it denotes under σ. -/
theorem tr_pat (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {p : Term} (hp : PatOK c P p) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs p)).interpret (stdI c) e m ↔
      ∃ v, PatVal c σ p v ∧ m = .val v :=
  AtT.tr_pat (c := c) (T := StepM c) (h := h) (P := P) (vs := vs) (tbl := tbl) (e := e) (σ := σ) (hvar := hvar) (p := p) (hp := hp)

/-! ## The terms and patterns of a well-formed semantics are covered -/

theorem HypModelCore.patHeads (h : HypModelCore c) : patHeadsOK c = true := h.sound.2.2.2.2.2.2.2.1

theorem patHead_kernel {k : CtorSig} (hk : k ∈ c.patCtxAll.heads) : k ∈ kernelSyms c := by
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs, List.mem_append] at hk
  rcases hk with (hk | hk) | (hk | hk) | hk
  · exact ctor_kernel hk
  · exact kernel_hook (List.mem_filter.mp hk).1
  · exact kernel_hook (List.mem_filter.mp hk).1
  · obtain ⟨kp, hkp, rfl⟩ := List.mem_map.mp hk
    exact kernel_param (List.mem_filter.mp hkp).1
  · exact List.mem_append_right _ hk

mutual
  theorem patOK_of_sorted (h : HypModelCore c) : ∀ {vars : List Srt} {p : Term} {s : Srt},
      sortOfTerm c.patCtxAll vars p = some s → PatOK c (· < vars.length) p
    | _, .var _, _, ht => .var (List.getElem?_eq_some_iff.mp (sortOfTerm_var.mp ht)).1
    | _, .dv _ _, _, ht => .dv (sortOfTerm_dv.mp ht).1
    | _, .app f ts, _, ht => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      have hh := List.all_eq_true.mp h.patHeads k hkm
      simp only [downHead, Bool.or_eq_true] at hh
      rw [hkn] at hh
      refine .app (patHead_kernel hkm) hkn (sortsOfTerms_length hargs) ?_
        (by rw [(h.sound.2.2.2.2.2.2.2.2 : OvlOK c).noFn]; exact List.not_mem_nil) (patOKs_of_sorted h hargs)
      rcases hh with h1 | (h1 | h1) | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    | _, .inj _ _ t, _, ht => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      exact .inj (h.subSorts hab).1 (h.subSorts hab).2 (patOK_of_sorted h ht')
    | _, .as t _, _, ht => by
      obtain ⟨hi, ht'⟩ := Exec.sortOfTerm_as ht
      exact .as (patOK_of_sorted h ht') (List.getElem?_eq_some_iff.mp hi).1
    termination_by structural _ p _ _ => p
  theorem patOKs_of_sorted (h : HypModelCore c) : ∀ {vars : List Srt} {ps : List Term} {ss : List Srt},
      sortsOfTerms c.patCtxAll vars ps = some ss → ∀ t ∈ ps, PatOK c (· < vars.length) t
    | _, [], _, _ => fun _ ht => absurd ht List.not_mem_nil
    | _, p :: ps, _, hs => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      have hp := patOK_of_sorted h h1
      have hps := patOKs_of_sorted h h2
      exact fun t ht => (List.mem_cons.mp ht).elim (fun he => he ▸ hp) (fun ht => hps t ht)
    termination_by structural _ ps _ _ => ps
end

theorem rhsHead_kernel {L : List CtorSig} (hL : HeadsOK c L) {k : CtorSig} (hk : k ∈ (c.rhsCtx L).heads) :
    k ∈ kernelSyms c := by
  simp only [Semantics.rhsCtx, List.mem_append] at hk
  rcases hk with ((((hk | hk) | hk) | hk) | hk) | hk
  · exact ctor_kernel hk
  · exact kernel_hook hk
  · obtain ⟨kp, hkp, rfl⟩ := List.mem_map.mp hk
    exact kernel_param hkp
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hk
    exact fn_sig_mem (List.mem_append_right _ hfn)
  · obtain ⟨fn, hfn, rfl⟩ := hL k hk
    exact fn_sig_mem hfn
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk
    exact ovl_kernel ho

theorem sortOfTerm_rhs_as {L : List CtorSig} {vars : List Srt} {t : Term} {i : Nat} {s : Srt} :
    sortOfTerm (c.rhsCtx L) vars (.as t i) ≠ some s := by
  simp [sortOfTerm, Semantics.rhsCtx]

mutual
  theorem termOK_of_sorted (h : HypModelCore c) {L : List CtorSig} (hL : HeadsOK c L) :
      ∀ {vars : List Srt} {t : Term} {s : Srt},
      sortOfTerm (c.rhsCtx L) vars t = some s → TermOK c (· < vars.length) t
    | _, .var _, _, ht => .var (List.getElem?_eq_some_iff.mp (sortOfTerm_var.mp ht)).1
    | _, .dv _ _, _, ht => .dv (sortOfTerm_dv.mp ht).1
    | _, .app f ts, _, ht => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      exact .app (rhsHead_kernel hL hkm) hkn (sortsOfTerms_length hargs) (termOKs_of_sorted h hL hargs)
    | _, .inj _ _ t, _, ht => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      exact .inj (h.subSorts hab).1 (h.subSorts hab).2 (termOK_of_sorted h hL ht')
    | _, .as _ _, _, ht => absurd ht sortOfTerm_rhs_as
    termination_by structural _ t _ _ => t
  theorem termOKs_of_sorted (h : HypModelCore c) {L : List CtorSig} (hL : HeadsOK c L) :
      ∀ {vars : List Srt} {ts : List Term} {ss : List Srt},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → ∀ t ∈ ts, TermOK c (· < vars.length) t
    | _, [], _, _ => fun _ ht => absurd ht List.not_mem_nil
    | _, p :: ps, _, hs => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      have hp := termOK_of_sorted h hL h1
      have hps := termOKs_of_sorted h hL h2
      exact fun t ht => (List.mem_cons.mp ht).elim (fun he => he ▸ hp) (fun ht => hps t ht)
    termination_by structural _ ps _ _ => ps
end

/-! ## Termination of terms -/

theorem sortPreds_shape {fn : Fn} (hfn : fn ∈ c.sortPreds) :
    ∀ cl ∈ fn.clauses, cl.req = none ∧ ∃ s lit, cl.rhs = .dv s lit := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl; exact ⟨rfl, _, _, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨rfl, _, _, rfl⟩

theorem HypModelCore.lookupFn (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) : c.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_allCl h.hyp.1 h.hyp.2.1 h.ovlCase).nodupFns hfn

/-- A function of the semantics is the one `lookupFn` finds under its label. -/
theorem lookupFn_of_sound (hs : HypSoundCore c) {fn : Fn} (hfn : fn ∈ c.allFns) : c.lookupFn fn.label = some fn := by
  rw [Semantics.lookupFn_eq]
  exact find?_label (sortCtx_of_all hs.1 hs.2.1 (OvlOK.ovlCase hs.2.2.2.2.2.2.2.2)).nodupFns hfn

/-- **A sort predicate terminates** at every argument list: its clauses have no `requires` and
literals as right-hand sides, so each applies or fails (`eval_result`). -/
theorem sortPred_total (hs : HypSoundCore c) {fn : Fn} (hfn : fn ∈ c.sortPreds) (vs : List GroundTerm) :
    ∃ r, Eval c fn.label vs r := by
  have hlk := lookupFn_of_sound hs (List.mem_append_right _ hfn)
  have hsh := sortPreds_shape hfn
  exact eval_result hlk (fun cl hcl => ⟨Semantics.sortPreds_exs hfn cl hcl, Semantics.sortPreds_post hfn cl hcl⟩) (Semantics.sortPreds_binds hfn) (fun cl hcl σ _ _ => ⟨(fun t ht => by rw [(hsh cl hcl).1] at ht; cases ht), true,
      Clause.holds_preTop (Semantics.sortPreds_pre hfn cl hcl) σ⟩)
    (fun cl hcl _ _ => by obtain ⟨_, s, l, h⟩ := hsh cl hcl; rw [h]; exact ⟨_, .dv⟩)
    (fun cl hcl _ _ t ht => by rw [sortPreds_ens hfn cl hcl] at ht; cases ht)

/-- **A function of the semantics terminates** at arguments of its sorts, where every function of
the definition does (`FnTerminates`). -/
theorem fn_total (hs : HypSoundCore c) (ht : FnTerminates c) {fn : Fn} (hfn : fn ∈ c.allFns) {vs : List GroundTerm}
    (hvs : c.sortsOf vs = some fn.args) : ∃ r, Eval c fn.label vs r := by
  rcases List.mem_append.mp hfn with hfn | hfn
  · exact ht fn hfn vs hvs
  · exact sortPred_total hs hfn vs

theorem isParam_of_mem {kp : ParamSig} (hkp : kp ∈ c.params) : c.isParam kp.sig.name = true := by
  unfold Semantics.isParam
  rw [Semantics.lookupParam_eq]
  cases hf : c.params.find? (·.sig.name == kp.sig.name) with
  | none => exact absurd (List.find?_eq_none.mp hf kp hkp) (by simp)
  | some _ => rfl

/-- A head of a right-hand side that is no constructor, hook, parameter or overloading symbol is a
function's. -/
theorem rhsHead_fn (hok : c.overloadsOK = true) {L : List CtorSig} (hL : HeadsOK c L) {k : CtorSig}
    (hk : k ∈ (c.rhsCtx L).heads) (hc : c.isCtor k.name = false) (hh : isHook k.name = false)
    (hp : c.isParam k.name = false) (hov : c.isOvl k.name = false) :
    ∃ fn ∈ c.allFns, fn.sig = k := by
  simp only [Semantics.rhsCtx, List.mem_append] at hk
  rcases hk with ((((hk | hk) | hk) | hk) | hk) | hk
  · rw [isCtor_of_mem hk] at hc; cases hc
  · rw [hookSigs_hooked k hk] at hh; cases hh
  · obtain ⟨kp, hkp, rfl⟩ := List.mem_map.mp hk
    rw [isParam_of_mem hkp] at hp; cases hp
  · obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hk
    exact ⟨fn, List.mem_append_right _ hfn, rfl⟩
  · exact hL k hk
  · exfalso
    obtain ⟨o, hom, rfl⟩ := List.mem_map.mp hk
    obtain ⟨o', ho'⟩ : ∃ o', c.lookupOvl o.sig.name = some o' :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨o, hom, by simp⟩)
    rw [(OvlLaws.ovl_parts hok ho').2.2.1] at hov; cases hov

mutual
  /-- **Every well-sorted term has a result** under a well-sorted σ, where every function of the
  definition has a result at arguments of its sorts. -/
  theorem evalTerm_total (h : HypSoundCore c) (hft : FnTerminates c) {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt} {σ : Subst}
      (hσ : c.WellSorted vars σ) : ∀ {t : Term} {s : Srt},
      sortOfTerm (c.rhsCtx L) vars t = some s → ∃ r, EvalTerm c σ t r
    | .var _, _, _ => ⟨_, .var⟩
    | .dv _ _, _, _ => ⟨_, .dv⟩
    | .inj _ _ t, _, ht => by
      obtain ⟨-, ht', -⟩ := sortOfTerm_inj.mp ht
      obtain ⟨r, hr⟩ := evalTerm_total h hft hL hσ ht'
      exact ⟨_, .inj hr⟩
    | .as _ _, _, ht => absurd ht sortOfTerm_rhs_as
    | .app f ts, _, ht => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      obtain ⟨rs, hrs⟩ := evalTerms_total h hft hL hσ hargs
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
          (fun ws has => EvalTerms.sorted hsc hrs hL hσ hargs has)
          (fun kg _ _ fn hfn _ hn vs hvs => hn ▸ hft fn hfn vs hvs)
      | false =>
      cases has : allSome rs with
      | none => exact ⟨none, .callUndef hc' hh' hrs has hp'⟩
      | some ws =>
        subst hkn
        obtain ⟨fn, hfn, rfl⟩ := rhsHead_fn h.2.2.2.2.2.2.2.2.ok hL hkm hc' hh' hp' hov
        have hws : c.sortsOf ws = some fn.args :=
          EvalTerms.sorted (sortCtx_of_all h.1 h.2.1 (OvlOK.ovlCase h.2.2.2.2.2.2.2.2)) hrs hL hσ hargs has
        obtain ⟨r, hr⟩ := fn_total h hft hfn hws
        exact ⟨r, .call hc' hh' hrs has hr hp'⟩
    termination_by structural t _ _ => t
  theorem evalTerms_total (h : HypSoundCore c) (hft : FnTerminates c) {L : List CtorSig} (hL : HeadsOK c L) {vars : List Srt} {σ : Subst}
      (hσ : c.WellSorted vars σ) : ∀ {ts : List Term} {ss : List Srt},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → ∃ rs, EvalTerms c σ ts rs
    | [], _, _ => ⟨[], .nil⟩
    | t :: ts, _, hs => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp hs
      obtain ⟨r, hr⟩ := evalTerm_total h hft hL hσ h1
      obtain ⟨rs, hrs⟩ := evalTerms_total h hft hL hσ h2
      exact ⟨r :: rs, .cons hr hrs⟩
    termination_by structural ts _ _ => ts
end

/-- **A well-sorted term has a result under a substitution well sorted on its variables**, where
every function has a result at arguments of its sorts: the variables outside `is` are given the
sort `Bool` and a value of it (`Semantics.extendHeld`), at which the term has the same sort and the
same result. -/
theorem evalTerm_total_atMP (h : HypSoundCore c) (hft : FnTerminates c) {L : List CtorSig}
    (hL : HeadsOK c L) {vars : List Srt} {is : List Nat} {τ : Subst} (hτ : c.WellSortedAt vars is τ)
    {t : Term} {s : Srt} (hvt : ∀ i ∈ varOccs t, i ∈ is) (ht : sortOfTerm (c.rhsCtx L) vars t = some s) :
    ∃ r, EvalTerm c τ t r := by
  let vars' : List Srt := (List.range vars.length).map fun i => if i ∈ is then vars.getD i 0 else Srt.bool
  have hv' : ∀ i, vars'[i]? =
      if i < vars.length then some (if i ∈ is then vars.getD i 0 else Srt.bool) else none := by
    intro i
    simp only [vars', List.getElem?_map]
    split
    · rename_i h; rw [List.getElem?_range h]; rfl
    · rename_i h; rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]; rfl
  have hagree : ∀ i ∈ is, vars'[i]? = vars[i]? := by
    intro i hi
    rw [hv']
    by_cases hlt : i < vars.length
    · simp [hlt, hi, List.getD_eq_getElem?_getD]
    · simp only [hlt, ite_false]
      exact (List.getElem?_eq_none (Nat.le_of_not_lt hlt)).symm
  have hheld : c.HeldAt vars' is := by
    intro i s' hs'
    by_cases hi : i ∈ is
    · exact Or.inl hi
    · right
      rw [hv'] at hs'
      split at hs'
      · simp only [Option.some.injEq] at hs'
        subst hs'
        exact ⟨bool true, sortOf_bool true⟩
      · cases hs'
  have hτ' : c.WellSortedAt vars' is τ := fun i hi s' hs' => hτ i hi s' (by rw [← hagree i hi]; exact hs')
  obtain ⟨τ', hτw, hτa⟩ := Semantics.extendHeld hheld hτ'
  have ht' : sortOfTerm (c.rhsCtx L) vars' t = some s := by
    rw [sortOfTerm_congr t fun i hi => hagree i (hvt i hi)]; exact ht
  obtain ⟨r, hr⟩ := evalTerm_total h hft hL hτw ht'
  exact ⟨r, Exec.EvalTerm.congr hr fun i hi => hτa i (hvt i hi)⟩

/-- Where every function has a result at arguments of its sorts, each `requires` of a clause has a
result at each match well sorted on its patterns and conditions (`PrioDecided`), which hold the
`requires`' variables; the clause's predicate is `\top`, true there. -/
theorem prioDecided_of_total (hs : HypSoundCore c) (ht : FnTerminates c) : PrioDecided c := by
  intro fn hfn vs cl σ _ _ cl' hcl' _ _ σ' hσ' _
  refine ⟨fun t hq => ?_, true,
    Clause.holds_preTop (Semantics.sortedOK_preTop hs.1 fn (List.mem_append_left _ hfn) cl' hcl') σ'⟩
  obtain ⟨-, -, L, hL, hreqs, -⟩ := clause_ctxOccE hs.1 (List.mem_append_left _ hfn) hcl'
  exact evalTerm_total_atMP hs ht hL hσ' (Clause.req_leftVarsRH hq) (hreqs t hq)

/-- Where every function has a result at arguments of its sorts, each clause instance has a result
under each well-sorted substitution: its `ensures` has one, and where that is `true`, its
right-hand side. -/
theorem instRes_of_total (hs : HypSoundCore c) (ht : FnTerminates c) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl' : Clause} (hcl' : cl' ∈ fn.clauses) {σ' : Subst} (hσ' : c.WellSorted cl'.vars σ') :
    ∃ r, cl'.InstRes c σ' r := by
  obtain ⟨-, -, L, hL, -, hrhs, hens⟩ := clause_ctxOccE hs.1 (List.mem_append_left _ hfn) hcl'
  obtain ⟨r, hr⟩ := evalTerm_total hs ht hL hσ' hrhs
  cases he : cl'.ens with
  | none => exact ⟨r, .inl ⟨fun t ht => (by rw [he] at ht; cases ht), hr⟩⟩
  | some t =>
    obtain ⟨w, hw⟩ := evalTerm_total hs ht hL hσ' (hens t he)
    by_cases hb : w = some (bool true)
    · subst hb
      exact ⟨r, .inl ⟨fun t' ht' => (by rw [he] at ht'; cases ht'; exact hw), hr⟩⟩
    · exact ⟨none, .inr ⟨t, w, he, hw, hb, rfl⟩⟩

/-- Where every function has a result at arguments of its sorts, each clause instance has a result
at each well-sorted match (`CoDefined`, `instRes_of_total`). -/
theorem coDefined_of_total (hs : HypSoundCore c) (ht : FnTerminates c) : CoDefined c :=
  fun fn hfn _ cl _ cl' _ _ hcl' _ hdec' _ => instRes_of_total hs ht hfn hcl'
    ((wellSortedAt_univ (Semantics.fnsNoExs_of_sortedOK hs.1 fn hfn cl' hcl')).mp hdec'.1.1)

/-- **Evaluation solves the equations** where every function has at most one result and a result
at arguments of its sorts, and each clause with existential variables has a result (`Clause.Res`)
at each match under which it decides (`hex`; `MatchIndependent` holds it). A clause without
existential variables has one by the termination, its right side's predicate being `\top`. -/
theorem fnSolves_of_total (hs : HypSoundCore c) (hd : FnDet c) (ht : FnTerminates c)
    (hex : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.exs ≠ [] → ∀ vs σ, cl.Decides c fn σ vs → ∃ r, cl.Res c σ r) :
    FnSolves c :=
  fnSolves_of_res (fun _ hfn => lookupFn_of_sound hs (List.mem_append_left _ hfn)) hd
    (prioDecided_of_total hs ht) fun fn hfn cl hcl vs _ σ hdec => by
      by_cases hx : cl.exs = []
      · obtain ⟨r, hr⟩ := instRes_of_total hs ht hfn hcl ((wellSortedAt_univ hx).mp hdec.1.1)
        exact ⟨r, Clause.res_of_instRes hx
          (Semantics.sortedOK_plainCl hs.1 fn (List.mem_append_left _ hfn) cl hcl).2 hr⟩
      · exact hex fn hfn cl hcl hx vs σ hdec

/-! ## `⌈req = true⌉` -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem tr_true {tbl : KoreAML.VarTable} (h : HypModelCore c) (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret (stdI_T c T) e a ↔ a = .val (bool true) := by
  rw [KoreAML.tr_dv, ← KoreAML.tr_dv (t := [])]
  have := denGoal (T := T) h (bool true) Srt.bool (sortOf_bool true) e a
  unfold den KoreAML.den bool at this
  rw [GroundTerm.kore, sortName_bool] at this
  exact this

end AtT

theorem tr_true {tbl : KoreAML.VarTable} (h : HypModelCore c) (e : Valuation Elem) (a : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (.dv (KoreAML.srt "Bool") "true")).interpret (stdI c) e a ↔ a = .val (bool true) :=
  AtT.tr_true (c := c) (T := StepM c) (tbl := tbl) (h := h) (e := e) (a := a)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **`⌈req = true⌉` holds exactly where `req` evaluates to `true`**, at the sort `σ'` of the
premise. -/
theorem reqPat_iff (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t)
    {S : Kore.KSort} {σ' : Elem} (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI_T c T) e a ↔ a = σ')
    (hσ' : KoreAML.IsSort (stdI_T c T) σ') (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs t)))).interpret (stdI_T c T) e m ↔
      KoreAML.Inh (stdI_T c T) σ' m ∧ EvalTerm c σ t (some (bool true)) := by
  have hn := h.namesK
  have hmi := h.det
  have hB : ∀ a, (KoreAML.trSort tbl (KoreAML.srt "Bool")).interpret (stdI_T c T) e a ↔ a = .srt Srt.bool := by
    intro a; rw [trSort_srt, ← sortName_bool (c := c)]; exact sort_den hn bool_numbered e a
  have hBs : KoreAML.IsSort (stdI_T c T) (.srt Srt.bool) :=
    (isSort_iff _).mpr ⟨Srt.bool, List.mem_range.mpr bool_numbered, rfl⟩
  simp only [reqPat]
  rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef hB hS hBs hσ']
  simp only [inh_srt, tr_term h hvar ht, tr_true h]
  constructor
  · rintro ⟨hm, hall⟩
    obtain ⟨v, hv, he⟩ := (hall (.val (bool true)) (sortOf_bool true)).mpr rfl
    cases he
    exact ⟨hm, hv⟩
  · rintro ⟨hm, hv⟩
    refine ⟨hm, fun a _ => ⟨?_, ?_⟩⟩
    · rintro ⟨v', hv', rfl⟩
      cases EvalTerm.functional_of_fnDet hmi hv' hv
      rfl
    · rintro rfl; exact ⟨_, hv, rfl⟩

end AtT

/-- **`⌈req = true⌉` holds exactly where `req` evaluates to `true`**, at the sort `σ'` of the
premise. -/
theorem reqPat_iff (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t)
    {S : Kore.KSort} {σ' : Elem} (hS : ∀ a, (KoreAML.trSort tbl S).interpret (stdI c) e a ↔ a = σ')
    (hσ' : KoreAML.IsSort (stdI c) σ') (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat S (some (Term.kore c vs t)))).interpret (stdI c) e m ↔
      KoreAML.Inh (stdI c) σ' m ∧ EvalTerm c σ t (some (bool true)) :=
  AtT.reqPat_iff (c := c) (T := StepM c) (h := h) (P := P) (vs := vs) (tbl := tbl) (e := e) (σ := σ) (hvar := hvar) (t := t) (ht := ht) (S := S) (σ' := σ') (hS := hS) (hσ' := hσ') (m := m)

/-! ## The variables of a clause or rule -/

mutual
  /-- The variables of a well-sorted pattern of a numbered sort have numbered sorts. -/
  theorem varOccs_num (h : HypModelCore c) {vars : List Srt} : ∀ (t : Term) {s : Srt},
      sortOfTerm c.patCtxAll vars t = some s → s < nRegSorts + c.sortNames.length →
      ∀ i ∈ varOccs t, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length
    | .var j, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      rw [mem_one hi, sortOfTerm_var.mp ht] at hs'
      cases hs'; exact hs
    | .app f ts, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨k, hk, hargs, _⟩ := sortOfTerm_app.mp ht
      exact varOccsList_num h ts hargs
        (fun s0 h0 => h.symSorts (patHead_kernel (lookupSig_spec hk).1) s0 (List.mem_cons_of_mem _ h0)) i hi s' hs'
    | .inj a b t, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨hab, h', _⟩ := sortOfTerm_inj.mp ht
      exact varOccs_num h t h' (h.subSorts hab).1 i hi s' hs'
    | .as t j, s, ht, hs, i, hi, s', hs' => by
      rw [varOccs] at hi
      obtain ⟨hv, h'⟩ := Exec.sortOfTerm_as ht
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_num h t h' hs i hi s' hs'
      · rw [mem_one hi, hv] at hs'; cases hs'; exact hs
    | .dv _ _, _, _, _, i, hi, _, _ => by rw [varOccs] at hi; cases hi
  theorem varOccsList_num (h : HypModelCore c) {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms c.patCtxAll vars ts = some ss → (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
      ∀ i ∈ varOccsList ts, ∀ s', vars[i]? = some s' → s' < nRegSorts + c.sortNames.length
    | [], _, _, _, i, hi, _, _ => by rw [varOccsList] at hi; cases hi
    | t :: ts, ss, ht, hs, i, hi, s', hs' => by
      rw [varOccsList] at hi
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_num h t h1 (hs s (List.mem_cons_self ..)) i hi s' hs'
      · exact varOccsList_num h ts h2 (fun s0 h0 => hs s0 (List.mem_cons_of_mem _ h0)) i hi s' hs'
end

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- A variable of a translated term, through the table `tbl`: its element. -/
theorem var_read {tbl : KoreAML.VarTable} {vs : List KoreAML.Var} {e : Valuation Elem} (i : Nat) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔ m = e.evalEvar (tbl.ev (keyAt vs i)) := by
  unfold KoreAML.varAt; rw [KoreAML.tr]; exact Iff.rfl

end AtT

/-- A variable of a translated term, through the table `tbl`: its element. -/
theorem var_read {tbl : KoreAML.VarTable} {vs : List KoreAML.Var} {e : Valuation Elem} (i : Nat) (m : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔ m = e.evalEvar (tbl.ev (keyAt vs i)) :=
  AtT.var_read (c := c) (T := StepM c) (tbl := tbl) (vs := vs) (e := e) (i := i) (m := m)

/-- The value an element is, if it is one. -/
def toVal : Elem → GroundTerm
  | .val v => v
  | _ => .ctor 0 []

/-- The substitution a valuation gives the variables `vars` named canonically, read through the
table `tbl`: each variable the value its element is. -/
def substE (c : Semantics) (tbl : KoreAML.VarTable) (vars : List Srt) (e : Valuation Elem) : Subst :=
  (List.range vars.length).map fun i => (i, toVal (e.evalEvar (tbl.ev (canonKey c vars i))))

theorem substE_lookup {tbl : KoreAML.VarTable} {vars : List Srt} {e : Valuation Elem} {i : Nat} (hi : i < vars.length) :
    (substE c tbl vars e).lookup i = some (toVal (e.evalEvar (tbl.ev (canonKey c vars i)))) := by
  unfold substE
  rw [List.range_eq_range', lookup_range']
  rw [if_pos ⟨Nat.zero_le _, by omega⟩]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Where a valuation gives each variable a value of its sort, its substitution is well sorted and
each variable reads as its value. -/
theorem substE_ok {tbl : KoreAML.VarTable} {vars : List Srt} {e : Valuation Elem}
    (hin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))) :
    c.WellSorted vars (substE c tbl vars e) ∧
      ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI_T c T) e m ↔
        ∃ v, (substE c tbl vars e).lookup i = some v ∧ m = .val v := by
  have hv : ∀ i < vars.length, ∃ v, e.evalEvar (tbl.ev (canonKey c vars i)) = .val v ∧
      c.sortOf v = some (vars.getD i 0) := fun i hi => inSort_val (hin i hi)
  constructor
  · intro i s hs
    have hi : i < vars.length := (List.getElem?_eq_some_iff.mp hs).1
    obtain ⟨v, he, hsv⟩ := hv i hi
    refine ⟨v, by rw [substE_lookup hi, he]; rfl, ?_⟩
    rwa [List.getD_eq_getElem?_getD, hs, Option.getD_some] at hsv
  · intro i hi m
    obtain ⟨v, he, -⟩ := hv i hi
    rw [var_read, substE_lookup hi]
    show m = e.evalEvar (tbl.ev (canonKey c vars i)) ↔ _
    rw [he]
    simp [toVal]

end AtT

/-- Where a valuation gives each variable a value of its sort, its substitution is well sorted and
each variable reads as its value. -/
theorem substE_ok {tbl : KoreAML.VarTable} {vars : List Srt} {e : Valuation Elem}
    (hin : ∀ i < vars.length, InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))) :
    c.WellSorted vars (substE c tbl vars e) ∧
      ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI c) e m ↔
        ∃ v, (substE c tbl vars e).lookup i = some v ∧ m = .val v :=
  AtT.substE_ok (c := c) (T := StepM c) (tbl := tbl) (vars := vars) (e := e) (hin := hin)

/-- The valuation that gives the canonical variables of `vars`, through `tbl`, the elements of
their values in σ, and agrees with `e` elsewhere. -/
noncomputable def overE (c : Semantics) (tbl : KoreAML.VarTable) (vars : List Srt) (σ : Subst) (e : Valuation Elem) :
    Valuation Elem :=
  ⟨fun x => if h : ∃ i < vars.length, x = tbl.ev (canonKey c vars i)
    then .val ((σ.lookup (Classical.choose h)).getD (.ctor 0 [])) else e.evalEvar x, e.evalSvar⟩

theorem overE_at {tbl : KoreAML.VarTable} {vars : List Srt} {σ : Subst} {e : Valuation Elem}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) {i : Nat} (hi : i < vars.length) :
    (overE c tbl vars σ e).evalEvar (tbl.ev (canonKey c vars i)) = .val ((σ.lookup i).getD (.ctor 0 [])) := by
  have hex : ∃ j < vars.length, tbl.ev (canonKey c vars i) = tbl.ev (canonKey c vars j) := ⟨i, hi, rfl⟩
  show (if h : _ then _ else _) = _
  rw [dif_pos hex]
  obtain ⟨hj, hje⟩ := Classical.choose_spec hex
  have e1 : Classical.choose hex = i := (canonKey_inj hi hj (ev_inj (hkeys i hi) (hkeys _ hj) hje)).symm
  rw [e1]

theorem overE_off {tbl : KoreAML.VarTable} {vars : List Srt} {σ : Subst} {e : Valuation Elem} {x : EVar}
    (hx : ∀ i < vars.length, x ≠ tbl.ev (canonKey c vars i)) : (overE c tbl vars σ e).evalEvar x = e.evalEvar x := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (fun ⟨i, hi, he⟩ => hx i hi he)]

theorem overE_ok {tbl : KoreAML.VarTable} {vars : List Srt} {σ : Subst} {e : Valuation Elem}
    (hkeys : ∀ i < vars.length, canonKey c vars i ∈ tbl) (hσ : c.WellSorted vars σ) :
    ∀ i, i < vars.length → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt (canonVars c vars) i)).interpret (stdI c)
      (overE c tbl vars σ e) m ↔ ∃ v, σ.lookup i = some v ∧ m = .val v := by
  intro i hi m
  rw [var_read]
  show m = (overE c tbl vars σ e).evalEvar (tbl.ev (canonKey c vars i)) ↔ _
  rw [overE_at hkeys hi]
  obtain ⟨v, hv, -⟩ := hσ i (vars.getD i 0) (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  rw [hv]
  simp

/-! ## Existentials over the variables -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- `∃b̄. body` holds at `e` where `body` holds at a valuation that differs from `e` at the binders
only, and gives each binder an element of its sort. -/
theorem existsAll_intro {tbl : KoreAML.VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e e' : Valuation Elem) (m : Elem),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS (stdI_T c T) n (e'.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
    (KoreAML.tr ⟨tbl, []⟩ body).interpret (stdI_T c T) e' m →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI_T c T) e m
  | [], e, e', m, _, _, hoff, hsv, _, hb => by
    have : e' = e := by
      cases e; cases e'
      simp only at hsv
      subst hsv
      congr 1
      funext x
      exact hoff x (fun _ h => absurd h List.not_mem_nil)
    subst this
    exact hb
  | b :: bs, e, e', m, hnd, hs, hoff, hsv, hg, hb => by
    show (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body))).interpret (stdI_T c T) e m
    rw [KoreAML.tr, KoreAML.interp_sExists]
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨e'.evalEvar (tbl.ev (KoreAML.evarKey b)), ?_, ?_⟩
    · rw [KoreAML.interp_member defOK_std]
      simp only [Function.update_same]
      obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
      rw [hn, trSort_srt]
      exact (inS_iff _).mpr (hg b (List.mem_cons_self ..) n hn)
    · refine existsAll_intro bs _ e' m hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb'))
        (fun x hx => ?_) hsv (fun b' hb' => hg b' (List.mem_cons_of_mem _ hb')) hb
      show e'.evalEvar x = Function.update e.evalEvar (tbl.ev (KoreAML.evarKey b)) (e'.evalEvar (tbl.ev (KoreAML.evarKey b))) x
      by_cases hxb : x = tbl.ev (KoreAML.evarKey b)
      · subst hxb; simp only [Function.update_same]
      · rw [Function.update_noteq hxb]
        exact hoff x (fun b' hb' => by
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact hxb
          · exact hx b' hb')

end AtT

/-- `∃b̄. body` holds at `e` where `body` holds at a valuation that differs from `e` at the binders
only, and gives each binder an element of its sort. -/
theorem existsAll_intro {tbl : KoreAML.VarTable} {S : Kore.KSort} {body : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e e' : Valuation Elem) (m : Elem),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e'.evalEvar x = e.evalEvar x) →
    e'.evalSvar = e.evalSvar →
    (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS (stdI c) n (e'.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
    (KoreAML.tr ⟨tbl, []⟩ body).interpret (stdI c) e' m →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body)).interpret (stdI c) e m :=
  AtT.existsAll_intro (c := c) (T := StepM c) (tbl := tbl) (S := S) (body := body)

/-! ## The rules that apply -/

theorem srtOf_top_den_T (h : HypModelCore c) {T : GroundTerm → GroundTerm → Prop} {tbl : KoreAML.VarTable}
    (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl (srtOf c topCellSort)).interpret (stdI_T c T) e a ↔ a = .srt topCellSort := by
  unfold srtOf; rw [trSort_srt]; exact AtT.sort_den h.namesK top_numbered e a

theorem top_isSort_T {T : GroundTerm → GroundTerm → Prop} : KoreAML.IsSort (stdI_T c T) (.srt topCellSort) :=
  (AtT.isSort_iff _).mpr ⟨topCellSort, List.mem_range.mpr top_numbered, rfl⟩

theorem srtOf_top_den (h : HypModelCore c) {tbl : KoreAML.VarTable} (e : Valuation Elem) (a : Elem) :
    (KoreAML.trSort tbl (srtOf c topCellSort)).interpret (stdI c) e a ↔ a = .srt topCellSort :=
  srtOf_top_den_T (T := StepM c) h e a

theorem top_isSort : KoreAML.IsSort (stdI c) (.srt topCellSort) :=
  top_isSort_T (T := StepM c)

end Model

end Faithful

end KCore
