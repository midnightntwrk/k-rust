/-
  KCore. The model-side reading of terms: in the value model, under a valuation that gives each
  variable of a term the element of its value in σ, the translation of a right-hand side or
  `requires` term denotes exactly the values `EvalTerm` gives it (`tr_term`). By construction: a
  symbol is interpreted as what evaluation does with it (`result`), a variable as its value, a
  literal as itself, an injection as `injNormal`. Nothing here needs evaluation to be functional
  or total; those are what a reading of `⌈t = true⌉` adds.
-/
import KcoreSpec.ModelDomains

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-- The terms the reading covers: variables in `P`, literals of their sorts, injections between
numbered sorts, and applications of a symbol with a signature to as many arguments as it takes. -/
inductive TermOK (c : Semantics) (P : Nat → Prop) : Term → Prop where
  | var {i : Nat} (h : P i) : TermOK c P (.var i)
  | dv {s : Srt} {lit : Lit} (h : dvOK c.lib s lit = true) : TermOK c P (.dv s lit)
  | inj {a b : Srt} {t : Term} (ha : a < nRegSorts + c.sortNames.length) (hb : b < nRegSorts + c.sortNames.length)
      (h : TermOK c P t) : TermOK c P (.inj a b t)
  | app {f : Sym} {ts : List Term} {k : CtorSig} (hk : k ∈ kernelSyms c) (hkn : k.name = f)
      (hl : ts.length = k.args.length) (h : ∀ t ∈ ts, TermOK c P t) : TermOK c P (.app f ts)

theorem allSome_map : ∀ ws : List GroundTerm, allSome (ws.map some) = some ws
  | [] => rfl
  | w :: ws => by simp [allSome, allSome_map ws]

theorem tr_ap_tbl (tbl : KoreAML.VarTable) (f : String) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap f ps) =
      KoreAML.appList (KoreAML.sym (.symbol f)) (ps.map (KoreAML.tr ⟨tbl, []⟩)) := by
  unfold KoreAML.ap
  rw [KoreAML.tr_app0, trArgs_appList]

section
variable {vs : List KoreAML.Var} {tbl : KoreAML.VarTable} {e : Valuation Elem} {σ : Subst}

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- Elements of the arguments' readings are the values of a list of evaluations. -/
theorem args_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ EvalTerms c σ ts (ws.map some) := by
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

/-- Elements of the arguments' readings are the values of a list of evaluations. -/
theorem args_read {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI c) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {bs : List Elem}, All2 (fun φ b => φ.interpret (stdI c) e b)
      ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      ∃ ws : List GroundTerm, bs = ws.map Elem.val ∧ EvalTerms c σ ts (ws.map some) :=
  AtT.args_read (c := c) (T := StepM c) (ts := ts) (ih := ih)

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The values of defined evaluations of the arguments are elements of their readings. -/
theorem args_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm}, EvalTerms c σ ts rs → allSome rs = some ws →
      All2 (fun φ b => φ.interpret (stdI_T c T) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) := by
  induction ts with
  | nil => intro rs ws h hs; cases h; cases hs; exact .nil
  | cons t ts iht =>
    intro rs ws h hs
    cases h with
    | cons ht hts =>
      rename_i r rs'
      cases r with
      | none => simp [allSome] at hs
      | some v =>
        cases hr : allSome rs' with
        | none => simp [allSome, hr] at hs
        | some ws' =>
          simp only [allSome, hr, Option.bind_some, Option.map_some, Option.some.injEq] at hs
          subst hs
          exact .cons ((ih t (List.mem_cons_self ..) _).mpr ⟨v, ht, rfl⟩)
            (iht (fun t' ht' => ih t' (List.mem_cons_of_mem _ ht')) hts hr)

end AtT

/-- The values of defined evaluations of the arguments are elements of their readings. -/
theorem args_read' {ts : List Term}
    (ih : ∀ t ∈ ts, ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI c) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v) :
    ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm}, EvalTerms c σ ts rs → allSome rs = some ws →
      All2 (fun φ b => φ.interpret (stdI c) e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩))
        (ws.map Elem.val) :=
  AtT.args_read' (c := c) (T := StepM c) (ts := ts) (ih := ih)

theorem evalTerms_length : ∀ {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
    ts.length = rs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [evalTerms_length hs]

theorem allSome_length : ∀ {rs : List (Option GroundTerm)} {ws : List GroundTerm}, allSome rs = some ws →
    rs.length = ws.length
  | [], ws, h => by cases h; rfl
  | none :: _, _, h => by simp [allSome] at h
  | some v :: rs, ws, h => by
    cases hr : allSome rs with
    | none => simp [allSome, hr] at h
    | some ws' =>
      simp only [allSome, hr, Option.bind_some, Option.map_some, Option.some.injEq] at h
      subst h
      simp [allSome_length hr]

end

theorem evalTerm_var_inv {σ : Subst} {i : Nat} {r : Option GroundTerm} (h : EvalTerm c σ (.var i) r) :
    r = σ.lookup i := by
  cases h; rfl

theorem evalTerm_dv_inv {σ : Subst} {s : Srt} {lit : Lit} {r : Option GroundTerm} (h : EvalTerm c σ (.dv s lit) r) :
    r = some (.dv s lit) := by
  cases h; rfl

theorem evalTerm_inj_inv {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm}
    (h : EvalTerm c σ (.inj a b t) r) : ∃ r', EvalTerm c σ t r' ∧ r = r'.map (injNormal a b) := by
  cases h with
  | inj h' => exact ⟨_, h', rfl⟩

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- The head of an application as `Term.kore` writes it, applied to argument elements: what the
symbol gives on their values. -/
theorem head_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {tbl : KoreAML.VarTable}
    {vs : List KoreAML.Var} {ts : List Term} {e : Valuation Elem} {ws : List GroundTerm}
    (hl : ws.length = k.args.length) (m : Elem) :
    (∃ a, (symHead c k.name).interpret (stdI_T c T) e a ∧
      AppE (stdI_T c T) a (ws.map Elem.val) m) ↔ result c k ws m := by
  obtain ⟨hd, xs, -, hw⟩ := symApp_head c k.name
  rw [symHead_of_symApp hw]
  exact instHead_app h hk hw hl e m

end AtT

/-- The head of an application as `Term.kore` writes it, applied to argument elements: what the
symbol gives on their values. -/
theorem head_app (h : HypModelCore c) {k : CtorSig} (hk : k ∈ kernelSyms c) {tbl : KoreAML.VarTable}
    {vs : List KoreAML.Var} {ts : List Term} {e : Valuation Elem} {ws : List GroundTerm}
    (hl : ws.length = k.args.length) (m : Elem) :
    (∃ a, (symHead c k.name).interpret (stdI c) e a ∧
      AppE (stdI c) a (ws.map Elem.val) m) ↔ result c k ws m :=
  AtT.head_app (c := c) (T := StepM c) (h := h) (k := k) (hk := hk) (tbl := tbl) (vs := vs) (ts := ts) (e := e) (ws := ws) (hl := hl) (m := m)

theorem kore_app_tr {tbl : KoreAML.VarTable} {vs : List KoreAML.Var} (f : Sym) (ts : List Term) :
    KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs (.app f ts)) =
      KoreAML.appList (symHead c f) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) := by
  rw [kore_app, tr_symApp, trArgs_appList]

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The reading of a term**: under a valuation that reads each variable as its value in σ, a
term denotes exactly the values `EvalTerm` gives it under σ. -/
theorem tr_term (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI_T c T) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI_T c T) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v := by
  have hn := h.namesK
  induction ht with
  | @var i hi =>
    intro m
    rw [Term.kore, hvar i hi m]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, by rw [← hv]; exact .var, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, (evalTerm_var_inv hv).symm, rfl⟩
  | @dv s lit hd =>
    intro m
    rw [Term.kore, KoreAML.tr]
    show (KoreAML.sym (.dv lit.text) ⬝ KoreAML.trSort tbl (KoreAML.srt (c.sortName s))).interpret (stdI_T c T) e m ↔ _
    rw [trSort_srt, KoreAML.interp_app]
    simp only [KoreAML.interp_sym, stdI_symb, sort_den hn (h.dvSort hd) e, stdI_app]
    constructor
    · rintro ⟨a, b, ha, rfl, hab⟩
      have ha' : a = .app (.dv lit.text) [] := ha
      subst ha'
      have hab' : ∃ l, m = .val (.dv s l) ∧ l.text = lit.text ∧ dvOK c.lib s l = true := hab
      obtain ⟨l, rfl, hlt, hl⟩ := hab'
      rw [lit_unique h.lits hl hd hlt]
      exact ⟨_, .dv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      cases evalTerm_dv_inv hv
      exact ⟨_, _, rfl, rfl, lit, rfl, rfl, hd⟩
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
            exact ⟨injNormal a b w, EvalTerm.inj hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨r', hr', hr⟩ := evalTerm_inj_inv hv
      cases r' with
      | none => cases hr
      | some w =>
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        refine ⟨_, rfl, [.srt a, .srt b, .val w], .cons ((sort_den hn ha e _).mpr rfl)
          (.cons ((sort_den hn hb e _).mpr rfl) (.cons ((ih _).mpr ⟨w, hr', rfl⟩) .nil)), ?_⟩
        simp only [AppE, stdI_app, evalApp_inj0, evalApp_inj1, evalApp_inj2, exists_eq_left]
  | @app f ts k hk hkn hl _ ih =>
    intro m
    subst hkn
    rw [kore_app_tr, interp_appList]
    constructor
    · rintro ⟨a, ha, bs, hbs, happ⟩
      obtain ⟨ws, rfl, hws⟩ := args_read (T := T) ih hbs
      have hlw : ws.length = k.args.length := by
        rw [← hl, evalTerms_length hws]; simp
      have hr := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw m).mp ⟨a, ha, happ⟩
      unfold result at hr
      by_cases hc : c.isCtor k.name = true
      · rw [if_pos hc] at hr
        subst hr
        refine ⟨_, ?_, rfl⟩
        have := EvalTerm.ctor (σ := σ) hc hws
        rw [allSome_map] at this
        exact this
      rw [if_neg hc] at hr
      have hc' : c.isCtor k.name = false := by simpa using hc
      by_cases hh : isHook k.name = true
      · rw [if_pos hh] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        exact ⟨v, .hook hc' hh hws (fun ws' h' => by rw [allSome_map] at h'; cases h'; exact hv)
          (fun h' => by rw [allSome_map] at h'; cases h'), rfl⟩
      rw [if_neg hh] at hr
      have hh' : isHook k.name = false := by simpa using hh
      by_cases hp : c.isParam k.name = true
      · rw [if_pos hp] at hr
        obtain ⟨v, rfl, hv⟩ := hr
        exact ⟨v, .param hc' hh' hp hws (by rw [allSome_map]; exact hv.symm), rfl⟩
      rw [if_neg hp] at hr
      have hp' : c.isParam k.name = false := by simpa using hp
      by_cases ho : c.isOvl k.name = true
      · rw [if_pos ho] at hr
        cases hcov : c.fnCover k.name ws with
        | none =>
          rw [ovlRes_none hcov] at hr
          subst hr
          refine ⟨_, ?_, rfl⟩
          have := EvalTerm.ovl (σ := σ) hc' ho hws (fun vs hvs => by
            rw [allSome_map] at hvs; cases hvs; exact hcov)
          rw [allSome_map] at this
          exact this
        | some kg =>
          obtain ⟨o, hlo⟩ := Option.isSome_iff_exists.mp (c.isOvl_parts ho).2.2.2.2
          obtain ⟨w, rfl, hw⟩ := (ovlRes_some hlo hcov _).mp hr
          exact ⟨_, .ovlFn hc' ho hws (allSome_map ws) hlo hcov hw, rfl⟩
      rw [if_neg ho] at hr
      obtain ⟨v, rfl, hv⟩ := hr
      exact ⟨v, .call hc' hh' hws (allSome_map ws) hv hp', rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have key : ∀ (rs : List (Option GroundTerm)) (ws : List GroundTerm), EvalTerms c σ ts rs →
          allSome rs = some ws → result c k ws (.val v) →
          ∃ a, (symHead c k.name).interpret (stdI_T c T) e a ∧
            ∃ bs, All2 (fun φ b => φ.interpret (stdI_T c T) e b)
              ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs ∧ AppE (stdI_T c T) a bs (.val v) := by
        intro rs ws hts hws hres
        have hlw : ws.length = k.args.length := by
          rw [← hl, evalTerms_length hts, allSome_length hws]
        obtain ⟨a, ha, happ⟩ := (head_app h hk (tbl := tbl) (vs := vs) (ts := ts) hlw _).mpr hres
        exact ⟨a, ha, _, args_read' ih hts hws, happ⟩
      generalize hr : some v = r at hv
      cases hv with
      | ctor hc hts =>
        rename_i rs
        cases hws : allSome rs with
        | none => rw [hws] at hr; cases hr
        | some ws =>
          rw [hws] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact key rs ws hts hws ((result_ctor hc _).mpr rfl)
      | hook hc hhk hts hh hund =>
        rename_i rs
        subst hr
        cases hws : allSome rs with
        | none => exact absurd (hund hws) (by simp)
        | some ws => exact key rs ws hts hws ((result_hook hc hhk _).mpr
          ⟨v, rfl, hh ws hws⟩)
      | param hc hhk hp hts hr' =>
        rename_i rs
        subst hr
        cases hws : allSome rs with
        | none => rw [hws] at hr'; cases hr'
        | some ws =>
          rw [hws] at hr'
          exact key rs ws hts hws ((result_param hc hhk hp _).mpr ⟨v, rfl, hr'.symm⟩)
      | call hc hh hts hvs hf hp =>
        rename_i rs ws
        subst hr
        exact key rs ws hts hvs ((result_fn hc hh hp (Eval.isOvl_false hf) _).mpr ⟨v, rfl, hf⟩)
      | callUndef => cases hr
      | ovl hc ho hts hnf =>
        rename_i rs
        cases hws : allSome rs with
        | none => rw [hws] at hr; cases hr
        | some ws =>
          rw [hws] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact key rs ws hts hws ((result_ovl ho (hnf ws hws) _).mpr rfl)
      | ovlFn hc ho hts hvs hlo hcov hf =>
        rename_i rs ws o kg r
        cases r with
        | none => cases hr
        | some w =>
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact key rs ws hts hvs ((result_ovlFn ho hlo hcov _).mpr ⟨w, rfl, hf⟩)

end AtT

/-- **The reading of a term**: under a valuation that reads each variable as its value in σ, a
term denotes exactly the values `EvalTerm` gives it under σ. -/
theorem tr_term (h : HypModelCore c) {P : Nat → Prop} {vs : List KoreAML.Var} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {σ : Subst}
    (hvar : ∀ i, P i → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (KoreAML.varAt vs i)).interpret (stdI c) e m ↔
      ∃ v, σ.lookup i = some v ∧ m = .val v) {t : Term} (ht : TermOK c P t) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret (stdI c) e m ↔
      ∃ v, EvalTerm c σ t (some v) ∧ m = .val v :=
  AtT.tr_term (c := c) (T := StepM c) (h := h) (P := P) (vs := vs) (tbl := tbl) (e := e) (σ := σ) (hvar := hvar) (t := t) (ht := ht)

end Model

end Faithful

end KCore
