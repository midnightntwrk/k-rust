/-
  KCore, checked layer: the executable step of CollExec.lean is sound.

  - `patEval_sound`, `patEvals_sound`: a pattern read as a value under σ (`patEval`) denotes that
    value (`PatVal`); `sameL_iff`: `sameL` is equality of lists.
  - `cmatch_sound`: every substitution `cmatch` returns is well sorted and a match (`PatVals`),
    whatever the candidates were: the check reads neither the enumeration nor a value's canonicity.
  - `evalT_sound` (with `evalTs_sound`, `evalF_sound`, `firstClause_sound`): a result `CExec.evalT`
    computes for a well-sorted term under a well-sorted σ is its `EvalTerm` result. A clause the
    evaluation skips must fail (`Fails`) for every well-sorted σ matching it, which the candidates
    reach only if the matcher is complete: that is the hypothesis `ClauseComplete c`.
  - `predVal_sound`: a value `predVal` computes for a well-sorted predicate is its `Holds` value.
  - `successorsN_sound_preds`, `successorsN_sound`, `successorsN_step`, `successors_step`: every
    successor the executable step lists is a `Step`. `NotApplies` for the rules of a smaller
    priority reads `RuleComplete c`.

  The hypotheses read of the core are `sortedOK`, `srReady` and `OvlCase` (all three from
  `execReady`, the last through `matchReadyO`: the sorts of overloading symbols' normal forms), and
  the two matcher completeness statements, which `execReady` gives (`clauseComplete_of_ready`,
  `ruleComplete_of_ready`, CollExecStep.lean).
-/
import KcoreSpec.CollExec
import KcoreSpec.StepSound

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-! ## The check -/

theorem sameL_iff : ∀ {ws vs : List GroundTerm}, sameL ws vs = true ↔ ws = vs
  | [], [] => by simp [sameL]
  | [], _ :: _ => by simp [sameL]
  | _ :: _, [] => by simp [sameL]
  | w :: ws, v :: vs => by
    simp only [sameL, Bool.and_eq_true, same_iff, sameL_iff, List.cons.injEq]

mutual
  /-- A pattern read as a value under σ denotes it. -/
  theorem patEval_sound {σ : Subst} : ∀ {p : Term} {v : GroundTerm},
      patEval c σ p = some v → PatVal c σ p v
    | .var i, v, h => .var (by simpa [patEval] using h)
    | .dv s l, v, h => by
      simp only [patEval, Option.some.injEq] at h
      subst h
      exact .dv
    | .inj a b p, v, h => by
      simp only [patEval, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact .inj (patEval_sound hw)
    | .as p i, v, h => by
      simp only [patEval] at h
      split at h
      · rename_i w u hw hu
        split at h
        · rename_i hs
          cases h
          exact .as (patEval_sound hw) (by rw [hu, same_iff.mp hs])
        · cases h
      · cases h
    | .app f ps, v, h => by
      simp only [patEval] at h
      split at h
      · cases h
      · rename_i vs hvs
        have hs := patEvals_sound hvs
        by_cases hc : c.isCtor f = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact .ctor hc hs
        · have hc' : c.isCtor f = false := by simpa using hc
          simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
          by_cases hp : patternHooks.contains f = true
          · simp only [hp, ↓reduceIte, Option.join_eq_some_iff] at h
            exact .hook hp hs h
          · have hp' : patternHooks.contains f = false := by simpa using hp
            simp only [hp', Bool.false_eq_true, ↓reduceIte] at h
            by_cases hcp : c.isCollPat f = true
            · simp only [hcp, ↓reduceIte] at h
              exact .coll hc' hcp hs h
            · have hcp' : c.isCollPat f = false := by simpa using hcp
              simp only [hcp', Bool.false_eq_true, ↓reduceIte] at h
              by_cases ho : c.isOvl f = true
              · simp only [ho, ↓reduceIte, Option.some.injEq] at h
                exact .ovl hc' ho hs h
              · have ho' : c.isOvl f = false := by simpa using ho
                simp only [ho', Bool.false_eq_true, ↓reduceIte] at h
                cases h
  termination_by structural p => p
  theorem patEvals_sound {σ : Subst} : ∀ {ps : List Term} {vs : List GroundTerm},
      patEvals c σ ps = some vs → PatVals c σ ps vs
    | [], vs, h => by
      simp only [patEvals, Option.some.injEq] at h
      subst h
      exact .nil
    | p :: ps, vs, h => by
      simp only [patEvals] at h
      split at h
      · rename_i v vs' hv hvs
        cases h
        exact .cons (patEval_sound hv) (patEvals_sound hvs)
      · cases h
  termination_by structural ps => ps
end

/-- **The matcher is sound**: every substitution `cmatch` returns is well sorted and under it the
patterns denote the values. -/
theorem cmatch_sound {vars : List Srt} {ps : List Term} {vs : List GroundTerm} {σ : Subst}
    (h : σ ∈ cmatch c vars ps vs) : c.WellSorted vars σ ∧ PatVals c σ ps vs := by
  unfold cmatch at h
  obtain ⟨-, hf⟩ := List.mem_filter.mp h
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hw, hm⟩ := hf
  refine ⟨wellSorted_iff.mp hw, ?_⟩
  split at hm
  · rename_i ws hws
    rw [sameL_iff.mp hm] at hws
    exact patEvals_sound hws
  · cases hm

/-! ## The matcher's completeness, as hypotheses -/

/-- The clauses' matcher is complete at arguments of the function's sorts: every well-sorted σ
under which a clause's patterns denote the arguments agrees, on the clause's variables, with a
substitution `clauseMatches` lists. -/
def ClauseComplete (c : Semantics) : Prop :=
  ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ (vs : List GroundTerm) (τ : Subst),
    c.sortsOf vs = some fn.args → c.WellSortedAt cl.vars cl.leftVars τ → PatVals c τ cl.pats vs →
    ∃ σ₀ ∈ clauseMatches c cl vs, ∀ i < cl.vars.length, σ₀.lookup i = τ.lookup i

/-- The rules' matcher is complete at configurations: every σ that gives the variables of the left
side and the conditions values of their sorts, and under which a rule's left-hand side denotes the
configuration, agrees, on the rule's variables, with a substitution `cmatch` lists. -/
def RuleComplete (c : Semantics) : Prop :=
  ∀ r ∈ c.rules, ∀ (x : GroundTerm) (τ : Subst),
    c.sortOf x = some topCellSort → c.WellSortedAt r.vars r.leftVars τ → PatVal c τ r.lhs x →
    ∃ σ₀ ∈ cmatch c r.vars [r.lhs] [x], ∀ i < r.vars.length, σ₀.lookup i = τ.lookup i

/-! ## What evaluation reads of the clauses -/

/-- Each function's clauses have a `requires` of sort Bool and a right-hand side of the result
sort, over the function signatures of some list L. -/
def CClauseCtx (c : Semantics) : Prop :=
  ∀ fn ∈ c.allFns, ∃ L, HeadsOK c L ∧ ∀ cl ∈ fn.clauses,
    reqOK (c.rhsCtx L) cl.vars cl.req = true ∧ sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
      reqOK (c.rhsCtx L) cl.vars cl.ens = true ∧ cl.pre = .top ∧ cl.exs = [] ∧ cl.post = .top

/-- A clause of a function under `CClauseCtx` has no existential variable and the right side's
predicate `\top`. -/
theorem CClauseCtx.plainCl (hcc : CClauseCtx c) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : cl.exs = [] ∧ cl.post = .top :=
  let ⟨_, _, h⟩ := hcc fn hfn
  (h cl hcl).2.2.2.2

theorem CClauseCtx.fnsNoExs (hcc : CClauseCtx c) : c.FnsNoExs :=
  fun _ hfn _ hcl => (hcc.plainCl (List.mem_append_left _ hfn) hcl).1

theorem cclauseCtx_of (hok : c.sortedOK = true) : CClauseCtx c := by
  have htop := Semantics.sortedOK_preTop hok
  have hpl := Semantics.sortedOK_plainCl hok
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨_, hfns⟩, _⟩ := hok
  intro fn hfn'
  rcases List.mem_append.mp hfn' with hfn | hfn
  · refine ⟨c.fns.map Fn.sig, Exec.headsOK_fns, fun cl hcl => ?_⟩
    have := hfns fn hfn cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at this
    replace this := this.1
    exact ⟨this.1.1.1.2, this.1.1.2, this.1.2, htop fn hfn' cl hcl, hpl fn hfn' cl hcl⟩
  · exact ⟨[], fun k hk => (nomatch hk), fun cl h =>
      ⟨(sortPreds_ctx hfn cl h).2.2.2.1, (sortPreds_ctx hfn cl h).2.2.2.2.1, (sortPreds_ctx hfn cl h).2.2.2.2.2,
        htop fn hfn' cl h, hpl fn hfn' cl h⟩⟩

/-! ## The clauses' candidates, as `firstClause` computes them -/

/-- A match's `requires` with `n` units of fuel: `some true` without one, `none` out of fuel. -/
def clauseReq (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option Bool :=
  match cl.req with
  | none => some true
  | some t => (CExec.evalT c n σ t).map isTrue

/-- The candidates of the clauses `cls` at `vs`: each clause with each of its matches and its
`requires`. -/
def candidates (c : Semantics) (n : Nat) (vs : List GroundTerm) (cls : List Clause) :
    List (Clause × Subst × Option Bool) :=
  cls.flatMap fun cl => (clauseMatches c cl vs).map fun σ => (cl, σ, clauseReq c n cl σ)

/-- A match's `ensures` with `n` units of fuel: `some true` without one, `none` out of fuel. -/
def clauseEns (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option Bool :=
  match cl.ens with
  | none => some true
  | some t => (CExec.evalT c n σ t).map isTrue

/-- A match's result where its `requires` is `true`: its right-hand side's where its `ensures` is
`true`, undefined where the `ensures` is something else, none out of fuel. -/
def candBody (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option (Option GroundTerm) :=
  match clauseEns c n cl σ with
  | some true => CExec.evalT c n σ cl.rhs
  | some false => some none
  | none => none

/-- A candidate's result: `candBody`, where its `requires` is `true`. -/
def candResult (c : Semantics) (n : Nat) (a : Clause × Subst × Option Bool) : Option (Option GroundTerm) :=
  if a.2.2 == some true then candBody c n a.1 a.2.1 else none

theorem firstClause_cons (n : Nat) (vs : List GroundTerm) (fr : Option GroundTerm) (cl : Clause)
    (rest : List Clause) :
    CExec.firstClause c (n + 1) vs fr (cl :: rest) =
      match (candidates c n vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome? (candResult c n) with
      | some r => some r
      | none =>
        if (candidates c n vs ((cl :: rest).takeWhile (·.prio == cl.prio))).all (·.2.2 == some false) then
          CExec.firstClause c n vs fr ((cl :: rest).dropWhile (·.prio == cl.prio))
        else none := by
  simp only [CExec.firstClause]
  rfl

theorem mem_candidates {n : Nat} {vs : List GroundTerm} {cls : List Clause} {cl : Clause} {σ : Subst}
    {b : Option Bool} :
    (cl, σ, b) ∈ candidates c n vs cls ↔ cl ∈ cls ∧ σ ∈ clauseMatches c cl vs ∧ b = clauseReq c n cl σ := by
  simp only [candidates, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨cl', h1, σ', h2, rfl, rfl, rfl⟩
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨cl, h1, σ, h2, rfl, rfl, rfl⟩

/-- A clause all of whose listed matches have a `requires` evaluating to something other than
`true` fails, where the matcher is complete (`ClauseComplete`): every well-sorted σ under which its
patterns denote the arguments agrees on the clause's variables with a listed match. -/
theorem fails_of_false (hcm : ClauseComplete c) {fn : Fn} {vs : List GroundTerm} {cl : Clause}
    {n : Nat} {L : List CtorSig} (hfn : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses)
    (hvs : c.sortsOf vs = some fn.args) (hreq : reqOK (c.rhsCtx L) cl.vars cl.req = true)
    (hev : ∀ σ t r, CExec.evalT c n σ t = some r → c.WellSorted cl.vars σ →
      sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool → EvalTerm c σ t r)
    (hf : ∀ σ ∈ clauseMatches c cl vs, clauseReq c n cl σ = some false) : Fails c vs cl :=
  .intro fun τ hτ hpv => by
    obtain ⟨σ₀, hm₀, hag⟩ := hcm fn hfn cl hcl vs τ hvs hτ hpv
    have hσ₀ := (cmatch_sound hm₀).1
    have hb := hf σ₀ hm₀
    unfold clauseReq at hb
    cases hrq : cl.req with
    | none => simp [hrq] at hb
    | some t =>
      simp only [hrq, Option.map_eq_some_iff] at hb
      rw [hrq] at hreq
      obtain ⟨r₀, h₀, he⟩ := hb
      have hev' := hev σ₀ t r₀ h₀ hσ₀ (reqOK_some hreq)
      have hvars := sortOfTerm_vars (reqOK_some hreq)
      exact .intro hrq (EvalTerm.congr hev' (fun i hi => hag i (hvars i hi))) (fun he' => by
        rw [he', isTrue_iff.mpr rfl] at he; cases he)

/-! ## Soundness of the evaluation -/

section
set_option linter.unusedSectionVars false
variable (hsc : SortCtx c) (hcc : CClauseCtx c) (hcm : ClauseComplete c)
include hsc hcc hcm

mutual
  /-- **The evaluation is sound**: a result `CExec.evalT` computes for a well-sorted term under a
  well-sorted σ is its `EvalTerm` result. -/
  theorem evalT_sound : ∀ (n : Nat) {σ : Subst} {t : Term} {r : Option GroundTerm}
      {vars : List Srt} {L : List CtorSig} {s : Srt},
      CExec.evalT c n σ t = some r → HeadsOK c L → c.WellSorted vars σ →
      sortOfTerm (c.rhsCtx L) vars t = some s → EvalTerm c σ t r
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [CExec.evalT] at h
    | n + 1, σ, .var i, r, _, _, _, h, _, _, _ => by
      simp only [CExec.evalT, Option.some.injEq] at h; subst h; exact .var
    | n + 1, σ, .dv s l, r, _, _, _, h, _, _, _ => by
      simp only [CExec.evalT, Option.some.injEq] at h; subst h; exact .dv
    | n + 1, σ, .as t i, r, _, _, _, h, _, _, _ => by simp [CExec.evalT] at h
    | n + 1, σ, .inj a b t, r, vars, L, s, h, hL, hσ, ht => by
      simp only [CExec.evalT, Option.map_eq_some_iff] at h
      obtain ⟨r₀, h₀, rfl⟩ := h
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      exact .inj (evalT_sound n h₀ hL hσ ht')
    | n + 1, σ, .app f ts, r, vars, L, s, h, hL, hσ, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      simp only [CExec.evalT, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
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
            by_cases ho : c.isOvl f = true
            · simp only [ho, ↓reduceIte] at hk
              cases has : allSome rs with
              | none =>
                simp only [has, Option.pure_def, Option.some.injEq] at hk
                subst hk
                have := EvalTerm.ovl hc' ho hts (fun vs hv => by rw [has] at hv; cases hv)
                rw [has] at this
                exact this
              | some ws =>
                simp only [has] at hk
                cases hcv : c.fnCover f ws with
                | none =>
                  simp only [hcv, Option.pure_def, Option.some.injEq] at hk
                  subst hk
                  have := EvalTerm.ovl hc' ho hts (fun vs hv => by rw [has] at hv; cases hv; exact hcv)
                  rw [has] at this
                  exact this
                | some kg =>
                  obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
                  have hws := EvalTerms.sorted hsc hts hL hσ hargs has
                  obtain ⟨fn, -, hlook, -, -, -, -, hus⟩ :=
                    OvlLaws.fnCover_fn_ovlF (hsc.ovl.fnFacts hsc.trans) hlo hws hcv
                  simp only [hcv, hlo, Option.map_eq_some_iff] at hk
                  obtain ⟨r₀, hr₀, rfl⟩ := hk
                  exact .ovlFn hc' ho hts has hlo hcv (evalF_sound n hr₀ hlook hus)
            have ho' : c.isOvl f = false := by simpa using ho
            simp only [ho', Bool.false_eq_true, ↓reduceIte] at hk
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
              obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (lookupOvl_none_of hsc ho') hk')
              obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
              have hlook : c.lookupFn f = some fn := by
                rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
              have hvs := EvalTerms.sorted hsc hts hL hσ hargs hall
              exact .call hc' hh' hts hall (evalF_sound n hk hlook hvs) hp'
  theorem evalTs_sound : ∀ (n : Nat) {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}
      {vars : List Srt} {L : List CtorSig} {ss : List Srt},
      CExec.evalTs c n σ ts = some rs → HeadsOK c L → c.WellSorted vars σ →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → EvalTerms c σ ts rs
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [CExec.evalTs] at h
    | n + 1, σ, [], rs, _, _, _, h, _, _, _ => by
      simp only [CExec.evalTs, Option.some.injEq] at h; subst h; exact .nil
    | n + 1, σ, t :: ts, rs, vars, L, ss, h, hL, hσ, hts => by
      simp only [CExec.evalTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, rs', hrs', rfl⟩ := h
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
      exact .cons (evalT_sound n hr hL hσ h1) (evalTs_sound n hrs' hL hσ h2)
  theorem evalF_sound : ∀ (n : Nat) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
      {fn : Fn}, CExec.evalF c n f vs = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      Eval c f vs r
    | 0, _, _, _, _, h, _, _ => by simp [CExec.evalF] at h
    | n + 1, f, vs, r, fn, h, hfn, hvs => by
      simp only [CExec.evalF, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨fn', hfn', h⟩ := h
      rw [hfn] at hfn'
      cases hfn'
      exact firstClause_sound n h hfn hvs (pre := []) rfl (fun _ h => nomatch h)
  /-- The evaluator tries the clauses in order of priority (`byPrio`): where it returns from a
  clause, every clause before it failed, among them every clause of a smaller priority. -/
  theorem firstClause_sound : ∀ (n : Nat) {fn : Fn} {vs : List GroundTerm} {cls : List Clause}
      {r : Option GroundTerm} {f : Sym} {pre : List Clause},
      CExec.firstClause c n vs (c.fnRest fn vs) cls = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      byPrio fn.clauses = pre ++ cls → (∀ cl ∈ pre, Fails c vs cl) → Eval c f vs r
    | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [CExec.firstClause] at h
    | n + 1, fn, vs, [], r, f, pre, h, hfn, hvs, hcls, hpre => by
      have hall : ∀ cl ∈ fn.clauses, Fails c vs cl := fun cl hcl =>
        hpre cl (by rw [← List.append_nil pre, ← hcls]; exact mem_byPrio.mpr hcl)
      simp only [CExec.firstClause, Option.some.injEq] at h
      subst h
      exact .rest hfn hall
    | n + 1, fn, vs, cl :: rest, r, f, pre, h, hfn, hvs, hcls, hpre => by
      have hfnm := (lookupFn_spec hfn).1
      obtain ⟨L, hL, hclk⟩ := hcc fn hfnm
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
        obtain ⟨hreq, hrhs, hensOK, htop, hexs, hpostT⟩ := hclk cl' hcf
        obtain ⟨hσw, hpv⟩ := cmatch_sound hσm
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
          have hprioE : ∀ x ∈ fn.clauses, x.aside = false → x.prio < cl'.prio → Fails c vs x :=
            fun x hx _ hlt => hpre x (byPrio_lt hcls hx (by omega))
          unfold candBody at hres
          split at hres
          · rename_i he
            refine .clause hfn hcf hσw hpv hreqE (Clause.holds_preTop htop σ) hprioE hexs (evalT_sound n hres hL hσw hrhs) (fun t ht => ?_)
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
              exact .ensFails hfn hcf hσw hpv hreqE (Clause.holds_preTop htop σ) hprioE hexs ht (evalT_sound n h₀ hL hσw (reqOK_some hensOK))
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
            obtain ⟨hreq, -⟩ := hclk x hxf
            exact fails_of_false hcm hfnm hxf hvs hreq
              (fun σ t r h hσ ht => evalT_sound n h hL hσ ht) (fun σ hσ => by
                have := List.all_eq_true.mp hall (x, σ, clauseReq c n x σ) (mem_candidates.mpr ⟨hx, hσ, rfl⟩)
                simpa using this)
        · cases h
end

/-- **The predicates' evaluation is sound**: a value `predVal` computes under a well-sorted σ for a
predicate whose terms are well sorted (`condOK`) is the predicate's `Holds` value under every τ
that agrees with σ on the variables. -/
theorem predVal_sound {vars : List Srt} {σ τ : Subst} (hσ : c.WellSorted vars σ)
    (hag : ∀ i < vars.length, σ.lookup i = τ.lookup i) {n k : Nat} :
    ∀ {p : Cond} {b : Bool}, c.condOK vars p = true → predVal c n σ p = some b → Holds c k τ p b
  | .top, b, _, h => by
    simp only [predVal, Option.some.injEq] at h; subst h; exact .top
  | .equals s t u, b, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases he : CExec.evalT c n σ t with
    | none => simp [predVal, he] at h
    | some r =>
      cases he' : CExec.evalT c n σ u with
      | none => simp [predVal, he, he'] at h
      | some r' =>
        simp only [predVal, he, he', Option.some.injEq] at h
        subst h
        exact .equals
          (EvalTerm.congr (evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ ht)
            fun i hi => hag i (sortOfTerm_vars ht i hi))
          (EvalTerm.congr (evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ hu)
            fun i hi => hag i (sortOfTerm_vars hu i hi))
  | .mem s t u, b, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases he : CExec.evalT c n σ t with
    | none => simp [predVal, he] at h
    | some r =>
      cases he' : CExec.evalT c n σ u with
      | none => simp [predVal, he, he'] at h
      | some r' =>
        simp only [predVal, he, he', Option.some.injEq] at h
        subst h
        exact .mem
          (EvalTerm.congr (evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ ht)
            fun i hi => hag i (sortOfTerm_vars ht i hi))
          (EvalTerm.congr (evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ hu)
            fun i hi => hag i (sortOfTerm_vars hu i hi))
  | .and p q, b, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true] at hc
    cases hp : predVal c n σ p with
    | none => simp [predVal, hp] at h
    | some b₁ =>
      cases hq : predVal c n σ q with
      | none => simp [predVal, hp, hq] at h
      | some b₂ =>
        simp only [predVal, hp, hq, Option.some.injEq] at h
        subst h
        exact .and (predVal_sound hσ hag hc.1 hp) (predVal_sound hσ hag hc.2 hq)
  | .bot, _, _, h | .not _, _, _, h | .or _ _, _, _, h | .implies _ _, _, _, h | .ceil _ _, _, _, h
  | .exMatch _ _ _ _ _, _, _, h | .ex _ _, _, _, h | .all _ _, _, _, h => by simp [predVal] at h

end

/-! ## Soundness of the step -/

theorem appVal_true : ∀ {q p : Option Bool}, appVal q p = some true ↔ q = some true ∧ p = some true
  | none, none | none, some false | none, some true | some false, none | some false, some false
  | some false, some true | some true, none | some true, some false | some true, some true => by decide

theorem appVal_false : ∀ {q p : Option Bool}, appVal q p = some false ↔ q = some false ∨ p = some false
  | none, none | none, some false | none, some true | some false, none | some false, some false
  | some false, some true | some true, none | some true, some false | some true, some true => by decide

theorem appVal_ne_none : ∀ {q p : Option Bool}, q ≠ none → p ≠ none → appVal q p ≠ none
  | none, none | none, some false | none, some true | some false, none | some false, some false
  | some false, some true | some true, none | some true, some false | some true, some true => by decide

/-- An `Option Bool` that is neither `none` nor `some true` is `some false`. -/
theorem eq_false_of_ne {b : Option Bool} (h1 : b ≠ none) (h2 : b ≠ some true) : b = some false := by
  match b, h1, h2 with
  | some false, _, _ => rfl
  | none, h, _ => exact absurd rfl h
  | some true, _, h => exact absurd rfl h

theorem ruleMatches_mem {n : Nat} {r : Rule} {x : GroundTerm} {σ : Subst} {b : Option Bool} :
    (σ, b) ∈ ruleMatches c n r x ↔ σ ∈ cmatch c r.vars [r.lhs] [x] ∧ b = matchVal c n r σ := by
  unfold ruleMatches
  rw [List.mem_map]
  constructor
  · rintro ⟨σ', hσ', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hσ', rfl⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩

/-- What a listed successor comes from: a rule r, a match of r whose `requires` and `pre` are
`true`, whose right-hand side evaluates to it, a configuration, and whose `ensures` and `post` are
`true`; every rule of a smaller priority has only match values `some false` at the same fuel. -/
theorem successorsN_mem_ens {n : Nat} {x y : GroundTerm} (hy : y ∈ successorsN c n x) :
    ∃ r ∈ c.rules,
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false) ∧
      ∃ σ, (σ, some true) ∈ ruleMatches c n r x ∧ CExec.evalT c n σ r.rhs = some (some y) ∧
        c.sortOf y = some topCellSort ∧ ensVal c n r σ = some true ∧
        predVal c n σ r.post = some true := by
  unfold successorsN at hy
  dsimp only at hy
  split at hy
  · simp at hy
  · rename_i p hp
    rw [List.min?_eq_some_iff] at hp
    obtain ⟨-, hmin⟩ := hp
    rw [List.mem_flatMap] at hy
    obtain ⟨⟨r, l⟩, hrl, hy⟩ := hy
    obtain ⟨hrl, hpr⟩ := List.mem_filter.mp hrl
    simp only [beq_iff_eq] at hpr
    obtain ⟨hrl, -⟩ := List.mem_filter.mp hrl
    obtain ⟨r₀, hr₀, he⟩ := List.mem_map.mp hrl
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨r₀, hr₀, fun r' hr' hlt σb hσb => ?_, ?_⟩
    · refine Classical.byContradiction fun hne => ?_
      have hin : (r', ruleMatches c n r' x) ∈ (c.rules.map fun r => (r, ruleMatches c n r x)).filter
          fun (_, l) => l.any fun (_, b) => b != some false := by
        refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r', hr', rfl⟩, ?_⟩
        simp only [List.any_eq_true, bne_iff_ne, ne_eq]
        exact ⟨σb, hσb, hne⟩
      have := hmin _ (List.mem_map.mpr ⟨_, hin, rfl⟩)
      simp only at this
      omega
    · rw [List.mem_filterMap] at hy
      obtain ⟨⟨σ, b⟩, hσb, hk⟩ := hy
      simp only at hk
      by_cases hb : b = some true
      · subst hb
        refine ⟨σ, hσb, ?_⟩
        simp only [beq_self_eq_true, ↓reduceIte] at hk
        cases he : CExec.evalT c n σ r₀.rhs with
        | none => rw [he] at hk; cases hk
        | some o =>
          cases o with
          | none => rw [he] at hk; cases hk
          | some y' =>
            rw [he] at hk
            dsimp only at hk
            split at hk
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              cases hk; exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
            · cases hk
      · have : (b == some true) = false := by simpa using hb
        simp [this] at hk

/-- What a listed successor comes from: a rule r, a match of r whose `requires` is `true` and
whose right-hand side evaluates to it, a configuration; every rule of a smaller priority has only
`requires` values `some false` at the same fuel. -/
theorem successorsN_mem {n : Nat} {x y : GroundTerm} (hy : y ∈ successorsN c n x) :
    ∃ r ∈ c.rules,
      (∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false) ∧
      ∃ σ, (σ, some true) ∈ ruleMatches c n r x ∧ CExec.evalT c n σ r.rhs = some (some y) ∧
        c.sortOf y = some topCellSort :=
  let ⟨r, hr, hlow, σ, hσ, he, hs, _, _⟩ := successorsN_mem_ens hy
  ⟨r, hr, hlow, σ, hσ, he, hs⟩

/-- What `sortedOK` checks of a rule's `requires` and right-hand side. -/
theorem ruleSorted_of {r : Rule} (hok : c.sortedOK = true) (hr : r ∈ c.rules) :
    reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req = true ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  have hrule : c.ruleSorted r = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.2 r hr
  have hp := Semantics.ruleSorted_parts c hrule
  exact ⟨hp.2.1, hp.2.2.2⟩

/-- What `sortedOK` checks of a rule's `ensures`. -/
theorem ruleSorted_ens_of {r : Rule} (hok : c.sortedOK = true) (hr : r ∈ c.rules) :
    reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens = true := by
  have hrule : c.ruleSorted r = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.2 r hr
  exact (Semantics.ruleSorted_parts c hrule).2.2.1

theorem patVal_of_patVals {σ : Subst} {p : Term} {v : GroundTerm} (h : PatVals c σ [p] [v]) :
    PatVal c σ p v := by
  cases h with
  | cons h _ => exact h

/-- What `sortedOK` checks of a rule's predicates. -/
theorem ruleSorted_preds_of {r : Rule} (hok : c.sortedOK = true) (hr : r ∈ c.rules) :
    c.condOK r.vars r.pre = true ∧ c.condOK r.vars r.post = true := by
  have hrule : c.ruleSorted r = true := by
    replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    exact hok.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true] at hrule
  exact ⟨hrule.1.1.1.1.1.2, hrule.1.1.1.2⟩

section
variable (hsc : SortCtx c) (hcc : CClauseCtx c) (hcm : ClauseComplete c)
include hsc hcc hcm

/-- A match whose value is `some false` makes the rule's condition fail under every τ that agrees
with it on the variables: its `requires` evaluates to something other than `true`, or its `pre`
is false (`predVal_sound`). -/
theorem ruleReqFails_of_matchVal (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) {n : Nat}
    {σ τ : Subst} (hσ : c.WellSorted r.vars σ) (hag : ∀ i < r.vars.length, σ.lookup i = τ.lookup i)
    (h : matchVal c n r σ = some false) : RuleReqFails c τ r := by
  rcases appVal_false.mp h with hq | hp
  · unfold reqVal at hq
    obtain ⟨hreq', -⟩ := ruleSorted_of hok hr
    cases ht : r.req with
    | none => simp [ht] at hq
    | some t =>
      rw [ht] at hq hreq'
      cases he' : CExec.evalT c n σ t with
      | none => simp [he'] at hq
      | some v =>
        simp only [he', Option.map_some, Option.some.injEq] at hq
        have hts := reqOK_some hreq'
        have hev := evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ hts
        refine RuleReqFails.intro ht (EvalTerm.congr hev (fun i hi => hag i (sortOfTerm_vars hts i hi))) ?_
        intro hv
        rw [hv] at hq
        exact absurd (isTrue_iff.mpr rfl) (by rw [hq]; simp)
  · exact .pre (predVal_sound hsc hcc hcm hσ hag (ruleSorted_preds_of hok hr).1 hp)

/-- A match whose value is `some true` has a `requires` that evaluates to `true` and a `pre` that
holds. -/
theorem req_pre_of_matchVal (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) {n : Nat}
    {σ : Subst} (hσ : c.WellSorted r.vars σ) (h : matchVal c n r σ = some true) :
    (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c r.vars.length σ r.pre true := by
  obtain ⟨hq, hp⟩ := appVal_true.mp h
  refine ⟨fun t ht => ?_, predVal_sound hsc hcc hcm hσ (fun _ _ => rfl) (ruleSorted_preds_of hok hr).1 hp⟩
  obtain ⟨hreq, -⟩ := ruleSorted_of hok hr
  rw [ht] at hreq
  unfold reqVal at hq
  rw [ht] at hq
  cases he' : CExec.evalT c n σ t with
  | none => simp [he'] at hq
  | some v =>
    simp only [he', Option.map_some, Option.some.injEq] at hq
    rw [isTrue_iff.mp hq] at he'
    exact evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ (reqOK_some hreq)

end

/-- **Every successor the executable step lists, at any fuel, is a step's**: it comes from a rule,
a well-sorted match, a `requires` evaluating to `true`, a `pre` that holds, the right-hand side's
result, an `ensures` evaluating to `true` and a `post` that holds, and no rule of a smaller
priority applies. -/
theorem successorsN_sound_preds (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hcm : ClauseComplete c) (hrc : RuleComplete c) {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : y ∈ successorsN c n x.val) :
    ∃ r ∈ c.rules, ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.pre true ∧
      EvalTerm c σ r.rhs (some y) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧
      Holds c r.vars.length σ r.post true ∧ c.sortOf y = some topCellSort ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) := by
  have hsc := sortCtx_of_all hok hsr hov
  have hcc := cclauseCtx_of hok
  obtain ⟨r, hr, hlow, σ, hσm, he, hs, hen, hpo⟩ := successorsN_mem_ens hy
  obtain ⟨hσm, hb⟩ := ruleMatches_mem.mp hσm
  obtain ⟨hσ, hpvs⟩ := cmatch_sound hσm
  obtain ⟨-, hrhs⟩ := ruleSorted_of hok hr
  obtain ⟨hreq, hpre⟩ := req_pre_of_matchVal hsc hcc hcm hok hr hσ hb.symm
  refine ⟨r, hr, σ, hσ, patVal_of_patVals hpvs, hreq, hpre,
    evalT_sound hsc hcc hcm n he Exec.headsOK_fns hσ hrhs, fun t ht => ?_,
    predVal_sound hsc hcc hcm hσ (fun _ _ => rfl) (ruleSorted_preds_of hok hr).2 hpo, hs,
    fun r' hr' hlt τ hτ hpv => ?_⟩
  · have hens := ruleSorted_ens_of hok hr
    rw [ht] at hens
    unfold ensVal at hen
    rw [ht] at hen
    cases he' : CExec.evalT c n σ t with
    | none => simp [he'] at hen
    | some v =>
      simp only [he', Option.map_some, Option.some.injEq] at hen
      rw [isTrue_iff.mp hen] at he'
      exact evalT_sound hsc hcc hcm n he' Exec.headsOK_fns hσ (reqOK_some hens)
  · obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r' hr' x.val τ x.property hτ hpv
    have hσ₀ := (cmatch_sound hσ₀m).1
    exact ruleReqFails_of_matchVal hsc hcc hcm hok hr' hσ₀ hag
      (hlow r' hr' hlt (σ₀, matchVal c n r' σ₀) (ruleMatches_mem.mpr ⟨hσ₀m, rfl⟩))

/-- **Every successor the executable step lists, at any fuel, is a step's**: it comes from a rule,
a well-sorted match, a `requires` evaluating to `true` and the right-hand side's result, and no rule
of a smaller priority applies. -/
theorem successorsN_sound (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hcm : ClauseComplete c) (hrc : RuleComplete c) {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : y ∈ successorsN c n x.val) :
    ∃ r ∈ c.rules, ∃ σ, c.WellSorted r.vars σ ∧ PatVal c σ r.lhs x.val ∧
      (∀ t, r.req = some t → EvalTerm c σ t (some (bool true))) ∧
      EvalTerm c σ r.rhs (some y) ∧
      (∀ t, r.ens = some t → EvalTerm c σ t (some (bool true))) ∧ c.sortOf y = some topCellSort ∧
      (∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val) :=
  let ⟨r, hr, σ, hσ, hpv, hreq, _, hrhs, hens, _, hs, hprio⟩ := successorsN_sound_preds hok hsr hov hcm hrc hy
  ⟨r, hr, σ, hσ, hpv, hreq, hrhs, hens, hs, hprio⟩

/-- Every successor the executable step lists, at any fuel, is a configuration `Step` reaches. -/
theorem successorsN_step (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hcm : ClauseComplete c) (hrc : RuleComplete c) {n : Nat} {x : Config c} {y : GroundTerm}
    (hy : y ∈ successorsN c n x.val) : ∃ h : c.sortOf y = some topCellSort, Step c x ⟨y, h⟩ := by
  obtain ⟨r, hr, σ, hσ, hpv, hreq, hpre, hrhs, hens, hpost, hs, hprio⟩ :=
    successorsN_sound_preds hok hsr hov hcm hrc hy
  exact ⟨hs, .rule r hr σ hσ hpv hreq hpre hrhs hens hpost hprio⟩

/-- `successors` keeps successors of `successorsN` only. -/
theorem mem_of_mem_dedup {y : GroundTerm} : ∀ (l acc : List GroundTerm),
    y ∈ l.foldl (fun acc y => if acc.any (same · y) then acc else acc ++ [y]) acc → y ∈ acc ∨ y ∈ l
  | [], acc, h => .inl h
  | a :: l, acc, h => by
    rw [List.foldl_cons] at h
    rcases mem_of_mem_dedup l _ h with h | h
    · split at h
      · exact .inl h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp h)))
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **The executable step is sound**: every successor `CExec.successors` lists is a `Step`
successor, given the matcher's completeness for the clauses and the rules. -/
theorem successors_step (hok : c.sortedOK = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    (hcm : ClauseComplete c) (hrc : RuleComplete c) {x : Config c} {y : GroundTerm}
    (hy : y ∈ successors c x.val) : ∃ h : c.sortOf y = some topCellSort, Step c x ⟨y, h⟩ := by
  unfold successors at hy
  rcases mem_of_mem_dedup _ [] hy with h | h
  · nomatch h
  · exact successorsN_step hok hsr hov hcm hrc h

/-- `successors_step` from the readiness check. -/
theorem successors_step_of_ready (hr : execReady c = true) (hcm : ClauseComplete c)
    (hrc : RuleComplete c) {x : Config c} {y : GroundTerm} (hy : y ∈ successors c x.val) :
    ∃ h : c.sortOf y = some topCellSort, Step c x ⟨y, h⟩ := by
  have hr' := hr
  simp only [execReady, Bool.and_eq_true] at hr'
  replace hr' := hr'.1
  exact successors_step hr'.1.1.1.1.1 hr'.1.1.1.1.2 (matchCtxO_of hr'.1.1.1.2).ovlCase hcm hrc hy

end KCore.CExec
