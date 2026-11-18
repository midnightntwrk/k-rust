/-
  KCore, checked layer: the executable step of CollExec.lean lists exactly the `Step` successors,
  for some fuel, on a core that `execReady` accepts and whose functions have at most one result at each
  argument list (`FnDet`): `CExec.step_iff`, the statement of `Exec.step_iff_of_ok` (StepIff.lean) for
  `CExec.successorsN`.

  The evaluation's completeness is EvalComplete.lean's, restated for `CExec.evalT` (which calls
  `cmatch`): `evalT_congr`, `evalT_mono` (more fuel gives the same result, under `FnDet`),
  `EvalTerm.exec` (an `EvalTerm` result is computed with some fuel). Where EvalComplete.lean reads
  `Exec`'s matcher, this file reads `cmatch_sound` (every listed match is well sorted and a match)
  and `ClauseComplete` (every well-sorted match agrees on the clause's variables with a listed one,
  `clauseComplete_of_ready`); the clauses' sorts are `CClauseCtx` (`cclauseCtx_of`).
  `step_iff`: `→` as `Exec.step_iff_of_ok`, the rules' matches from `RuleComplete`
  (`ruleComplete_of_ready`); `←` is `successorsN_step_ready`.
-/
import KcoreSpec.CollExecStep
import KcoreSpec.EvalComplete

set_option autoImplicit false

namespace KCore.CExec

open KCore Exec GroundTerm

variable {c : Semantics}

/-- A class of clauses all of whose listed matches have a `requires` `some false` fails. -/
theorem class_fails (hsc : SortCtx c) (hcc : CClauseCtx c) (hcm : ClauseComplete c) {f : Sym}
    {fn : Fn} {vs : List GroundTerm} {n : Nat} {cls : List Clause}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (hin : ∀ x ∈ cls, x ∈ fn.clauses)
    (hall : (candidates c n vs cls).all (·.2.2 == some false) = true) : ∀ x ∈ cls, Fails c vs x := by
  intro x hx
  have hfm := (lookupFn_spec hfn).1
  obtain ⟨L, hL, hclk⟩ := hcc fn hfm
  exact fails_of_false hcm hfm (hin x hx) hvs (hclk x (hin x hx)).1
    (fun σ t r h hσ ht => evalT_sound hsc hcc hcm n h hL hσ ht) (fun σ hσ => by
      have := List.all_eq_true.mp hall (x, σ, clauseReq c n x σ) (mem_candidates.mpr ⟨hx, hσ, rfl⟩)
      simpa using this)

/-! ## The executable evaluation depends on σ only through the term's variables -/

mutual
  theorem evalT_congr : ∀ (n : Nat) {σ σ' : Subst} {t : Term},
      (∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) → CExec.evalT c n σ t = CExec.evalT c n σ' t
    | 0, _, _, _, _ => by simp [CExec.evalT]
    | n + 1, σ, σ', .var i, ha => by simp [CExec.evalT, ha i (by simp [varOccs])]
    | n + 1, _, _, .dv _ _, _ => by simp [CExec.evalT]
    | n + 1, _, _, .as _ _, _ => by simp [CExec.evalT]
    | n + 1, σ, σ', .inj a b t, ha => by
      simp only [CExec.evalT]
      rw [evalT_congr n (fun i hi => ha i (by simpa [varOccs] using hi))]
    | n + 1, σ, σ', .app f ts, ha => by
      simp only [CExec.evalT]
      rw [evalTs_congr n (fun i hi => ha i (by simpa [varOccs] using hi))]
  theorem evalTs_congr : ∀ (n : Nat) {σ σ' : Subst} {ts : List Term},
      (∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i) → CExec.evalTs c n σ ts = CExec.evalTs c n σ' ts
    | 0, _, _, _, _ => by simp [CExec.evalTs]
    | n + 1, _, _, [], _ => by simp [CExec.evalTs]
    | n + 1, σ, σ', t :: ts, ha => by
      simp only [CExec.evalTs]
      rw [evalT_congr n (fun i hi => ha i (by simp [varOccsList, hi])),
        evalTs_congr n (fun i hi => ha i (by simp [varOccsList, hi]))]
end

/-- A predicate's value depends on σ only through the variables, for a predicate whose terms are
well sorted (`condOK`). -/
theorem predVal_congr {vars : List Srt} {n : Nat} {σ σ' : Subst}
    (hag : ∀ i < vars.length, σ.lookup i = σ'.lookup i) :
    ∀ {p : Cond}, c.condOK vars p = true → predVal c n σ p = predVal c n σ' p
  | .top, _ => rfl
  | .equals s t u, hc => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    simp only [predVal]
    rw [evalT_congr n (t := t) (fun i hi => hag i (sortOfTerm_vars ht i hi)),
      evalT_congr n (t := u) (fun i hi => hag i (sortOfTerm_vars hu i hi))]
  | .mem s t u, hc => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    simp only [predVal]
    rw [evalT_congr n (t := t) (fun i hi => hag i (sortOfTerm_vars ht i hi)),
      evalT_congr n (t := u) (fun i hi => hag i (sortOfTerm_vars hu i hi))]
  | .and p q, hc => by
    simp only [Semantics.condOK, Bool.and_eq_true] at hc
    simp only [predVal]
    rw [predVal_congr hag hc.1, predVal_congr hag hc.2]
  | .bot, _ | .not _, _ | .or _ _, _ | .implies _ _, _ | .ceil _ _, _ | .exMatch _ _ _ _ _, _
  | .ex _ _, _ | .all _ _, _ => rfl

theorem candResult_false {n : Nat} {x : Clause} {σ : Subst} (h : clauseReq c n x σ = some false) :
    candResult c n (x, σ, clauseReq c n x σ) = none := by
  unfold candResult; simp [h]

/-- A `requires` computed with some fuel is computed with more, given that its terms are. -/
theorem clauseReq_mono {n : Nat} {cl : Clause} {σ : Subst} {L : List CtorSig} {b : Bool}
    (hreq : reqOK (c.rhsCtx L) cl.vars cl.req = true)
    (hev : ∀ t r, CExec.evalT c n σ t = some r → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool →
      CExec.evalT c (n + 1) σ t = some r)
    (h : clauseReq c n cl σ = some b) : clauseReq c (n + 1) cl σ = some b := by
  unfold clauseReq at h ⊢
  cases hrq : cl.req with
  | none => simpa [hrq] using h
  | some t =>
    simp only [hrq, Option.map_eq_some_iff] at h ⊢
    rw [hrq] at hreq
    obtain ⟨r₀, h₀, he⟩ := h
    exact ⟨r₀, hev t r₀ h₀ (reqOK_some hreq), he⟩

/-- An `ensures` computed with some fuel is computed with more, given that its terms are. -/
theorem clauseEns_mono {n : Nat} {cl : Clause} {σ : Subst} {L : List CtorSig} {b : Bool}
    (hens : reqOK (c.rhsCtx L) cl.vars cl.ens = true)
    (hev : ∀ t r, CExec.evalT c n σ t = some r → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool →
      CExec.evalT c (n + 1) σ t = some r)
    (h : clauseEns c n cl σ = some b) : clauseEns c (n + 1) cl σ = some b := by
  unfold clauseEns at h ⊢
  cases hrq : cl.ens with
  | none => simpa [hrq] using h
  | some t =>
    simp only [hrq, Option.map_eq_some_iff] at h ⊢
    rw [hrq] at hens
    obtain ⟨r₀, h₀, he⟩ := h
    exact ⟨r₀, hev t r₀ h₀ (reqOK_some hens), he⟩

section
set_option linter.unusedSectionVars false
variable (hsc : SortCtx c) (hcc : CClauseCtx c) (hcm : ClauseComplete c) (hfd : FnDet c)
include hsc hcc hcm hfd

/-! ## More fuel gives the same result -/

mutual
  theorem evalT_mono : ∀ (n : Nat) {σ : Subst} {t : Term} {r : Option GroundTerm}
      {vars : List Srt} {L : List CtorSig} {s : Srt},
      CExec.evalT c n σ t = some r → HeadsOK c L → c.WellSorted vars σ →
      sortOfTerm (c.rhsCtx L) vars t = some s → CExec.evalT c (n + 1) σ t = some r
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [CExec.evalT] at h
    | n + 1, σ, .var i, r, _, _, _, h, _, _, _ => by simpa [CExec.evalT] using h
    | n + 1, σ, .dv s l, r, _, _, _, h, _, _, _ => by simpa [CExec.evalT] using h
    | n + 1, σ, .as t i, r, _, _, _, h, _, _, _ => by simp [CExec.evalT] at h
    | n + 1, σ, .inj a b t, r, vars, L, s, h, hL, hσ, ht => by
      simp only [CExec.evalT, Option.map_eq_some_iff] at h ⊢
      obtain ⟨r₀, h₀, rfl⟩ := h
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      exact ⟨r₀, evalT_mono n h₀ hL hσ ht', rfl⟩
    | n + 1, σ, .app f ts, r, vars, L, s, h, hL, hσ, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      simp only [CExec.evalT, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨rs, hrs, hk⟩ := h
      refine ⟨rs, evalTs_mono n hrs hL hσ hargs, ?_⟩
      by_cases hc : c.isCtor f = true
      · simp only [hc, ↓reduceIte] at hk ⊢; exact hk
      · have hc' : c.isCtor f = false := by simpa using hc
        simp only [hc', ↓reduceIte, Bool.false_eq_true] at hk ⊢
        by_cases hh : isHook f = true
        · simp only [hh, ↓reduceIte] at hk ⊢; exact hk
        · have hh' : isHook f = false := by simpa using hh
          simp only [hh', ↓reduceIte, Bool.false_eq_true] at hk ⊢
          by_cases hp : c.isParam f = true
          · simp only [hp, ↓reduceIte] at hk ⊢; exact hk
          · have hp' : c.isParam f = false := by simpa using hp
            simp only [hp', ↓reduceIte, Bool.false_eq_true] at hk ⊢
            by_cases ho : c.isOvl f = true
            · simp only [ho, ↓reduceIte] at hk ⊢
              cases hall : allSome rs with
              | none => simp only [hall] at hk ⊢; exact hk
              | some vs =>
                simp only [hall] at hk ⊢
                cases hcv : c.fnCover f vs with
                | none => simp only [hcv] at hk ⊢; exact hk
                | some kg =>
                  obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
                  have hvs := EvalTerms.sorted hsc (evalTs_sound hsc hcc hcm n hrs hL hσ hargs) hL hσ hargs hall
                  obtain ⟨fn, -, hlook, -, -, -, -, hus⟩ :=
                    OvlLaws.fnCover_fn_ovlF (hsc.ovl.fnFacts hsc.trans) hlo hvs hcv
                  simp only [hcv, hlo, Option.map_eq_some_iff] at hk ⊢
                  obtain ⟨r₀, hr₀, rfl⟩ := hk
                  exact ⟨r₀, evalF_mono n hr₀ hlook hus, rfl⟩
            have ho' : c.isOvl f = false := by simpa using ho
            simp only [ho', ↓reduceIte, Bool.false_eq_true] at hk ⊢
            cases hall : allSome rs with
            | none => simp only [hall] at hk ⊢; exact hk
            | some vs =>
              simp only [hall] at hk ⊢
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
              have hvs := EvalTerms.sorted hsc (evalTs_sound hsc hcc hcm n hrs hL hσ hargs) hL hσ hargs hall
              exact evalF_mono n hk hlook hvs
  theorem evalTs_mono : ∀ (n : Nat) {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}
      {vars : List Srt} {L : List CtorSig} {ss : List Srt},
      CExec.evalTs c n σ ts = some rs → HeadsOK c L → c.WellSorted vars σ →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → CExec.evalTs c (n + 1) σ ts = some rs
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [CExec.evalTs] at h
    | n + 1, σ, [], rs, _, _, _, h, _, _, _ => by simpa [CExec.evalTs] using h
    | n + 1, σ, t :: ts, rs, vars, L, ss, h, hL, hσ, hts => by
      simp only [CExec.evalTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨r, hr, rs', hrs', rfl⟩ := h
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
      exact ⟨r, evalT_mono n hr hL hσ h1, rs', evalTs_mono n hrs' hL hσ h2, rfl⟩
  theorem evalF_mono : ∀ (n : Nat) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
      {fn : Fn}, CExec.evalF c n f vs = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      CExec.evalF c (n + 1) f vs = some r
    | 0, _, _, _, _, h, _, _ => by simp [CExec.evalF] at h
    | n + 1, f, vs, r, fn, h, hfn, hvs => by
      simp only [CExec.evalF, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨fn', hfn', h⟩ := h
      rw [hfn] at hfn'
      cases hfn'
      exact ⟨fn, hfn, firstClause_mono n h hfn hvs (pre := []) rfl (fun _ h => nomatch h)⟩
  theorem firstClause_mono : ∀ (n : Nat) {fn : Fn} {vs : List GroundTerm} {cls : List Clause}
      {r : Option GroundTerm} {f : Sym} {pre : List Clause},
      CExec.firstClause c n vs (c.fnRest fn vs) cls = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      byPrio fn.clauses = pre ++ cls → (∀ cl ∈ pre, Fails c vs cl) →
      CExec.firstClause c (n + 1) vs (c.fnRest fn vs) cls = some r
    | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [CExec.firstClause] at h
    | n + 1, fn, vs, [], r, f, pre, h, _, _, _, _ => by simpa [CExec.firstClause] using h
    | n + 1, fn, vs, cl :: rest, r, f, pre, h, hfn, hvs, hcls, hpre => by
      have hE := firstClause_sound hsc hcc hcm (n + 1) h hfn hvs hcls hpre
      obtain ⟨L, hL, hclk⟩ := hcc fn (lookupFn_spec hfn).1
      have hin : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), x ∈ fn.clauses := fun x hx =>
        mem_byPrio.mp (by rw [hcls]; exact List.mem_append_right _ (List.takeWhile_subset _ hx))
      have hws : ∀ x σ, σ ∈ clauseMatches c x vs → c.WellSorted x.vars σ := fun x σ hσ =>
        (cmatch_sound hσ).1
      have hreqm : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), ∀ σ ∈ clauseMatches c x vs,
          ∀ b, clauseReq c n x σ = some b → clauseReq c (n + 1) x σ = some b := fun x hx σ hσ b hb =>
        clauseReq_mono (hclk x (hin x hx)).1
          (fun t r h ht => evalT_mono n h hL (hws x σ hσ) ht) hb
      rw [firstClause_cons] at h ⊢
      split at h
      · rename_i r' hfind
        injection h with hrr
        subst hrr
        obtain ⟨⟨x, σ, b⟩, hmem, hres⟩ := List.exists_of_findSome?_eq_some hfind
        obtain ⟨hx, hσ, rfl⟩ := mem_candidates.mp hmem
        have hres' : candResult c (n + 1) (x, σ, clauseReq c (n + 1) x σ) = some r' := by
          unfold candResult at hres ⊢
          simp only at hres ⊢
          split at hres
          · rename_i hb
            have hb' : clauseReq c n x σ = some true := by simpa using hb
            rw [hreqm x hx σ hσ true hb']
            simp only [beq_self_eq_true, ↓reduceIte]
            have hem := fun {b : Bool} (he : clauseEns c n x σ = some b) =>
              clauseEns_mono (hclk x (hin x hx)).2.2.1
                (fun t r h ht => evalT_mono n h hL (hws x σ hσ) ht) he
            unfold candBody at hres ⊢
            split at hres
            · rename_i he
              rw [hem he]
              exact evalT_mono n hres hL (hws x σ hσ) (hclk x (hin x hx)).2.1
            · rename_i he
              rw [hem he]
              exact hres
            · cases hres
          · cases hres
        cases hf : (candidates c (n + 1) vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome?
            (candResult c (n + 1)) with
        | none =>
          exact absurd (List.findSome?_eq_none_iff.mp hf _ (mem_candidates.mpr ⟨hx, hσ, rfl⟩))
            (by rw [hres']; simp)
        | some r'' =>
          have hE' : Eval c f vs r'' := firstClause_sound hsc hcc hcm (n + 2)
            (by rw [firstClause_cons, hf]) hfn hvs hcls hpre
          simp only [hfd _ _ _ _ hE' hE]
      · split at h
        · rename_i hnone hall
          have hfalse : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), ∀ σ ∈ clauseMatches c x vs,
              clauseReq c (n + 1) x σ = some false := fun x hx σ hσ => by
            have := List.all_eq_true.mp hall (x, σ, clauseReq c n x σ) (mem_candidates.mpr ⟨hx, hσ, rfl⟩)
            exact hreqm x hx σ hσ false (by simpa using this)
          have hnone' : (candidates c (n + 1) vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome?
              (candResult c (n + 1)) = none :=
            List.findSome?_eq_none_iff.mpr fun ⟨x, σ, b⟩ hm => by
              obtain ⟨hx, hσ, rfl⟩ := mem_candidates.mp hm
              exact candResult_false (hfalse x hx σ hσ)
          have hall' : (candidates c (n + 1) vs ((cl :: rest).takeWhile (·.prio == cl.prio))).all
              (·.2.2 == some false) = true :=
            List.all_eq_true.mpr fun ⟨x, σ, b⟩ hm => by
              obtain ⟨hx, hσ, rfl⟩ := mem_candidates.mp hm
              simp [hfalse x hx σ hσ]
          rw [hnone']
          simp only [hall', ↓reduceIte]
          refine firstClause_mono n h hfn hvs
            (pre := pre ++ (cl :: rest).takeWhile (·.prio == cl.prio))
            (by rw [hcls, List.append_assoc, List.takeWhile_append_dropWhile]) (fun x hx => ?_)
          rcases List.mem_append.mp hx with hx | hx
          · exact hpre x hx
          · exact class_fails hsc hcc hcm hfn hvs hin hall x hx
        · cases h
end

theorem evalT_mono_le {n m : Nat} (hle : n ≤ m) {σ : Subst} {t : Term} {r : Option GroundTerm}
    {vars : List Srt} {L : List CtorSig} {s : Srt} (h : CExec.evalT c n σ t = some r) (hL : HeadsOK c L)
    (hσ : c.WellSorted vars σ) (ht : sortOfTerm (c.rhsCtx L) vars t = some s) : CExec.evalT c m σ t = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalT_mono hsc hcc hcm hfd _ ih hL hσ ht

/-- More fuel gives a predicate the same value. -/
theorem predVal_mono_le {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) :
    ∀ {p : Cond} {n m : Nat} {b : Bool}, n ≤ m → c.condOK vars p = true → predVal c n σ p = some b →
      predVal c m σ p = some b
  | .top, _, _, _, _, _, h => by simpa [predVal] using h
  | .equals s t u, n, m, b, hle, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases he : CExec.evalT c n σ t with
    | none => simp [predVal, he] at h
    | some r =>
      cases he' : CExec.evalT c n σ u with
      | none => simp [predVal, he, he'] at h
      | some r' =>
        simp only [predVal, he, he'] at h
        simp only [predVal, evalT_mono_le hsc hcc hcm hfd hle he Exec.headsOK_fns hσ ht,
          evalT_mono_le hsc hcc hcm hfd hle he' Exec.headsOK_fns hσ hu]
        exact h
  | .mem s t u, n, m, b, hle, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases he : CExec.evalT c n σ t with
    | none => simp [predVal, he] at h
    | some r =>
      cases he' : CExec.evalT c n σ u with
      | none => simp [predVal, he, he'] at h
      | some r' =>
        simp only [predVal, he, he'] at h
        simp only [predVal, evalT_mono_le hsc hcc hcm hfd hle he Exec.headsOK_fns hσ ht,
          evalT_mono_le hsc hcc hcm hfd hle he' Exec.headsOK_fns hσ hu]
        exact h
  | .and p q, n, m, b, hle, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true] at hc
    cases hp : predVal c n σ p with
    | none => simp [predVal, hp] at h
    | some b₁ =>
      cases hq : predVal c n σ q with
      | none => simp [predVal, hp, hq] at h
      | some b₂ =>
        simp only [predVal, hp, hq] at h
        simp only [predVal, predVal_mono_le hσ hle hc.1 hp, predVal_mono_le hσ hle hc.2 hq]
        exact h
  | .bot, _, _, _, _, _, h | .not _, _, _, _, _, _, h | .or _ _, _, _, _, _, _, h
  | .implies _ _, _, _, _, _, _, h | .ceil _ _, _, _, _, _, _, h | .exMatch _ _ _ _ _, _, _, _, _, _, h
  | .ex _ _, _, _, _, _, _, h | .all _ _, _, _, _, _, _, h => by simp [predVal] at h

theorem evalTs_mono_le {n m : Nat} (hle : n ≤ m) {σ : Subst} {ts : List Term}
    {rs : List (Option GroundTerm)} {vars : List Srt} {L : List CtorSig} {ss : List Srt}
    (h : CExec.evalTs c n σ ts = some rs) (hL : HeadsOK c L) (hσ : c.WellSorted vars σ)
    (hts : sortsOfTerms (c.rhsCtx L) vars ts = some ss) : CExec.evalTs c m σ ts = some rs := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalTs_mono hsc hcc hcm hfd _ ih hL hσ hts

theorem evalF_mono_le {n m : Nat} (hle : n ≤ m) {f : Sym} {vs : List GroundTerm}
    {r : Option GroundTerm} {fn : Fn} (h : CExec.evalF c n f vs = some r) (hfn : c.lookupFn f = some fn)
    (hvs : c.sortsOf vs = some fn.args) : CExec.evalF c m f vs = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalF_mono hsc hcc hcm hfd _ ih hfn hvs

theorem clauseReq_mono_le {n m : Nat} (hle : n ≤ m) {fn : Fn} {cl : Clause} {σ : Subst} {b : Bool}
    (hfn : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (h : clauseReq c n cl σ = some b) : clauseReq c m cl σ = some b := by
  obtain ⟨L, hL, hclk⟩ := hcc fn hfn
  induction hle with
  | refl => exact h
  | step _ ih =>
    exact clauseReq_mono (hclk cl hcl).1 (fun t r h ht => evalT_mono hsc hcc hcm hfd _ h hL hσ ht) ih

/-! ## Completeness of the executable evaluation -/

/-- Every match the matcher lists of the clause has, with enough fuel, a `requires` that is not
`true`: the clause is passed. -/
def SkipFuel (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∃ m₀, ∀ m, m₀ ≤ m → ∀ σ ∈ clauseMatches c cl vs, clauseReq c m cl σ = some false

/-- Some match the matcher lists of the clause has, with enough fuel, a `requires` that is `true`
and a result (its `ensures` and, where that is `true`, its right-hand side have results): the
clause gives one. -/
def ApplyFuel (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∃ σ ∈ clauseMatches c cl vs, ∃ m₀, ∀ m, m₀ ≤ m →
    clauseReq c m cl σ = some true ∧ ∃ r, candResult c m (cl, σ, some true) = some r

omit hsc hcc hcm hfd in
/-- The clauses of a sorted list are tried a priority at a time: where every clause of a smaller
priority than p is passed and some clause of priority p gives a result, or every clause is passed,
the evaluation has a result with enough fuel. -/
theorem firstClause_some {vs : List GroundTerm} {fr : Option GroundTerm} {p : Nat} : ∀ (k : Nat) (l : List Clause),
    l.length ≤ k → l.Pairwise (fun a b => a.prio ≤ b.prio) →
    (∀ x ∈ l, x.prio < p → SkipFuel c vs x) →
    ((∃ x ∈ l, x.prio = p ∧ ApplyFuel c vs x) ∨ ∀ x ∈ l, SkipFuel c vs x) →
    ∃ M, ∀ m, M ≤ m → ∃ r, CExec.firstClause c m vs fr l = some r
  | _, [], _, _, _, _ => ⟨1, fun m hm => ⟨fr, by
      cases m with
      | zero => omega
      | succ m => rfl⟩⟩
  | 0, _ :: _, hk, _, _, _ => by simp at hk
  | k + 1, cl :: rest, hk, hs, hlow, hcase => by
    have hsplit := List.takeWhile_append_dropWhile (p := (·.prio == cl.prio)) (l := cl :: rest)
    have hcl : cl ∈ (cl :: rest).takeWhile (·.prio == cl.prio) := by simp [List.takeWhile_cons]
    have hlen : ((cl :: rest).dropWhile (·.prio == cl.prio)).length ≤ k := by
      have h1 := congrArg List.length hsplit
      rw [List.length_append] at h1
      have h2 := List.length_pos_of_mem hcl
      simp only [List.length_cons] at hk h1
      omega
    have hsub : ∀ x ∈ (cl :: rest).dropWhile (·.prio == cl.prio), x ∈ cl :: rest := fun x hx =>
      (List.dropWhile_suffix (l := cl :: rest) (·.prio == cl.prio)).subset hx
    have hs' := hs.sublist (List.dropWhile_suffix (l := cl :: rest) (·.prio == cl.prio)).sublist
    have hhead : ∀ x ∈ cl :: rest, cl.prio ≤ x.prio := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_refl _
      · exact (List.pairwise_cons.mp hs).1 x hx
    -- the first priority's clauses all passed: the evaluation goes on to the next priority
    have skip : (∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), SkipFuel c vs x) →
        ((∃ x ∈ (cl :: rest).dropWhile (·.prio == cl.prio), x.prio = p ∧ ApplyFuel c vs x) ∨
          ∀ x ∈ (cl :: rest).dropWhile (·.prio == cl.prio), SkipFuel c vs x) →
        ∃ M, ∀ m, M ≤ m → ∃ r, CExec.firstClause c m vs fr (cl :: rest) = some r := by
      intro hsk hcase'
      obtain ⟨M, hM⟩ := fuel_max (l := (cl :: rest).takeWhile (·.prio == cl.prio)) hsk
      obtain ⟨M', hM'⟩ := firstClause_some k _ hlen hs' (fun x hx => hlow x (hsub x hx)) hcase'
      refine ⟨max M M' + 1, fun m hm => ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨r, hr⟩ := hM' m' (by omega)
      refine ⟨r, ?_⟩
      have hfalse : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), ∀ σ ∈ clauseMatches c x vs,
          clauseReq c m' x σ = some false := fun x hx => hM x hx m' (by omega)
      have hnone : (candidates c m' vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome?
          (candResult c m') = none :=
        List.findSome?_eq_none_iff.mpr fun ⟨x, σ, b⟩ hm => by
          obtain ⟨hx, hσ, rfl⟩ := mem_candidates.mp hm
          exact candResult_false (hfalse x hx σ hσ)
      have hall : (candidates c m' vs ((cl :: rest).takeWhile (·.prio == cl.prio))).all
          (·.2.2 == some false) = true :=
        List.all_eq_true.mpr fun ⟨x, σ, b⟩ hm => by
          obtain ⟨hx, hσ, rfl⟩ := mem_candidates.mp hm
          simp [hfalse x hx σ hσ]
      rw [firstClause_cons, hnone]
      simp only [hall, ↓reduceIte]
      exact hr
    have inDrop : ∀ x ∈ cl :: rest, x.prio ≠ cl.prio → x ∈ (cl :: rest).dropWhile (·.prio == cl.prio) :=
      fun x hx hne => by
        rw [← hsplit] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact absurd (prio_of_mem_takeWhile hx) hne
        · exact hx
    rcases hcase with ⟨x, hx, hxp, hxa⟩ | hall
    · rcases Nat.lt_trichotomy cl.prio p with hlt | heq | hgt
      · exact skip (fun y hy => hlow y (List.takeWhile_subset _ hy) (by rw [prio_of_mem_takeWhile hy]; exact hlt))
          (.inl ⟨x, inDrop x hx (by omega), hxp, hxa⟩)
      · -- the clause of priority p is among the first priority's
        have hxt := mem_takeWhile_of_sorted (p := cl.prio) hs (fun a ha => by cases ha; rfl) hx (by omega)
        obtain ⟨σ, hσ, m₀, hm₀⟩ := hxa
        refine ⟨m₀ + 1, fun m hm => ?_⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        obtain ⟨hq, r, hr⟩ := hm₀ m' (by omega)
        have hres : candResult c m' (x, σ, clauseReq c m' x σ) = some r := by
          rw [hq]; exact hr
        cases hf : (candidates c m' vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome?
            (candResult c m') with
        | none =>
          exact absurd (List.findSome?_eq_none_iff.mp hf _ (mem_candidates.mpr ⟨hxt, hσ, rfl⟩))
            (by rw [hres]; simp)
        | some r' => exact ⟨r', by rw [firstClause_cons, hf]⟩
      · exact absurd (hhead x hx) (by omega)
    · exact skip (fun y hy => hall y (List.takeWhile_subset _ hy))
        (.inr fun y hy => hall y (hsub y hy))

/-! The derivations are mutual and `Fails` quantifies over substitutions, so the proof uses the
recursor (`Eval.rec`, `EvalTerm.rec`) with one motive per relation; each case is a lemma below. -/

/-- What each relation's derivation gives: some fuel computes it. -/
def M1 (c : Semantics) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ fn, c.lookupFn f = some fn → c.sortsOf vs = some fn.args → ∃ n, CExec.evalF c n f vs = some r
def M2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ fn f, c.lookupFn f = some fn → cl ∈ fn.clauses → c.sortsOf vs = some fn.args → SkipFuel c vs cl
def M3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  ∀ L, HeadsOK c L → c.WellSorted cl.vars σ → reqOK (c.rhsCtx L) cl.vars cl.req = true →
    cl.pre = .top →
    ∃ t r n, cl.req = some t ∧ CExec.evalT c n σ t = some r ∧ r ≠ some (bool true)
def M4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ vars L s, HeadsOK c L → c.WellSorted vars σ → sortOfTerm (c.rhsCtx L) vars t = some s →
    ∃ n, CExec.evalT c n σ t = some r
def M5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  ∀ vars L ss, HeadsOK c L → c.WellSorted vars σ → sortsOfTerms (c.rhsCtx L) vars ts = some ss →
    ∃ n, CExec.evalTs c n σ ts = some rs

/-- Where the evaluation of `byPrio fn.clauses` has a result with enough fuel, it is the derived
result `r`. -/
theorem evalF_of_some {f : Sym} {fn : Fn} {vs : List GroundTerm} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (hE : Eval c f vs r)
    (h : ∃ M, ∀ m, M ≤ m → ∃ r, CExec.firstClause c m vs (c.fnRest fn vs) (byPrio fn.clauses) = some r) :
    ∃ n, CExec.evalF c n f vs = some r := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨r', hr'⟩ := hM M (Nat.le_refl _)
  have hev : CExec.evalF c (M + 1) f vs = some r' := by
    simp only [CExec.evalF, hfn, Option.bind_eq_bind, Option.bind_some, hr']
  have hE' := evalF_sound hsc hcc hcm (M + 1) hev hfn hvs
  exact ⟨M + 1, by rw [hev, hfd _ _ _ _ hE' hE]⟩

theorem case_clause {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {r : Option GroundTerm} (hfn' : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl')
    (hrhs : EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)))
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → M2 c vs cl')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihrhs : M4 c σ cl.rhs r)
    (ihens : ∀ t, cl.ens = some t → M4 c σ t (some (bool true))) : M1 c f vs r := by
  intro fn₀ hfn hvs
  rw [hfn] at hfn'
  cases hfn'
  have hfm := (lookupFn_spec hfn).1
  obtain ⟨L, hL, hclk⟩ := hcc fn hfm
  obtain ⟨hrq, hrt, hensOK, _⟩ := hclk cl hmem
  obtain ⟨σ₀, hm₀, hag₀⟩ := hcm fn hfm cl hmem vs σ hvs (hσ.at _) hmatch
  have hag : ∀ t m, (∀ i ∈ varOccs t, i < cl.vars.length) → CExec.evalT c m σ₀ t = CExec.evalT c m σ t :=
    fun t m hv => evalT_congr m (fun i hi => hag₀ i (hv i hi))
  obtain ⟨nq, hnq⟩ : ∃ nq, ∀ m, nq ≤ m → clauseReq c m cl σ₀ = some true := by
    cases hreqc : cl.req with
    | none => exact ⟨0, fun m _ => by unfold clauseReq; rw [hreqc]⟩
    | some t =>
      rw [hreqc] at hrq
      obtain ⟨n, hn⟩ := ihreq t hreqc cl.vars L Srt.bool hL hσ (reqOK_some hrq)
      refine ⟨n, fun m hm => ?_⟩
      unfold clauseReq
      rw [hreqc]
      simp only
      rw [hag t m (sortOfTerm_vars (reqOK_some hrq)),
        evalT_mono_le hsc hcc hcm hfd hm hn hL hσ (reqOK_some hrq)]
      simp [isTrue_iff]
  obtain ⟨ne, hne⟩ : ∃ ne, ∀ m, ne ≤ m → clauseEns c m cl σ₀ = some true := by
    cases hensc : cl.ens with
    | none => exact ⟨0, fun m _ => by unfold clauseEns; rw [hensc]⟩
    | some t =>
      rw [hensc] at hensOK
      obtain ⟨n, hn⟩ := ihens t hensc cl.vars L Srt.bool hL hσ (reqOK_some hensOK)
      refine ⟨n, fun m hm => ?_⟩
      unfold clauseEns
      rw [hensc]
      simp only
      rw [hag t m (sortOfTerm_vars (reqOK_some hensOK)),
        evalT_mono_le hsc hcc hcm hfd hm hn hL hσ (reqOK_some hensOK)]
      simp [isTrue_iff]
  obtain ⟨nr, hnr⟩ := ihrhs cl.vars L fn.result hL hσ hrt
  have happ : ApplyFuel c vs cl :=
    ⟨σ₀, hm₀, max (max nq nr) ne, fun m hm =>
      ⟨hnq m (by omega), r, by
        unfold candResult candBody
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [hne m (by omega)]
        show CExec.evalT c m σ₀ cl.rhs = some r
        rw [hag cl.rhs m (sortOfTerm_vars hrt)]
        exact evalT_mono_le hsc hcc hcm hfd (by omega : nr ≤ m) hnr hL hσ hrt⟩⟩
  refine evalF_of_some hsc hcc hcm hfd hfn hvs (.clause hfn hmem hσ hmatch hreq hpre (fun cl' h _ hlt => hprio cl' h hlt)
      (hcc.plainCl hfm hmem).1 hrhs hens (Clause.holds_postTop (hcc.plainCl hfm hmem).2 σ))
    (firstClause_some (p := cl.prio) _ _ (Nat.le_refl _) (pairwise_byPrio _)
      (fun x hx hlt => ihprio x (mem_byPrio.mp hx) hlt fn f hfn (mem_byPrio.mp hx) hvs)
      (.inl ⟨cl, mem_byPrio.mpr hmem, rfl, happ⟩))

theorem case_ensFails {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {t : Term} {w : Option GroundTerm} (hfn' : c.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c cl.vars.length σ cl.pre true)
    (hprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl')
    (ht : cl.ens = some t) (he : EvalTerm c σ t w) (hw : w ≠ some (bool true))
    (ihprio : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → M2 c vs cl')
    (ihreq : ∀ t, cl.req = some t → M4 c σ t (some (bool true)))
    (ihe : M4 c σ t w) : M1 c f vs none := by
  intro fn₀ hfn hvs
  rw [hfn] at hfn'
  cases hfn'
  have hfm := (lookupFn_spec hfn).1
  obtain ⟨L, hL, hclk⟩ := hcc fn hfm
  obtain ⟨hrq, hrt, hensOK, _⟩ := hclk cl hmem
  obtain ⟨σ₀, hm₀, hag₀⟩ := hcm fn hfm cl hmem vs σ hvs (hσ.at _) hmatch
  have hag : ∀ t m, (∀ i ∈ varOccs t, i < cl.vars.length) → CExec.evalT c m σ₀ t = CExec.evalT c m σ t :=
    fun t m hv => evalT_congr m (fun i hi => hag₀ i (hv i hi))
  obtain ⟨nq, hnq⟩ : ∃ nq, ∀ m, nq ≤ m → clauseReq c m cl σ₀ = some true := by
    cases hreqc : cl.req with
    | none => exact ⟨0, fun m _ => by unfold clauseReq; rw [hreqc]⟩
    | some t =>
      rw [hreqc] at hrq
      obtain ⟨n, hn⟩ := ihreq t hreqc cl.vars L Srt.bool hL hσ (reqOK_some hrq)
      refine ⟨n, fun m hm => ?_⟩
      unfold clauseReq
      rw [hreqc]
      simp only
      rw [hag t m (sortOfTerm_vars (reqOK_some hrq)),
        evalT_mono_le hsc hcc hcm hfd hm hn hL hσ (reqOK_some hrq)]
      simp [isTrue_iff]
  rw [ht] at hensOK
  obtain ⟨ne, hne⟩ := ihe cl.vars L Srt.bool hL hσ (reqOK_some hensOK)
  have hef : ∀ m, ne ≤ m → clauseEns c m cl σ₀ = some false := fun m hm => by
    unfold clauseEns
    rw [ht]
    simp only
    rw [hag t m (sortOfTerm_vars (reqOK_some hensOK)),
      evalT_mono_le hsc hcc hcm hfd hm hne hL hσ (reqOK_some hensOK)]
    simp only [Option.map_some, Option.some.injEq]
    cases hb : isTrue w
    · rfl
    · exact absurd (isTrue_iff.mp hb) hw
  have happ : ApplyFuel c vs cl :=
    ⟨σ₀, hm₀, max nq ne, fun m hm =>
      ⟨hnq m (by omega), none, by
        unfold candResult candBody
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [hef m (by omega)]⟩⟩
  refine evalF_of_some hsc hcc hcm hfd hfn hvs (.ensFails hfn hmem hσ hmatch hreq hpre (fun cl' h _ hlt => hprio cl' h hlt)
      (hcc.plainCl hfm hmem).1 ht he hw)
    (firstClause_some (p := cl.prio) _ _ (Nat.le_refl _) (pairwise_byPrio _)
      (fun x hx hlt => ihprio x (mem_byPrio.mp hx) hlt fn f hfn (mem_byPrio.mp hx) hvs)
      (.inl ⟨cl, mem_byPrio.mpr hmem, rfl, happ⟩))

theorem case_rest {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hfn' : c.lookupFn f = some fn) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl)
    (ihnone : ∀ cl ∈ fn.clauses, M2 c vs cl) : M1 c f vs (c.fnRest fn vs) := by
  intro fn hfn hvs
  rw [hfn] at hfn'
  cases hfn'
  exact evalF_of_some hsc hcc hcm hfd hfn hvs (.rest hfn hnone)
    (firstClause_some (p := 0) _ _ (Nat.le_refl _) (pairwise_byPrio _) (fun _ _ h => nomatch h)
      (.inr fun x hx => ihnone x (mem_byPrio.mp hx) fn f hfn (mem_byPrio.mp hx) hvs))

theorem case_fails {vs : List GroundTerm} {cl : Clause}
    (ih : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs → M3 c σ cl) : M2 c vs cl := by
  intro fn f hfn hmem hvs
  have hfm := (lookupFn_spec hfn).1
  obtain ⟨L, hL, hclk⟩ := hcc fn hfm
  obtain ⟨hreq, -, -, htop, -⟩ := hclk cl hmem
  obtain ⟨N, hN⟩ := fuel_max (P := fun m σ => clauseReq c m cl σ = some false)
    (l := clauseMatches c cl vs) (fun σ hσ => by
      obtain ⟨hσw, hpv⟩ := cmatch_sound hσ
      obtain ⟨t, r, n, ht, hn, hr⟩ := ih σ (hσw.at _) hpv L hL hσw hreq htop
      have h0 : clauseReq c n cl σ = some false := by
        unfold clauseReq
        rw [ht]
        simp only [hn, Option.map_some, Option.some.injEq]
        cases hb : isTrue r
        · rfl
        · exact absurd (isTrue_iff.mp hb) hr
      exact ⟨n, fun m hm => clauseReq_mono_le hsc hcc hcm hfd hm hfm hmem hσw h0⟩)
  exact ⟨N, fun m hm σ hσ => hN σ hσ m hm⟩

theorem case_reqFails {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
    (ht : cl.req = some t) (hr : r ≠ some (bool true)) (ihe : M4 c σ t r) : M3 c σ cl := by
  intro L hL hσ hreq _
  rw [ht] at hreq
  obtain ⟨n, hn⟩ := ihe cl.vars L Srt.bool hL hσ (reqOK_some hreq)
  exact ⟨t, r, n, ht, hn, hr⟩

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hts : EvalTerms c σ ts rs) (hvs : allSome rs = some vs) (hev : Eval c f vs r) (hp : c.isParam f = false)
    (ihts : M5 c σ ts rs) (ihf : M1 c f vs r) : M4 c σ (.app f ts) r := by
  have ho := Eval.isOvl_false hev
  intro vars L s hL hσ ht
  obtain ⟨k, hk', hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n₁, hn₁⟩ := ihts vars L k.args hL hσ hargs
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc,
    lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk'
  obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (lookupOvl_none_of hsc ho) hk')
  obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
  have hlook : c.lookupFn f = some fn := by
    rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
  have hvsS := EvalTerms.sorted hsc hts hL hσ hargs hvs
  obtain ⟨n₂, hn₂⟩ := ihf fn hlook hvsS
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [CExec.evalT, evalTs_mono_le hsc hcc hcm hfd (Nat.le_max_left _ _) hn₁ hL hσ hargs, hk, hhk, hp,
    hvs, evalF_mono_le hsc hcc hcm hfd (Nat.le_max_right _ _) hn₂ hlook hvsS, Option.bind_eq_bind,
    Option.bind_some, Bool.false_eq_true, ↓reduceIte, ho]

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r) (hund : allSome rs = none → r = none)
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  refine ⟨n + 1, ?_⟩
  simp only [CExec.evalT, hn, hk, hhk, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true,
    ↓reduceIte]
  cases hall : allSome rs with
  | none => simp [hund hall]
  | some vs => exact hh vs hall

theorem case_param {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false) (hp : c.isParam f = true)
    (hr : r = (allSome rs).bind (c.paramVal f)) (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  refine ⟨n + 1, ?_⟩
  simp only [CExec.evalT, hn, hk, hhk, hp, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true,
    ↓reduceIte, Option.pure_def, hr]

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (.ctor f)) := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  exact ⟨n + 1, by simp [CExec.evalT, hn, hk]⟩

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) none := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  refine ⟨n + 1, ?_⟩
  cases ho : c.isOvl f <;> simp [CExec.evalT, hn, hk, hhk, hp, hvs, ho]

theorem case_ovl {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true)
    (hnf : ∀ vs, allSome rs = some vs → c.fnCover f vs = none) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (c.norm f)) := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  obtain ⟨-, hhk, hp, -, -⟩ := c.isOvl_parts ho
  refine ⟨n + 1, ?_⟩
  cases hall : allSome rs with
  | none => simp [CExec.evalT, hn, hk, hhk, hp, ho, hall]
  | some vs => simp [CExec.evalT, hn, hk, hhk, hp, ho, hall, hnf vs hall]

/-- An overloading symbol at values a function it overloads covers: the fuel of the arguments and
of the function's evaluation at the stripped arguments. -/
theorem case_ovlFn {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {o : OvlSig} {kg : CtorSig} {r : Option GroundTerm}
    (hk : c.isCtor f = false) (ho : c.isOvl f = true) (hts : EvalTerms c σ ts rs)
    (hvs : allSome rs = some vs) (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f vs = some kg)
    (ihts : M5 c σ ts rs) (ihf : M1 c kg.name (stripAll kg.args o.sig.args vs) r) :
    M4 c σ (.app f ts) (r.map (lift kg.result o.sig.result)) := by
  intro vars L s hL hσ ht
  obtain ⟨k, hk', hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n₁, hn₁⟩ := ihts vars L k.args hL hσ hargs
  obtain ⟨-, hhk, hp, -, -⟩ := c.isOvl_parts ho
  have hvsS := EvalTerms.sorted hsc hts hL hσ hargs hvs
  obtain ⟨o', hlo', hko⟩ := rhs_lookup_ovl hsc hL hk' ho
  rw [hlo] at hlo'
  cases hlo'
  rw [hko] at hvsS
  obtain ⟨fn, -, hlook, -, -, -, -, hus⟩ := OvlLaws.fnCover_fn_ovlF (hsc.ovl.fnFacts hsc.trans) hlo hvsS hcov
  obtain ⟨n₂, hn₂⟩ := ihf fn hlook hus
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [CExec.evalT, evalTs_mono_le hsc hcc hcm hfd (Nat.le_max_left _ _) hn₁ hL hσ hargs, hk, hhk, hp, ho,
    hvs, hcov, hlo, evalF_mono_le hsc hcc hcm hfd (Nat.le_max_right _ _) hn₂ hlook hus, Option.bind_eq_bind,
    Option.bind_some, Bool.false_eq_true, ↓reduceIte, Option.map_some]

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (ih : M4 c σ t r) :
    M4 c σ (.inj a b t) (r.map (injNormal a b)) := by
  intro vars L s hL hσ ht
  obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
  obtain ⟨n, hn⟩ := ih vars L a hL hσ ht'
  exact ⟨n + 1, by simp [CExec.evalT, hn]⟩

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : M4 c σ t r) (ih2 : M5 c σ ts rs) : M5 c σ (t :: ts) (r :: rs) := by
  intro vars L ss hL hσ hts
  obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
  obtain ⟨n₁, hn₁⟩ := ih1 vars L s hL hσ h1
  obtain ⟨n₂, hn₂⟩ := ih2 vars L ss' hL hσ h2
  exact ⟨max n₁ n₂ + 1, by
    simp [CExec.evalTs, evalT_mono_le hsc hcc hcm hfd (Nat.le_max_left _ _) hn₁ hL hσ h1,
      evalTs_mono_le hsc hcc hcm hfd (Nat.le_max_right _ _) hn₂ hL hσ h2]⟩

/-- An `EvalTerm` result is computed with some fuel, where no clause is `aside`. -/
theorem EvalTerm.exec (hna : c.AsideFree) {σ : Subst} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
    M4 c σ t r :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ hrhs hens _ ihreq _ ihprio ihrhs ihens _ =>
      case_clause hsc hcc hcm hfd hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        hrhs hens (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihrhs ihens)
    (fun hfn hnone ihnone => case_rest hsc hcc hcm hfd hfn hnone ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ ht he hw ihreq _ ihprio ihe =>
      case_ensFails hsc hcc hcm hfd hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        ht he hw (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihe)
    (fun hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun _ ih => case_fails hsc hcc hcm hfd ih)
    (fun ht _ hr ihe => case_reqFails hsc hcc hcm hfd ht hr ihe)
    (fun h _ => by intro _ _ _ _ htop; rw [htop] at h; exact absurd h.top_eq (by simp))
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ ih => case_inj hsc hcc hcm hfd ih)
    (fun hk _ ihts => case_ctor hsc hcc hcm hfd hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hsc hcc hcm hfd hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hsc hcc hcm hfd hk hhk hp hr ihts)
    (fun hk hhk hts hvs hev hp ihts ihf => case_call hsc hcc hcm hfd hk hhk hts hvs hev hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hsc hcc hcm hfd hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hsc hcc hcm hfd hk ho hnf ihts)
    (fun hk ho hts hvs hlo hcov _ ihts ihf => case_ovlFn hsc hcc hcm hfd hk ho hts hvs hlo hcov ihts ihf)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ ih1 ih2 => case_cons hsc hcc hcm hfd ih1 ih2)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h

/-- A function's `Eval` result is computed by the executable evaluation with some fuel, at
arguments of its argument sorts, where no clause is `aside`. -/
theorem Eval.exec (hna : c.AsideFree) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c f vs r) :
    M1 c f vs r :=
  Eval.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ hrhs hens _ ihreq _ ihprio ihrhs ihens _ =>
      case_clause hsc hcc hcm hfd hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        hrhs hens (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihrhs ihens)
    (fun hfn hnone ihnone => case_rest hsc hcc hcm hfd hfn hnone ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ ht he hw ihreq _ ihprio ihe =>
      case_ensFails hsc hcc hcm hfd hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        ht he hw (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihe)
    (fun hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun _ ih => case_fails hsc hcc hcm hfd ih)
    (fun ht _ hr ihe => case_reqFails hsc hcc hcm hfd ht hr ihe)
    (fun h _ => by intro _ _ _ _ htop; rw [htop] at h; exact absurd h.top_eq (by simp))
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ ih => case_inj hsc hcc hcm hfd ih)
    (fun hk _ ihts => case_ctor hsc hcc hcm hfd hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hsc hcc hcm hfd hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hsc hcc hcm hfd hk hhk hp hr ihts)
    (fun hk hhk hts hvs hev hp ihts ihf => case_call hsc hcc hcm hfd hk hhk hts hvs hev hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hsc hcc hcm hfd hk hhk hvs hp ihts)
    (fun hk ho _ hnf ihts => case_ovl hsc hcc hcm hfd hk ho hnf ihts)
    (fun hk ho hts hvs hlo hcov _ ihts ihf => case_ovlFn hsc hcc hcm hfd hk ho hts hvs hlo hcov ihts ihf)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ ih1 ih2 => case_cons hsc hcc hcm hfd ih1 ih2)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    h

/-- **A predicate's `Holds` value is computed with some fuel**, for a predicate `predVal`
evaluates whose terms are well sorted, where no clause is `aside`. -/
theorem predVal_exec (hna : c.AsideFree) {vars : List Srt} {σ : Subst} (hσ : c.WellSorted vars σ) :
    ∀ {p : Cond} {k : Nat} {b : Bool}, predAtoms p = true → c.condOK vars p = true →
      Holds c k σ p b → ∃ N, ∀ m, N ≤ m → predVal c m σ p = some b
  | .top, _, _, _, _, h => ⟨0, fun _ _ => by cases h; rfl⟩
  | .equals s t u, _, _, _, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases h with
    | equals h₁ h₂ =>
      obtain ⟨n₁, e₁⟩ := EvalTerm.exec hsc hcc hcm hfd hna h₁ vars _ s Exec.headsOK_fns hσ ht
      obtain ⟨n₂, e₂⟩ := EvalTerm.exec hsc hcc hcm hfd hna h₂ vars _ s Exec.headsOK_fns hσ hu
      refine ⟨max n₁ n₂, fun m hm => ?_⟩
      simp only [predVal, evalT_mono_le hsc hcc hcm hfd (m := m) (by omega) e₁ Exec.headsOK_fns hσ ht,
        evalT_mono_le hsc hcc hcm hfd (m := m) (by omega) e₂ Exec.headsOK_fns hσ hu]
  | .mem s t u, _, _, _, hc, h => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ht, hu⟩, -⟩ := hc
    cases h with
    | mem h₁ h₂ =>
      obtain ⟨n₁, e₁⟩ := EvalTerm.exec hsc hcc hcm hfd hna h₁ vars _ s Exec.headsOK_fns hσ ht
      obtain ⟨n₂, e₂⟩ := EvalTerm.exec hsc hcc hcm hfd hna h₂ vars _ s Exec.headsOK_fns hσ hu
      refine ⟨max n₁ n₂, fun m hm => ?_⟩
      simp only [predVal, evalT_mono_le hsc hcc hcm hfd (m := m) (by omega) e₁ Exec.headsOK_fns hσ ht,
        evalT_mono_le hsc hcc hcm hfd (m := m) (by omega) e₂ Exec.headsOK_fns hσ hu]
  | .and p q, _, _, ha, hc, h => by
    simp only [predAtoms, Bool.and_eq_true] at ha
    simp only [Semantics.condOK, Bool.and_eq_true] at hc
    cases h with
    | and h₁ h₂ =>
      obtain ⟨N₁, hN₁⟩ := predVal_exec hna hσ ha.1 hc.1 h₁
      obtain ⟨N₂, hN₂⟩ := predVal_exec hna hσ ha.2 hc.2 h₂
      exact ⟨max N₁ N₂, fun m hm => by simp only [predVal, hN₁ m (by omega), hN₂ m (by omega)]⟩
  | .bot, _, _, ha, _, _ | .not _, _, _, ha, _, _ | .or _ _, _, _, ha, _, _ | .implies _ _, _, _, ha, _, _
  | .ceil _ _, _, _, ha, _, _ | .exMatch _ _ _ _ _, _, _, ha, _, _ | .ex _ _, _, _, ha, _, _
  | .all _ _, _, _, ha, _, _ => by simp [predAtoms] at ha

end

/-- A rule all of whose smaller-priority competitors have only match values `some false`, and one
of its matches with value `true`, a configuration as right-hand side, `ensures` `true` and `post`
`true`, is listed. -/
theorem successorsN_of {n : Nat} {x y : GroundTerm} {r : Rule} (hr : r ∈ c.rules)
    (hlow : ∀ r' ∈ c.rules, r'.prio < r.prio → ∀ σb ∈ ruleMatches c n r' x, σb.2 = some false)
    {σ : Subst} (hσ : (σ, some true) ∈ ruleMatches c n r x)
    (he : CExec.evalT c n σ r.rhs = some (some y)) (hy : c.sortOf y = some topCellSort)
    (hens : ensVal c n r σ = some true) (hpost : predVal c n σ r.post = some true) :
    y ∈ CExec.successorsN c n x := by
  unfold CExec.successorsN
  dsimp only
  have hin : (r, ruleMatches c n r x) ∈ (c.rules.map fun r => (r, ruleMatches c n r x)).filter
      fun (_, l) => l.any fun (_, b) => b != some false := by
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    simp only [List.any_eq_true, bne_iff_ne, ne_eq]
    exact ⟨_, hσ, by simp⟩
  have hmin : (((c.rules.map fun r => (r, ruleMatches c n r x)).filter
      fun (_, l) => l.any fun (_, b) => b != some false).map (·.1.prio)).min? = some r.prio := by
    rw [List.min?_eq_some_iff]
    refine ⟨List.mem_map.mpr ⟨_, hin, rfl⟩, fun q hq => ?_⟩
    obtain ⟨⟨r', l⟩, hrl, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hrl, hany⟩ := List.mem_filter.mp hrl
    obtain ⟨r'', hr'', he'⟩ := List.mem_map.mp hrl
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    simp only [List.any_eq_true, bne_iff_ne, ne_eq] at hany
    obtain ⟨σb, hσb, hne⟩ := hany
    simp only
    refine Classical.byContradiction fun hlt => ?_
    exact hne (hlow r'' hr'' (by omega) σb hσb)
  rw [hmin]
  simp only
  rw [List.mem_flatMap]
  refine ⟨(r, ruleMatches c n r x), List.mem_filter.mpr ⟨hin, by simp⟩, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨(σ, some true), hσ, by simp [he, hy, hens, hpost]⟩

/-- **The executable step lists exactly the `Step` successors**, for some fuel, on a core that
`execReady` accepts and whose functions have at most one result at each argument list: the
statement of
`Exec.step_iff_of_ok` for `CExec.successorsN`. -/
theorem step_iff (hr : execReady c = true) (hfd : FnDet c) (x y : Config c) :
    Step c x y ↔ ∃ n, (CExec.successorsN c n x.val).any (same · y.val) = true := by
  have hready := hr
  have hr' := hr
  simp only [execReady, Bool.and_eq_true] at hr'
  replace hr' := hr'.1
  have hok := hr'.1.1.1.1.1
  have hsc := sortCtx_of_all hok hr'.1.1.1.1.2 (matchCtxO_of hr'.1.1.1.2).ovlCase
  have hcc := cclauseCtx_of hok
  have hcm := clauseComplete_of_ready hr
  have hrc := ruleComplete_of_ready hr
  have hna : c.AsideFree := asideFree_of_ready hr
  constructor
  · rintro ⟨r, hr, σ, hσ, hmatch, hreq, hpre, heval, hens, hpost, hprio⟩
    obtain ⟨hrq, hrt⟩ := ruleSorted_of hok hr
    have hen := ruleSorted_ens_of hok hr
    have hpc := ruleSorted_preds_of hok hr
    have hat := rule_atoms_of_execReady hready hr
    obtain ⟨σ₀, hσ₀m, hag⟩ := hrc r hr x.val σ x.property (hσ.at _) hmatch
    have hcongr : ∀ t m, (∀ i ∈ varOccs t, i < r.vars.length) →
        CExec.evalT c m σ₀ t = CExec.evalT c m σ t :=
      fun t m hv => evalT_congr m (fun i hi => hag i (hv i hi))
    -- fuel for the rule's own `requires`, `pre`, right-hand side, `ensures` and `post`
    obtain ⟨nq, hnq⟩ : ∃ nq, ∀ t, r.req = some t → CExec.evalT c nq σ t = some (some (bool true)) := by
      cases hreqc : r.req with
      | none => exact ⟨0, fun t ht => nomatch ht⟩
      | some t =>
        rw [hreqc] at hrq
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hna (hreq t hreqc) r.vars _ Srt.bool headsOK_fns hσ
          (reqOK_some hrq)
        exact ⟨n, fun t' ht' => by cases ht'; exact hn⟩
    obtain ⟨ne, hne⟩ : ∃ ne, ∀ t, r.ens = some t → CExec.evalT c ne σ t = some (some (bool true)) := by
      cases hensc : r.ens with
      | none => exact ⟨0, fun t ht => nomatch ht⟩
      | some t =>
        rw [hensc] at hen
        obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hna (hens t hensc) r.vars _ Srt.bool headsOK_fns hσ
          (reqOK_some hen)
        exact ⟨n, fun t' ht' => by cases ht'; exact hn⟩
    obtain ⟨nr, hnr⟩ := EvalTerm.exec hsc hcc hcm hfd hna heval r.vars _ topCellSort headsOK_fns hσ hrt
    obtain ⟨np, hnp⟩ := predVal_exec hsc hcc hcm hfd hna hσ hat.1 hpc.1 hpre
    obtain ⟨nt, hnt⟩ := predVal_exec hsc hcc hcm hfd hna hσ hat.2.1 hpc.2 hpost
    -- fuel for every listed match of every rule of a smaller priority
    let low := (c.rules.filter (·.prio < r.prio)).flatMap fun r' =>
      (cmatch c r'.vars [r'.lhs] [x.val]).map (r', ·)
    obtain ⟨N, hN⟩ := fuel_list
      (P := fun n (a : Rule × Subst) => a.1 ∈ c.rules ∧ c.WellSorted a.1.vars a.2 ∧
        ((∃ t v, a.1.req = some t ∧ CExec.evalT c n a.2 t = some v ∧ v ≠ some (bool true)) ∨
          predVal c n a.2 a.1.pre = some false))
      (fun n a ⟨har, haw, hor⟩ => by
        refine ⟨har, haw, ?_⟩
        rcases hor with ⟨t, v, ht, he, hv⟩ | hp
        · obtain ⟨hrq', -⟩ := ruleSorted_of hok har
          rw [ht] at hrq'
          exact Or.inl ⟨t, v, ht, evalT_mono hsc hcc hcm hfd n he headsOK_fns haw (reqOK_some hrq'), hv⟩
        · exact Or.inr (predVal_mono_le hsc hcc hcm hfd haw (Nat.le_succ n) (ruleSorted_preds_of hok har).1 hp))
      (l := low) (fun a ha => by
        obtain ⟨r', hr', ha⟩ := List.mem_flatMap.mp ha
        obtain ⟨hr', hlt⟩ := List.mem_filter.mp hr'
        obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp ha
        obtain ⟨hσw, hpvs⟩ := cmatch_sound hσ'
        cases hprio r' hr' (by simpa using hlt) σ' (hσw.at _) (patVal_of_patVals hpvs) with
        | intro ht he hv =>
          obtain ⟨hrq', -⟩ := ruleSorted_of hok hr'
          rw [ht] at hrq'
          obtain ⟨n, hn⟩ := EvalTerm.exec hsc hcc hcm hfd hna he r'.vars _ Srt.bool headsOK_fns hσw
            (reqOK_some hrq')
          exact ⟨n, hr', hσw, Or.inl ⟨_, _, ht, hn, hv⟩⟩
        | pre hf =>
          obtain ⟨n, hn⟩ := predVal_exec hsc hcc hcm hfd hna hσw (rule_atoms_of_execReady hready hr').1
            (ruleSorted_preds_of hok hr').1 hf
          exact ⟨n, hr', hσw, Or.inr (hn n (Nat.le_refl _))⟩)
    obtain ⟨M, hM⟩ : ∃ M, M = max N (max nq (max nr (max ne (max np nt)))) := ⟨_, rfl⟩
    refine ⟨M, ?_⟩
    rw [List.any_eq_true]
    refine ⟨y.val, ?_, same_iff.mpr rfl⟩
    have hrhs : CExec.evalT c M σ₀ r.rhs = some (some y.val) := by
      rw [hcongr r.rhs _ (sortOfTerm_vars hrt)]
      exact evalT_mono_le hsc hcc hcm hfd (by omega) hnr headsOK_fns hσ hrt
    refine successorsN_of hr (fun r' hr' hlt σb hσb => ?_) (σ := σ₀)
      (ruleMatches_mem.mpr ⟨hσ₀m, ?_⟩) hrhs y.property ?_ ?_
    · obtain ⟨σ', b⟩ := σb
      obtain ⟨hσ', rfl⟩ := ruleMatches_mem.mp hσb
      have hmem : (r', σ') ∈ low :=
        List.mem_flatMap.mpr ⟨r', List.mem_filter.mpr ⟨hr', by simpa using hlt⟩,
          List.mem_map.mpr ⟨σ', hσ', rfl⟩⟩
      show matchVal c _ r' σ' = some false
      rcases (hN _ hmem M (by omega)).2.2 with ⟨t, v, ht, he, hv⟩ | hp
      · refine appVal_false.mpr (Or.inl ?_)
        unfold reqVal
        rw [ht]
        simp only [he, Option.map_some, Option.some.injEq]
        cases hb : isTrue v
        · rfl
        · exact absurd (isTrue_iff.mp hb) hv
      · exact appVal_false.mpr (Or.inr hp)
    · have hq : reqVal c M r σ₀ = some true := by
        unfold reqVal
        cases hreqc : r.req with
        | none => rfl
        | some t =>
          rw [hreqc] at hrq
          have hq : CExec.evalT c M σ₀ t = some (some (bool true)) := by
            rw [hcongr t _ (sortOfTerm_vars (reqOK_some hrq))]
            exact evalT_mono_le hsc hcc hcm hfd (by omega) (hnq t hreqc) headsOK_fns hσ (reqOK_some hrq)
          simp [hq, isTrue_iff]
      show some true = appVal (reqVal c M r σ₀) (predVal c M σ₀ r.pre)
      rw [hq, predVal_congr hag hpc.1, hnp M (by omega)]
      rfl
    · unfold ensVal
      cases hensc : r.ens with
      | none => rfl
      | some t =>
        rw [hensc] at hen
        have hq : CExec.evalT c M σ₀ t = some (some (bool true)) := by
          rw [hcongr t _ (sortOfTerm_vars (reqOK_some hen))]
          exact evalT_mono_le hsc hcc hcm hfd (by omega) (hne t hensc) headsOK_fns hσ (reqOK_some hen)
        simp [hq, isTrue_iff]
    · rw [predVal_congr hag hpc.2, hnt M (by omega)]
  · rintro ⟨n, hn⟩
    rw [List.any_eq_true] at hn
    obtain ⟨z, hz, hs⟩ := hn
    rw [same_iff] at hs
    subst hs
    obtain ⟨_, hst⟩ := successorsN_step_ready hr hz
    exact hst

end KCore.CExec
