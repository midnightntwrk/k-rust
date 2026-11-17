/-
  KCore, checked layer: the executable evaluation is complete (toward `Exec.step_iff`, Exec.lean).

  `EvalTerm.exec`: an `EvalTerm` result is computed by the executable evaluation with some fuel,
  for a well-sorted term under a well-sorted σ, in a core that `ok`, `srReady` and `matchReady`
  accept and whose clauses of one priority are coherent (`CoherentAll`). The evaluation tries the
  priorities in order (`firstClause`): a clause of a smaller priority than the one that applies
  fails, and is passed once the fuel suffices to evaluate its `requires` under each substitution
  the matcher finds (finitely many); at the priority of the clause that applies, the matcher finds
  it (`matchL_complete`) with a substitution that agrees with the relation's on its variables
  (`evalT_congr`), so with enough fuel some candidate of that priority gives a result, whatever the
  others do. That result is an `Eval` result (`evalF_sound`), and coherence makes it the one
  derived (`Eval.functional`). Coherence is also what makes more fuel give the same result
  (`evalT_mono`): the candidate found with less fuel is still found with more, and an earlier one
  found only with more gives the same result.
-/
import KcoreSpec.StepSound
import KcoreSpec.Uniq
import KcoreSpec.EvalFunctional

set_option autoImplicit false

namespace KCore.Exec

open KCore

variable {c : Semantics}

/-! ## The executable evaluation depends on σ only through the term's variables -/

mutual
  theorem evalT_congr : ∀ (n : Nat) {σ σ' : Subst} {t : Term},
      (∀ i ∈ varOccs t, σ.lookup i = σ'.lookup i) → evalT c n σ t = evalT c n σ' t
    | 0, _, _, _, _ => by simp [evalT]
    | n + 1, σ, σ', .var i, ha => by simp [evalT, ha i (by simp [varOccs])]
    | n + 1, _, _, .dv _ _, _ => by simp [evalT]
    | n + 1, _, _, .as _ _, _ => by simp [evalT]
    | n + 1, σ, σ', .inj a b t, ha => by
      simp only [evalT]
      rw [evalT_congr n (fun i hi => ha i (by simpa [varOccs] using hi))]
    | n + 1, σ, σ', .app f ts, ha => by
      simp only [evalT]
      rw [evalTs_congr n (fun i hi => ha i (by simpa [varOccs] using hi))]
  theorem evalTs_congr : ∀ (n : Nat) {σ σ' : Subst} {ts : List Term},
      (∀ i ∈ varOccsList ts, σ.lookup i = σ'.lookup i) → evalTs c n σ ts = evalTs c n σ' ts
    | 0, _, _, _, _ => by simp [evalTs]
    | n + 1, _, _, [], _ => by simp [evalTs]
    | n + 1, σ, σ', t :: ts, ha => by
      simp only [evalTs]
      rw [evalT_congr n (fun i hi => ha i (by simp [varOccsList, hi])),
        evalTs_congr n (fun i hi => ha i (by simp [varOccsList, hi]))]
end

/-! ## Fuel for finitely many evaluations -/

theorem fuel_list {α : Type} {P : Nat → α → Prop} (hmono : ∀ n a, P n a → P (n + 1) a) :
    ∀ {l : List α}, (∀ a ∈ l, ∃ n, P n a) → ∃ N, ∀ a ∈ l, ∀ m, N ≤ m → P m a
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | a :: l, h => by
    obtain ⟨n, hn⟩ := h a (List.mem_cons_self ..)
    obtain ⟨N, hN⟩ := fuel_list hmono (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have up : ∀ {k m : Nat} {b : α}, k ≤ m → P k b → P m b := by
      intro k m b hkm hk
      induction hkm with
      | refl => exact hk
      | step _ ih => exact hmono _ _ ih
    refine ⟨max n N, fun b hb m hm => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact up (Nat.le_trans (Nat.le_max_left _ _) hm) hn
    · exact hN b hb m (Nat.le_trans (Nat.le_max_right _ _) hm)

theorem mapM_of_forall {α β : Type} {g : α → Option β} {f : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, g a = some (f a)) → l.mapM g = some (l.map f)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_of_forall (fun b hb => h b (List.mem_cons_of_mem _ hb)), Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, List.map_cons]

theorem fuel_max {α : Type} {P : Nat → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ m₀, ∀ m, m₀ ≤ m → P m a) → ∃ M, ∀ a ∈ l, ∀ m, M ≤ m → P m a
  | [], _ => ⟨0, fun _ h => nomatch h⟩
  | a :: l, h => by
    obtain ⟨n, hn⟩ := h a (List.mem_cons_self ..)
    obtain ⟨N, hN⟩ := fuel_max (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max n N, fun b hb m hm => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hn m (Nat.le_trans (Nat.le_max_left _ _) hm)
    · exact hN b hb m (Nat.le_trans (Nat.le_max_right _ _) hm)

theorem candResult_false {n : Nat} {x : Clause} {σ : Subst} (h : clauseReq c n x σ = some false) :
    candResult c n (x, σ, clauseReq c n x σ) = none := by
  unfold candResult; simp [h]

/-- A `requires` computed with some fuel is computed with more, given that its terms are. -/
theorem clauseReq_mono {n : Nat} {cl : Clause} {σ : Subst} {L : List CtorSig} {b : Bool}
    (hreq : reqOK (c.rhsCtx L) cl.vars cl.req = true)
    (hev : ∀ t r, evalT c n σ t = some r → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool →
      evalT c (n + 1) σ t = some r)
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
    (hev : ∀ t r, evalT c n σ t = some r → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool →
      evalT c (n + 1) σ t = some r)
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
variable (hsc : SortCtx c) (hcc : ClauseCtx c) (hmc : MatchCtx c) (hco : CoherentAll c)
include hsc hcc hmc hco

/-! ## More fuel gives the same result -/

mutual
  theorem evalT_mono : ∀ (n : Nat) {σ : Subst} {t : Term} {r : Option GroundTerm}
      {vars : List Srt} {L : List CtorSig} {s : Srt},
      evalT c n σ t = some r → HeadsOK c L → c.WellSorted vars σ →
      sortOfTerm (c.rhsCtx L) vars t = some s → evalT c (n + 1) σ t = some r
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [evalT] at h
    | n + 1, σ, .var i, r, _, _, _, h, _, _, _ => by simpa [evalT] using h
    | n + 1, σ, .dv s l, r, _, _, _, h, _, _, _ => by simpa [evalT] using h
    | n + 1, σ, .as t i, r, _, _, _, h, _, _, _ => by simp [evalT] at h
    | n + 1, σ, .inj a b t, r, vars, L, s, h, hL, hσ, ht => by
      simp only [evalT, Option.map_eq_some_iff] at h ⊢
      obtain ⟨r₀, h₀, rfl⟩ := h
      obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
      exact ⟨r₀, evalT_mono n h₀ hL hσ ht', rfl⟩
    | n + 1, σ, .app f ts, r, vars, L, s, h, hL, hσ, ht => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      simp only [evalT, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
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
              obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (by simp [Semantics.lookupOvl, hmc.noOvl]) hk')
              obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
              have hlook : c.lookupFn f = some fn := by
                rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
              have hvs := EvalTerms.sorted hsc (evalTs_sound hsc hcc hmc n hrs hL hσ hargs) hL hσ hargs hall
              exact evalF_mono n hk hlook hvs
  theorem evalTs_mono : ∀ (n : Nat) {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}
      {vars : List Srt} {L : List CtorSig} {ss : List Srt},
      evalTs c n σ ts = some rs → HeadsOK c L → c.WellSorted vars σ →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → evalTs c (n + 1) σ ts = some rs
    | 0, _, _, _, _, _, _, h, _, _, _ => by simp [evalTs] at h
    | n + 1, σ, [], rs, _, _, _, h, _, _, _ => by simpa [evalTs] using h
    | n + 1, σ, t :: ts, rs, vars, L, ss, h, hL, hσ, hts => by
      simp only [evalTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨r, hr, rs', hrs', rfl⟩ := h
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
      exact ⟨r, evalT_mono n hr hL hσ h1, rs', evalTs_mono n hrs' hL hσ h2, rfl⟩
  theorem evalF_mono : ∀ (n : Nat) {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm}
      {fn : Fn}, evalF c n f vs = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      evalF c (n + 1) f vs = some r
    | 0, _, _, _, _, h, _, _ => by simp [evalF] at h
    | n + 1, f, vs, r, fn, h, hfn, hvs => by
      simp only [evalF, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨fn', hfn', h⟩ := h
      rw [hfn] at hfn'
      cases hfn'
      exact ⟨fn, hfn, firstClause_mono n h hfn hvs (pre := []) rfl (fun _ h => nomatch h)⟩
  theorem firstClause_mono : ∀ (n : Nat) {fn : Fn} {vs : List GroundTerm} {cls : List Clause}
      {r : Option GroundTerm} {f : Sym} {pre : List Clause},
      firstClause c n vs (c.fnRest fn vs) cls = some r → c.lookupFn f = some fn → c.sortsOf vs = some fn.args →
      byPrio fn.clauses = pre ++ cls → (∀ cl ∈ pre, Fails c vs cl) →
      firstClause c (n + 1) vs (c.fnRest fn vs) cls = some r
    | 0, _, _, _, _, _, _, h, _, _, _, _ => by simp [firstClause] at h
    | n + 1, fn, vs, [], r, f, pre, h, _, _, _, _ => by simpa [firstClause] using h
    | n + 1, fn, vs, cl :: rest, r, f, pre, h, hfn, hvs, hcls, hpre => by
      have hE := firstClause_sound hsc hcc hmc (n + 1) h hfn hvs hcls hpre
      obtain ⟨L, hL, hclk⟩ := hcc fn (lookupFn_spec hfn).1
      have hin : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), x ∈ fn.clauses := fun x hx =>
        mem_byPrio.mp (by rw [hcls]; exact List.mem_append_right _ (List.takeWhile_subset _ hx))
      have hws : ∀ x σ, σ ∈ clauseMatches c x vs → c.WellSorted x.vars σ := fun x σ hσ =>
        wellSorted_iff.mp (List.mem_filter.mp hσ).2
      have hreqm : ∀ x ∈ (cl :: rest).takeWhile (·.prio == cl.prio), ∀ σ ∈ clauseMatches c x vs,
          ∀ b, clauseReq c n x σ = some b → clauseReq c (n + 1) x σ = some b := fun x hx σ hσ b hb =>
        clauseReq_mono (hclk x (hin x hx)).2.2.2.1
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
              clauseEns_mono (hclk x (hin x hx)).2.2.2.2.2.1
                (fun t r h ht => evalT_mono n h hL (hws x σ hσ) ht) he
            unfold candBody at hres ⊢
            split at hres
            · rename_i he
              rw [hem he]
              exact evalT_mono n hres hL (hws x σ hσ) (hclk x (hin x hx)).2.2.2.2.1
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
          have hE' : Eval c f vs r'' := firstClause_sound hsc hcc hmc (n + 2)
            (by rw [firstClause_cons, hf]) hfn hvs hcls hpre
          simp only [Eval.functional hco hE' hE]
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
          · exact class_fails hsc hcc hmc hfn hvs hin hall x hx
        · cases h
end

theorem evalT_mono_le {n m : Nat} (hle : n ≤ m) {σ : Subst} {t : Term} {r : Option GroundTerm}
    {vars : List Srt} {L : List CtorSig} {s : Srt} (h : evalT c n σ t = some r) (hL : HeadsOK c L)
    (hσ : c.WellSorted vars σ) (ht : sortOfTerm (c.rhsCtx L) vars t = some s) : evalT c m σ t = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalT_mono hsc hcc hmc hco _ ih hL hσ ht

theorem evalTs_mono_le {n m : Nat} (hle : n ≤ m) {σ : Subst} {ts : List Term}
    {rs : List (Option GroundTerm)} {vars : List Srt} {L : List CtorSig} {ss : List Srt}
    (h : evalTs c n σ ts = some rs) (hL : HeadsOK c L) (hσ : c.WellSorted vars σ)
    (hts : sortsOfTerms (c.rhsCtx L) vars ts = some ss) : evalTs c m σ ts = some rs := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalTs_mono hsc hcc hmc hco _ ih hL hσ hts

theorem evalF_mono_le {n m : Nat} (hle : n ≤ m) {f : Sym} {vs : List GroundTerm}
    {r : Option GroundTerm} {fn : Fn} (h : evalF c n f vs = some r) (hfn : c.lookupFn f = some fn)
    (hvs : c.sortsOf vs = some fn.args) : evalF c m f vs = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalF_mono hsc hcc hmc hco _ ih hfn hvs

theorem clauseReq_mono_le {n m : Nat} (hle : n ≤ m) {fn : Fn} {cl : Clause} {σ : Subst} {b : Bool}
    (hfn : fn ∈ c.allFns) (hcl : cl ∈ fn.clauses) (hσ : c.WellSorted cl.vars σ)
    (h : clauseReq c n cl σ = some b) : clauseReq c m cl σ = some b := by
  obtain ⟨L, hL, hclk⟩ := hcc fn hfn
  induction hle with
  | refl => exact h
  | step _ ih =>
    exact clauseReq_mono (hclk cl hcl).2.2.2.1 (fun t r h ht => evalT_mono hsc hcc hmc hco _ h hL hσ ht) ih

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

omit hsc hcc hmc hco in
/-- The clauses of a sorted list are tried a priority at a time: where every clause of a smaller
priority than p is passed and some clause of priority p gives a result, or every clause is passed,
the evaluation has a result with enough fuel. -/
theorem firstClause_some {vs : List GroundTerm} {fr : Option GroundTerm} {p : Nat} : ∀ (k : Nat) (l : List Clause),
    l.length ≤ k → l.Pairwise (fun a b => a.prio ≤ b.prio) →
    (∀ x ∈ l, x.prio < p → SkipFuel c vs x) →
    ((∃ x ∈ l, x.prio = p ∧ ApplyFuel c vs x) ∨ ∀ x ∈ l, SkipFuel c vs x) →
    ∃ M, ∀ m, M ≤ m → ∃ r, firstClause c m vs fr l = some r
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
        ∃ M, ∀ m, M ≤ m → ∃ r, firstClause c m vs fr (cl :: rest) = some r := by
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
  ∀ fn, c.lookupFn f = some fn → c.sortsOf vs = some fn.args → ∃ n, evalF c n f vs = some r
def M2 (c : Semantics) (vs : List GroundTerm) (cl : Clause) : Prop :=
  ∀ fn f, c.lookupFn f = some fn → cl ∈ fn.clauses → c.sortsOf vs = some fn.args → SkipFuel c vs cl
def M3 (c : Semantics) (σ : Subst) (cl : Clause) : Prop :=
  ∀ L, HeadsOK c L → c.WellSorted cl.vars σ → reqOK (c.rhsCtx L) cl.vars cl.req = true →
    cl.pre = .top →
    ∃ t r n, cl.req = some t ∧ evalT c n σ t = some r ∧ r ≠ some (bool true)
def M4 (c : Semantics) (σ : Subst) (t : Term) (r : Option GroundTerm) : Prop :=
  ∀ vars L s, HeadsOK c L → c.WellSorted vars σ → sortOfTerm (c.rhsCtx L) vars t = some s →
    ∃ n, evalT c n σ t = some r
def M5 (c : Semantics) (σ : Subst) (ts : List Term) (rs : List (Option GroundTerm)) : Prop :=
  ∀ vars L ss, HeadsOK c L → c.WellSorted vars σ → sortsOfTerms (c.rhsCtx L) vars ts = some ss →
    ∃ n, evalTs c n σ ts = some rs

/-- Where the evaluation of `byPrio fn.clauses` has a result with enough fuel, it is the derived
result `r`. -/
theorem evalF_of_some {f : Sym} {fn : Fn} {vs : List GroundTerm} {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) (hE : Eval c f vs r)
    (h : ∃ M, ∀ m, M ≤ m → ∃ r, firstClause c m vs (c.fnRest fn vs) (byPrio fn.clauses) = some r) :
    ∃ n, evalF c n f vs = some r := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨r', hr'⟩ := hM M (Nat.le_refl _)
  have hev : evalF c (M + 1) f vs = some r' := by
    simp only [evalF, hfn, Option.bind_eq_bind, Option.bind_some, hr']
  have hE' := evalF_sound hsc hcc hmc (M + 1) hev hfn hvs
  exact ⟨M + 1, by rw [hev, Eval.functional hco hE' hE]⟩

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
  obtain ⟨hpt, hmf, hlc, hrq, hrt, hensOK, _⟩ := hclk cl hmem
  have hcov := binds_all hlc
  have hn : 4 * termSizeList cl.pats + 1 ≤ patFuel cl.pats := by unfold patFuel; omega
  obtain ⟨σ₀, hm₀, hx₀, _, hb₀⟩ := matchL_complete hmc hσ (patFuel cl.pats) (σ := []) hn hmf
    hmatch hpt (fun _ _ h => by simp [List.lookup] at h)
  have hσ₀ := wellSorted_of_below hσ hx₀ hb₀ hcov
  have hag : ∀ t m, (∀ i ∈ varOccs t, i < cl.vars.length) → evalT c m σ₀ t = evalT c m σ t :=
    fun t m hv => evalT_congr m (fun i hi => (agree_of_ext hx₀ hb₀ i (hcov i (hv i hi))).trans rfl)
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
        evalT_mono_le hsc hcc hmc hco hm hn hL hσ (reqOK_some hrq)]
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
        evalT_mono_le hsc hcc hmc hco hm hn hL hσ (reqOK_some hensOK)]
      simp [isTrue_iff]
  obtain ⟨nr, hnr⟩ := ihrhs cl.vars L fn.result hL hσ hrt
  have happ : ApplyFuel c vs cl :=
    ⟨σ₀, List.mem_filter.mpr ⟨hm₀, wellSorted_iff.mpr hσ₀⟩, max (max nq nr) ne, fun m hm =>
      ⟨hnq m (by omega), r, by
        unfold candResult candBody
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [hne m (by omega)]
        show evalT c m σ₀ cl.rhs = some r
        rw [hag cl.rhs m (sortOfTerm_vars hrt)]
        exact evalT_mono_le hsc hcc hmc hco (by omega : nr ≤ m) hnr hL hσ hrt⟩⟩
  refine evalF_of_some hsc hcc hmc hco hfn hvs
    (.clause hfn hmem hσ hmatch hreq hpre (fun cl' h _ hlt => hprio cl' h hlt)
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
  obtain ⟨hpt, hmf, hlc, hrq, hrt, hensOK, _⟩ := hclk cl hmem
  have hcov := binds_all hlc
  have hn : 4 * termSizeList cl.pats + 1 ≤ patFuel cl.pats := by unfold patFuel; omega
  obtain ⟨σ₀, hm₀, hx₀, _, hb₀⟩ := matchL_complete hmc hσ (patFuel cl.pats) (σ := []) hn hmf
    hmatch hpt (fun _ _ h => by simp [List.lookup] at h)
  have hσ₀ := wellSorted_of_below hσ hx₀ hb₀ hcov
  have hag : ∀ t m, (∀ i ∈ varOccs t, i < cl.vars.length) → evalT c m σ₀ t = evalT c m σ t :=
    fun t m hv => evalT_congr m (fun i hi => (agree_of_ext hx₀ hb₀ i (hcov i (hv i hi))).trans rfl)
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
        evalT_mono_le hsc hcc hmc hco hm hn hL hσ (reqOK_some hrq)]
      simp [isTrue_iff]
  rw [ht] at hensOK
  obtain ⟨ne, hne⟩ := ihe cl.vars L Srt.bool hL hσ (reqOK_some hensOK)
  have hef : ∀ m, ne ≤ m → clauseEns c m cl σ₀ = some false := fun m hm => by
    unfold clauseEns
    rw [ht]
    simp only
    rw [hag t m (sortOfTerm_vars (reqOK_some hensOK)),
      evalT_mono_le hsc hcc hmc hco hm hne hL hσ (reqOK_some hensOK)]
    simp only [Option.map_some, Option.some.injEq]
    cases hb : isTrue w
    · rfl
    · exact absurd (isTrue_iff.mp hb) hw
  have happ : ApplyFuel c vs cl :=
    ⟨σ₀, List.mem_filter.mpr ⟨hm₀, wellSorted_iff.mpr hσ₀⟩, max nq ne, fun m hm =>
      ⟨hnq m (by omega), none, by
        unfold candResult candBody
        simp only [beq_self_eq_true, ↓reduceIte]
        rw [hef m (by omega)]⟩⟩
  refine evalF_of_some hsc hcc hmc hco hfn hvs
    (.ensFails hfn hmem hσ hmatch hreq hpre (fun cl' h _ hlt => hprio cl' h hlt)
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
  exact evalF_of_some hsc hcc hmc hco hfn hvs (.rest hfn hnone)
    (firstClause_some (p := 0) _ _ (Nat.le_refl _) (pairwise_byPrio _) (fun _ _ h => nomatch h)
      (.inr fun x hx => ihnone x (mem_byPrio.mp hx) fn f hfn (mem_byPrio.mp hx) hvs))

theorem case_fails {vs : List GroundTerm} {cl : Clause}
    (ih : ∀ σ, c.WellSortedAt cl.vars cl.leftVars σ → PatVals c σ cl.pats vs → M3 c σ cl) : M2 c vs cl := by
  intro fn f hfn hmem hvs
  have hfm := (lookupFn_spec hfn).1
  obtain ⟨L, hL, hclk⟩ := hcc fn hfm
  obtain ⟨_, _, _, hreq, _, _, htop, _⟩ := hclk cl hmem
  obtain ⟨N, hN⟩ := fuel_max (P := fun m σ => clauseReq c m cl σ = some false)
    (l := clauseMatches c cl vs) (fun σ hσ => by
      obtain ⟨hm, hws⟩ := List.mem_filter.mp hσ
      have hσw := wellSorted_iff.mp hws
      obtain ⟨_, hpv⟩ := matchL_sound _ (canonVs_of_sortsOf hvs) hm
      obtain ⟨t, r, n, ht, hn, hr⟩ := ih σ (hσw.at _) hpv L hL hσw hreq htop
      have h0 : clauseReq c n cl σ = some false := by
        unfold clauseReq
        rw [ht]
        simp only [hn, Option.map_some, Option.some.injEq]
        cases hb : isTrue r
        · rfl
        · exact absurd (isTrue_iff.mp hb) hr
      exact ⟨n, fun m hm => clauseReq_mono_le hsc hcc hmc hco hm hfm hmem hσw h0⟩)
  exact ⟨N, fun m hm σ hσ => hN σ hσ m hm⟩

theorem case_reqFails {σ : Subst} {cl : Clause} {t : Term} {r : Option GroundTerm}
    (ht : cl.req = some t) (hr : r ≠ some (bool true)) (ihe : M4 c σ t r) : M3 c σ cl := by
  intro L hL hσ hreq _
  rw [ht] at hreq
  obtain ⟨n, hn⟩ := ihe cl.vars L Srt.bool hL hσ (reqOK_some hreq)
  exact ⟨t, r, n, ht, hn, hr⟩

theorem case_call {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {vs : List GroundTerm} {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = false)
    (hts : EvalTerms c σ ts rs) (hvs : allSome rs = some vs) (hp : c.isParam f = false)
    (ihts : M5 c σ ts rs) (ihf : M1 c f vs r) : M4 c σ (.app f ts) r := by
  intro vars L s hL hσ ht
  obtain ⟨k, hk', hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n₁, hn₁⟩ := ihts vars L k.args hL hσ hargs
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hk)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk'
  rw [lookupSig_append_of_none hnc,
    lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hhk),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at hk'
  obtain ⟨hkL, hkn⟩ := lookupSig_spec (lookup_drop_ovls (by simp [Semantics.lookupOvl, hmc.noOvl]) hk')
  obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
  have hlook : c.lookupFn f = some fn := by
    rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hsc.nodupFns hfn
  have hvsS := EvalTerms.sorted hsc hts hL hσ hargs hvs
  obtain ⟨n₂, hn₂⟩ := ihf fn hlook hvsS
  refine ⟨max n₁ n₂ + 1, ?_⟩
  simp only [evalT, evalTs_mono_le hsc hcc hmc hco (Nat.le_max_left _ _) hn₁ hL hσ hargs, hk, hhk, hp,
    hvs, evalF_mono_le hsc hcc hmc hco (Nat.le_max_right _ _) hn₂ hlook hvsS, Option.bind_eq_bind,
    Option.bind_some, Bool.false_eq_true, ↓reduceIte]

theorem case_hook {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    {r : Option GroundTerm} (hk : c.isCtor f = false) (hhk : isHook f = true)
    (hh : ∀ vs, allSome rs = some vs → c.hookRes f vs = some r) (hund : allSome rs = none → r = none)
    (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) r := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  refine ⟨n + 1, ?_⟩
  simp only [evalT, hn, hk, hhk, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true,
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
  simp only [evalT, hn, hk, hhk, hp, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true,
    ↓reduceIte, Option.pure_def, hr]

theorem case_ctor {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = true) (ihts : M5 c σ ts rs) :
    M4 c σ (.app f ts) ((allSome rs).map (.ctor f)) := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  exact ⟨n + 1, by simp [evalT, hn, hk]⟩

theorem case_callUndef {σ : Subst} {f : Sym} {ts : List Term} {rs : List (Option GroundTerm)}
    (hk : c.isCtor f = false) (hhk : isHook f = false) (hvs : allSome rs = none)
    (hp : c.isParam f = false) (ihts : M5 c σ ts rs) : M4 c σ (.app f ts) none := by
  intro vars L s hL hσ ht
  obtain ⟨k, _, hargs, _⟩ := sortOfTerm_app.mp ht
  obtain ⟨n, hn⟩ := ihts vars L k.args hL hσ hargs
  exact ⟨n + 1, by simp [evalT, hn, hk, hhk, hp, hvs]⟩

theorem case_inj {σ : Subst} {a b : Srt} {t : Term} {r : Option GroundTerm} (ih : M4 c σ t r) :
    M4 c σ (.inj a b t) (r.map (injNormal a b)) := by
  intro vars L s hL hσ ht
  obtain ⟨_, ht', _⟩ := sortOfTerm_inj.mp ht
  obtain ⟨n, hn⟩ := ih vars L a hL hσ ht'
  exact ⟨n + 1, by simp [evalT, hn]⟩

theorem case_cons {σ : Subst} {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} (ih1 : M4 c σ t r) (ih2 : M5 c σ ts rs) : M5 c σ (t :: ts) (r :: rs) := by
  intro vars L ss hL hσ hts
  obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp hts
  obtain ⟨n₁, hn₁⟩ := ih1 vars L s hL hσ h1
  obtain ⟨n₂, hn₂⟩ := ih2 vars L ss' hL hσ h2
  exact ⟨max n₁ n₂ + 1, by
    simp [evalTs, evalT_mono_le hsc hcc hmc hco (Nat.le_max_left _ _) hn₁ hL hσ h1,
      evalTs_mono_le hsc hcc hmc hco (Nat.le_max_right _ _) hn₂ hL hσ h2]⟩

/-- An `EvalTerm` result is computed with some fuel, where no clause is `aside`. -/
theorem EvalTerm.exec (hna : c.AsideFree) {σ : Subst} {t : Term} {r : Option GroundTerm} (h : EvalTerm c σ t r) :
    M4 c σ t r :=
  EvalTerm.rec (motive_1 := fun f vs r _ => M1 c f vs r) (motive_2 := fun vs cl _ => M2 c vs cl)
    (motive_3 := fun σ cl _ => M3 c σ cl) (motive_4 := fun σ t r _ => M4 c σ t r)
    (motive_5 := fun σ ts rs _ => M5 c σ ts rs)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True) (motive_8 := fun _ _ _ _ => True)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ hrhs hens _ ihreq _ ihprio ihrhs ihens _ =>
      case_clause hsc hcc hmc hco hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        hrhs hens (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihrhs ihens)
    (fun hfn hnone ihnone => case_rest hsc hcc hmc hco hfn hnone ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ ht he hw ihreq _ ihprio ihe =>
      case_ensFails hsc hcc hmc hco hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        ht he hw (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihe)
    (fun hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun _ ih => case_fails hsc hcc hmc hco ih)
    (fun ht _ hr ihe => case_reqFails hsc hcc hmc hco ht hr ihe)
    (fun h _ => by intro _ _ _ _ htop; rw [htop] at h; exact absurd h.top_eq (by simp))
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ ih => case_inj hsc hcc hmc hco ih)
    (fun hk _ ihts => case_ctor hsc hcc hmc hco hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hsc hcc hmc hco hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hsc hcc hmc hco hk hhk hp hr ihts)
    (fun hk hhk hts hvs _ hp ihts ihf => case_call hsc hcc hmc hco hk hhk hts hvs hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hsc hcc hmc hco hk hhk hvs hp ihts)
    (fun _ ho _ _ _ => by rw [c.isOvl_of_none hmc.noOvl] at ho; cases ho)
    (fun _ ho _ _ _ _ _ _ _ => by rw [c.isOvl_of_none hmc.noOvl] at ho; cases ho)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ ih1 ih2 => case_cons hsc hcc hmc hco ih1 ih2)
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
      case_clause hsc hcc hmc hco hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        hrhs hens (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihrhs ihens)
    (fun hfn hnone ihnone => case_rest hsc hcc hmc hco hfn hnone ihnone)
    (fun hfn hmem hσ hmatch hreq hpre hprio _ ht he hw ihreq _ ihprio ihe =>
      case_ensFails hsc hcc hmc hco hfn hmem hσ hmatch hreq hpre (fun x h hlt => hprio x h (hna hfn x h) hlt)
        ht he hw (fun x h hlt => ihprio x h (hna hfn x h) hlt) ihreq ihe)
    (fun hfn hmem _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun hfn hmem hne _ _ _ _ _ _ _ _ _ _ _ => absurd (hcc.plainCl (lookupFn_spec hfn).1 hmem).1 hne)
    (fun _ ih => case_fails hsc hcc hmc hco ih)
    (fun ht _ hr ihe => case_reqFails hsc hcc hmc hco ht hr ihe)
    (fun h _ => by intro _ _ _ _ htop; rw [htop] at h; exact absurd h.top_eq (by simp))
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ ih => case_inj hsc hcc hmc hco ih)
    (fun hk _ ihts => case_ctor hsc hcc hmc hco hk ihts)
    (fun hk hhk _ hh hund ihts => case_hook hsc hcc hmc hco hk hhk hh hund ihts)
    (fun hk hhk hp _ hr ihts => case_param hsc hcc hmc hco hk hhk hp hr ihts)
    (fun hk hhk hts hvs _ hp ihts ihf => case_call hsc hcc hmc hco hk hhk hts hvs hp ihts ihf)
    (fun hk hhk _ hvs hp ihts => case_callUndef hsc hcc hmc hco hk hhk hvs hp ihts)
    (fun _ ho _ _ _ => by rw [c.isOvl_of_none hmc.noOvl] at ho; cases ho)
    (fun _ ho _ _ _ _ _ _ _ => by rw [c.isOvl_of_none hmc.noOvl] at ho; cases ho)
    (fun _ _ _ _ _ _ => ⟨1, rfl⟩)
    (fun _ _ ih1 ih2 => case_cons hsc hcc hmc hco ih1 ih2)
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

end

end KCore.Exec
