/-
  Helper-lemma spike, by hand: `F.eval` and `F.eval_iff` for kore.k's `app`, `lookup`, `mkInj`
  and for `match` at two argument lists where only `m-fail` applies, each proof written for its
  function (shared lemmas over the clauses' shapes, one case analysis for the clauses of a
  smaller priority).
-/
import User.SpikeBase

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KK.Spike.Hand

open KCore KCore.Det RefKk KK KK.Spike

/-- A result of a function of kore.k is its only one. -/
theorem iff_of_eval {f : Sym} {vs : List GroundTerm} {v r : Option GroundTerm} (h : Eval c₀ f vs v) :
    Eval c₀ f vs r ↔ r = v :=
  ⟨fun h' => Eval.functional coherent h' h, fun e => e ▸ h⟩

/-! ## `app` -/

spike_hb in
theorem app.eval (xs ys : List GroundTerm) (hx : ∀ t ∈ xs, c₀.sortOf t = some 33)
    (hy : ∀ t ∈ ys, c₀.sortOf t = some 33) :
    Eval c₀ 447 [tsOf xs, tsOf ys] (some (tsOf (xs ++ ys))) := by
  induction xs with
  | nil =>
    exact .clause (cl := appNil) (σ := enumFrom 0 [tsOf ys]) lookup_app (by simp [fnApp])
      (ws_enum (.cons (sort_ts hy) .nil)) (.cons (.ctor (by decide +kernel) .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) .top (no_smaller (by decide)) rfl (ev_var rfl) (fun _ h => by cases h) .top
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, c₀.sortOf u = some 33 := fun u hu => hx u (List.mem_cons_of_mem _ hu)
    exact .clause (cl := appCons) (σ := enumFrom 0 [t, tsOf ts, tsOf ys]) lookup_app (by simp [fnApp])
      (ws_enum (.cons (hx t (List.mem_cons_self ..)) (.cons (sort_ts hts) (.cons (sort_ts hy) .nil))))
      (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) .top (no_smaller (by decide)) rfl
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (ih hts)) .nil)))
      (fun _ h => by cases h) .top

theorem app.eval_iff (xs ys : List GroundTerm) (hx : ∀ t ∈ xs, c₀.sortOf t = some 33)
    (hy : ∀ t ∈ ys, c₀.sortOf t = some 33) {r : Option GroundTerm} :
    Eval c₀ 447 [tsOf xs, tsOf ys] r ↔ r = some (tsOf (xs ++ ys)) := iff_of_eval (app.eval xs ys hx hy)

/-! ## `lookup` -/

/-- kore.k's `lookup`: the clause list of the first entry numbered `f`. -/
def lookupF (f : Int) : List (Int × GroundTerm) → Option GroundTerm
  | [] => none
  | (g, cs) :: fs => if f = g then some cs else lookupF f fs

spike_hb in
theorem lookup.eval (f : Int) (fs : List (Int × GroundTerm)) (h : ∀ p ∈ fs, c₀.sortOf p.2 = some 35) :
    Eval c₀ 485 [.dv 3 (.int f), fnsOf fs] (some (lookOf (lookupF f fs))) := by
  induction fs with
  | nil =>
    exact .clause (cl := lkNil) (σ := enumFrom 0 [.dv 3 (.int f)]) lookup_lookup (by simp [fnLookup])
      (ws_enum (.cons (sort_int f) .nil)) (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) .nil))
      (fun _ h => by cases h) .top (no_smaller (by decide)) rfl (ev_ctor .nil) (fun _ h => by cases h) .top
  | cons p fs ih =>
    obtain ⟨g, cs⟩ := p
    have hfs : ∀ q ∈ fs, c₀.sortOf q.2 = some 35 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hw : c₀.WellSorted [3, 3, 35, 39] (enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs]) :=
      ws_enum (.cons (sort_int f) (.cons (sort_int g) (.cons (h (g, cs) (List.mem_cons_self ..))
        (.cons (sort_fns hfs) .nil))))
    have hm : PatVals c₀ (enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs])
        [.var 0, .app 421 [.var 1, .var 2, .var 3]] [.dv 3 (.int f), fnsOf ((g, cs) :: fs)] :=
      .cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil)
    by_cases hfg : f = g
    · have hr : lookupF f ((g, cs) :: fs) = some cs := by simp [lookupF, hfg]
      rw [hr]
      refine .clause (cl := lkHit) lookup_lookup (by simp [fnLookup]) hw hm ?_ .top (no_smaller (by decide)) rfl
        (ev_ctor (.cons (ev_var rfl) .nil)) (fun _ h => by cases h) .top
      intro t ht
      cases ht
      simpa [hfg] using ev_int2 (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs]) (P := (· = ·)) hook_intEq
        (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
    · have hr : lookupF f ((g, cs) :: fs) = lookupF f fs := by simp [lookupF, hfg]
      rw [hr]
      refine .clause (cl := lkMiss) lookup_lookup (by simp [fnLookup]) hw hm ?_ .top (no_smaller (by decide)) rfl
        (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (ih hfs)) (fun _ h => by cases h) .top
      intro t ht
      cases ht
      simpa [hfg] using ev_int2 (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs]) (P := (· ≠ ·)) hook_intNe
        (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)

theorem lookup.eval_iff (f : Int) (fs : List (Int × GroundTerm)) (h : ∀ p ∈ fs, c₀.sortOf p.2 = some 35)
    {r : Option GroundTerm} :
    Eval c₀ 485 [.dv 3 (.int f), fnsOf fs] r ↔ r = some (lookOf (lookupF f fs)) := iff_of_eval (lookup.eval f fs h)

/-! ## `mkInj` -/

/-- kore.k's `mkInj`: `bot` stays, an injection is re-targeted, any other term is injected. -/
def mkInjF (a b t : GroundTerm) : GroundTerm :=
  match t with
  | .ctor 412 [] => t
  | .ctor 424 [c, _, u] => .ctor 424 [c, b, u]
  | _ => .ctor 424 [a, b, t]

spike_hb in
theorem mkInj.eval (a b t : GroundTerm) (ha : c₀.sortOf a = some 3) (hb : c₀.sortOf b = some 3)
    (ht : c₀.sortOf t = some 33) : Eval c₀ 493 [a, b, t] (some (mkInjF a b t)) := by
  unfold mkInjF
  split
  · exact .clause (cl := injBot) (σ := enumFrom 0 [b, .ctor 412 [], a]) lookup_mkInj (by simp [fnMkInj])
      (ws_enum (.cons hb (.cons ht (.cons ha .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor (by decide +kernel) .nil) rfl) .nil)))
      (fun _ h => by cases h) .top (no_smaller (by decide)) rfl (ev_var rfl) (fun _ h => by cases h) .top
  · next c x u =>
    obtain ⟨hc, hr⟩ := sorts_cons_inv (sort_args ht (as := [3, 3, 33]) (by decide +kernel))
    obtain ⟨hx, hr⟩ := sorts_cons_inv hr
    obtain ⟨hu, -⟩ := sorts_cons_inv hr
    exact .clause (cl := injCompose) (σ := enumFrom 0 [c, x, u, a, b]) lookup_mkInj (by simp [fnMkInj])
      (ws_enum (.cons hc (.cons hx (.cons hu (.cons ha (.cons hb .nil))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel)
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil)))
      (fun _ h => by cases h) .top (no_smaller (by decide)) rfl
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (fun _ h => by cases h) .top
  · next hbot hij =>
    refine .clause (cl := injNew) (σ := enumFrom 0 [a, b, t]) lookup_mkInj (by simp [fnMkInj])
      (ws_enum (.cons ha (.cons hb (.cons ht .nil)))) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (fun _ h => by cases h) .top ?_ rfl
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (fun _ h => by cases h) .top
    intro cl' hm _ hp
    simp only [fnMkInj, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · refine .intro fun σ _ hm => ?_
      rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h2, _⟩⟩⟩
      obtain ⟨xs, he, hxs⟩ := pv_ctor h2
      rcases hxs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
      exact (hij _ _ _ he).elim
    · refine .intro fun σ _ hm => ?_
      rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h2, _⟩⟩⟩
      obtain ⟨xs, he, hxs⟩ := pv_ctor (PatVal.as_inv h2).1
      cases hxs
      exact (hbot he).elim
    · exact absurd hp (by decide)

theorem mkInj.eval_iff (a b t : GroundTerm) (ha : c₀.sortOf a = some 3) (hb : c₀.sortOf b = some 3)
    (ht : c₀.sortOf t = some 33) {r : Option GroundTerm} :
    Eval c₀ 493 [a, b, t] r ↔ r = some (mkInjF a b t) := iff_of_eval (mkInj.eval a b t ha hb ht)

/-! ## `match` where only `m-fail` applies -/

/-- A clause whose first pattern is of another constructor than the first argument fails. -/
theorem fails_at1 {cl : Clause} {g h : Sym} {ps rest : List Term} {us vs : List GroundTerm}
    (hp : cl.pats = .app g ps :: rest) (hg : g ≠ h) (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ (.ctor h us :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨v, vs', he, hv, -⟩ := PatVals.cons_inv hm
  cases he
  obtain ⟨xs, he, -⟩ := pv_ctor hv hc hk
  cases he
  exact (hg rfl).elim

/-- A clause whose second pattern is of another constructor than the second argument fails. -/
theorem fails_at2 {cl : Clause} {g h : Sym} {p : Term} {ps rest : List Term} {w : GroundTerm}
    {us vs : List GroundTerm} (hp : cl.pats = p :: .app g ps :: rest) (hg : g ≠ h)
    (hc : c₀.isCtor g = true := by decide +kernel) (hk : patternHooks.contains g = false := by decide +kernel) :
    Fails c₀ (w :: .ctor h us :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨v, vs', he, -, hm'⟩ := PatVals.cons_inv hm
  cases he
  obtain ⟨v, vs', he, hv, -⟩ := PatVals.cons_inv hm'
  cases he
  obtain ⟨xs, he, -⟩ := pv_ctor hv hc hk
  cases he
  exact (hg rfl).elim

/-- The term `iv(I)` and any term of sort `Term` built by a constructor of one argument. -/
theorem sort_term1 {f : Sym} {v : GroundTerm} {a : Srt} (hv : c₀.sortOf v = some a)
    (hk : (lookupSig c₀.ctorSigs f).map (fun k => (k.args, k.result)) = some ([a], 33)) :
    c₀.sortOf (.ctor f [v]) = some 33 := sort_ctor hk (sorts_cons hv sorts_nil)

spike_hb in
/-- `match(iv(I), bv(Y), B, S)` is `.Ms`: no equation of priority 50 matches. -/
theorem match.eval_iv_bv (i y b s : GroundTerm) (hi : c₀.sortOf i = some 3) (hy : c₀.sortOf y = some 2)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) :
    Eval c₀ 486 [.ctor 425 [i], .ctor 413 [y], b, s] (some (.ctor 403 [])) := by
  refine .clause (cl := mFail) (σ := enumFrom 0 [.ctor 425 [i], .ctor 413 [y], b, s]) lookup_match (by simp [fnMatch])
    (ws_enum (.cons (sort_term1 hi (by decide +kernel)) (.cons (sort_term1 hy (by decide +kernel)) (.cons hb (.cons hs .nil)))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) .top ?_ rfl (ev_ctor .nil) (fun _ h => by cases h) .top
  intro cl' hm _ hp
  simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hp (by decide)
    | exact fails_at1 rfl (by decide)
    | exact fails_at2 rfl (by decide)

theorem match.eval_iv_bv_iff (i y b s : GroundTerm) (hi : c₀.sortOf i = some 3) (hy : c₀.sortOf y = some 2)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) {r : Option GroundTerm} :
    Eval c₀ 486 [.ctor 425 [i], .ctor 413 [y], b, s] r ↔ r = some (.ctor 403 []) :=
  iff_of_eval (match.eval_iv_bv i y b s hi hy hb hs)

spike_hb in
/-- `match(iv(I), iv(J), B, S)` is `.Ms` where I and J differ: `m-int` matches and its `requires`
is `false`; no other equation of priority 50 matches. -/
theorem match.eval_iv_ne (i j : Int) (b s : GroundTerm) (hij : i ≠ j)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) :
    Eval c₀ 486 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s] (some (.ctor 403 [])) := by
  refine .clause (cl := mFail) (σ := enumFrom 0 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s])
    lookup_match (by simp [fnMatch])
    (ws_enum (.cons (sort_term1 (sort_int i) (by decide +kernel))
      (.cons (sort_term1 (sort_int j) (by decide +kernel)) (.cons hb (.cons hs .nil)))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) .top ?_ rfl (ev_ctor .nil) (fun _ h => by cases h) .top
  intro cl' hm _ hp
  simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hp (by decide)
    | exact fails_at1 rfl (by decide)
    | exact fails_at2 rfl (by decide)
    | skip
  -- m-int: I and J are the two Ints, and `I ==Int J` is `false`
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, _⟩⟩
  obtain ⟨xs, he, hxs⟩ := pv_ctor h0
  cases he
  rcases hxs with _ | ⟨hx, _ | _⟩
  obtain ⟨ys, he, hys⟩ := pv_ctor h1
  cases he
  rcases hys with _ | ⟨hy, _ | _⟩
  refine .intro rfl (ev_int2 (P := (· = ·)) hook_intEq (ev_var (PatVal.var_inv hx)) (ev_var (PatVal.var_inv hy))) ?_
  rw [decide_eq_false hij]
  exact fun h => absurd (bool_inj (Option.some.inj h)) (by decide)

theorem match.eval_iv_ne_iff (i j : Int) (b s : GroundTerm) (hij : i ≠ j)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) {r : Option GroundTerm} :
    Eval c₀ 486 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s] r ↔ r = some (.ctor 403 []) :=
  iff_of_eval (match.eval_iv_ne i j b s hij hb hs)

end KK.Spike.Hand
