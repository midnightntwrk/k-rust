/-
  Helper-lemma spike, as text a generator writes: `F.eval` and `F.eval_iff` for kore.k's `app`,
  `lookup`, `mkInj` and for `match` at two argument lists where only `m-fail` applies.

  Each Lean function is the cascade of its equations in the order of the semantics' clauses, with
  an `Option` result: the first equation that applies gives the value, a partial call's value is
  bound, and where no equation applies the result is `none`. Each proof is one block per branch of
  the cascade, written from the clause's literal alone by fixed forms:
  - the equation of the branch: `Eval.clause` at the substitution that lists the variables' values
    (`enumFrom`), with the patterns' `PatVals`, the `requires` and the right side term by term;
  - for each equation of the function, in order: `absurd hp (by decide)` where its priority is not
    smaller, otherwise `Fails` by inverting its patterns down to the position that refutes it
    (another constructor, the branch's negative hypothesis, or a `requires` with the value `false`);
  - a right side that binds a partial call: the two cases of the call's value;
  - the branch where no equation applies: `Eval.rest`, `Fails` for every equation.
  No block reads another block, and no lemma is about one function.
-/
import User.SpikeBase

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KK.Spike.Cascade

open KCore KCore.Det RefKk KK KK.Kit KK.Spike

/-! ## `app` -/

/-- kore.k's `app` as a cascade. -/
def appC : List GroundTerm → List GroundTerm → Option (List GroundTerm)
  | [], us => some us
  | t :: ts, us => (appC ts us).bind fun r => some (t :: r)

spike_hb in
theorem app.eval (xs ys : List GroundTerm) (hx : ∀ t ∈ xs, c₀.sortOf t = some 33)
    (hy : ∀ t ∈ ys, c₀.sortOf t = some 33) :
    Eval c₀ 447 [tsOf xs, tsOf ys] ((appC xs ys).map tsOf) := by
  induction xs with
  | nil =>
    -- app-nil
    refine Eval.clause (cl := appNil) (σ := enumFrom 0 [tsOf ys]) lookup_app (by simp [fnApp])
      (ws_enum (.cons (sort_ts hy) .nil))
      (.cons (.ctor (by decide +kernel) .nil) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) Holds.top ?_ rfl (ev_var rfl) (fun _ h => by cases h) Holds.top
    intro cl' hm _ hp
    simp only [fnApp, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, c₀.sortOf u = some 33 := fun u hu => hx u (List.mem_cons_of_mem _ hu)
    have ih := ih hts
    -- app-cons
    refine Eval.clause (cl := appCons) (σ := enumFrom 0 [t, tsOf ts, tsOf ys]) lookup_app (by simp [fnApp])
      (ws_enum (.cons (hx t (List.mem_cons_self ..)) (.cons (sort_ts hts) (.cons (sort_ts hy) .nil))))
      (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))
      (fun _ h => by cases h) Holds.top ?_ rfl ?_ (fun _ h => by cases h) Holds.top
    · -- the equations of a smaller priority
      intro cl' hm _ hp
      simp only [fnApp, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
    · -- the right side: the call's value
      simp only [appC]
      cases hr : appC ts ys with
      | none =>
        rw [hr] at ih
        exact EvalTerm.ctor (σ := enumFrom 0 [t, tsOf ts, tsOf ys]) (rs := [some t, none]) (by decide +kernel)
          (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih) .nil))
      | some r =>
        rw [hr] at ih
        exact ev_ctor (.cons (ev_var rfl) (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih) .nil))

theorem app.eval_iff (xs ys : List GroundTerm) (hx : ∀ t ∈ xs, c₀.sortOf t = some 33)
    (hy : ∀ t ∈ ys, c₀.sortOf t = some 33) {r : Option GroundTerm} :
    Eval c₀ 447 [tsOf xs, tsOf ys] r ↔ r = (appC xs ys).map tsOf :=
  ⟨fun h => Eval.functional coherent h (app.eval xs ys hx hy), fun e => e ▸ app.eval xs ys hx hy⟩

/-! ## `lookup` -/

/-- kore.k's `lookup` as a cascade. -/
def lookupC (f : Int) : List (Int × GroundTerm) → Option (Option GroundTerm)
  | (g, cs) :: fs => if f = g then some (some cs) else if f ≠ g then lookupC f fs else none
  | [] => some none

spike_hb in
theorem lookup.eval (f : Int) (fs : List (Int × GroundTerm)) (h : ∀ p ∈ fs, c₀.sortOf p.2 = some 35) :
    Eval c₀ 485 [.dv 3 (.int f), fnsOf fs] ((lookupC f fs).map lookOf) := by
  induction fs with
  | nil =>
    -- lookup-nil
    refine Eval.clause (cl := lkNil) (σ := enumFrom 0 [.dv 3 (.int f)]) lookup_lookup (by simp [fnLookup])
      (ws_enum (.cons (sort_int f) .nil))
      (.cons (.var rfl) (.cons (.ctor (by decide +kernel) .nil) .nil))
      (fun _ h => by cases h) Holds.top ?_ rfl (ev_ctor .nil) (fun _ h => by cases h) Holds.top
    intro cl' hm _ hp
    simp only [fnLookup, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
  | cons p fs ih =>
    obtain ⟨g, cs⟩ := p
    have hfs : ∀ q ∈ fs, c₀.sortOf q.2 = some 35 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have ih := ih hfs
    rw [lookupC]
    by_cases h1 : f = g
    · rw [ite_pos h1]
      -- lookup-hit
      refine Eval.clause (cl := lkHit) (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs])
        lookup_lookup (by simp [fnLookup])
        (ws_enum (.cons (sort_int f) (.cons (sort_int g) (.cons (h (g, cs) (List.mem_cons_self ..))
          (.cons (sort_fns hfs) .nil)))))
        (.cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil))
        ?_ Holds.top ?_ rfl (ev_ctor (.cons (ev_var rfl) .nil)) (fun _ h => by cases h) Holds.top
      · intro t ht
        cases ht
        have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs]) (P := (· = ·))
          hook_intEq (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
        rwa [decide_eq_true h1] at hq
      · intro cl' hm _ hp
        simp only [fnLookup, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
    · rw [ite_neg h1]
      by_cases h2 : f ≠ g
      · rw [ite_pos h2]
        -- lookup-miss
        refine Eval.clause (cl := lkMiss) (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs])
          lookup_lookup (by simp [fnLookup])
          (ws_enum (.cons (sort_int f) (.cons (sort_int g) (.cons (h (g, cs) (List.mem_cons_self ..))
            (.cons (sort_fns hfs) .nil)))))
          (.cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil))
          ?_ Holds.top ?_ rfl (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) ih) (fun _ h => by cases h) Holds.top
        · intro t ht
          cases ht
          have hq := ev_int2 (σ := enumFrom 0 [.dv 3 (.int f), .dv 3 (.int g), cs, fnsOf fs]) (P := (· ≠ ·))
            hook_intNe (ev_var (i := 0) rfl) (ev_var (i := 1) rfl)
          rwa [decide_eq_true h2] at hq
        · intro cl' hm _ hp
          simp only [fnLookup, List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl
          · exact absurd hp (by decide)
          · exact absurd hp (by decide)
          · exact absurd hp (by decide)
      · rw [ite_neg h2]
        -- no equation applies
        refine Eval.rest (fn := fnLookup) lookup_lookup ?_
        intro cl hm
        simp only [fnLookup, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨h0, _ | ⟨h1', _⟩⟩
          obtain ⟨xs, he, hxs⟩ := pv_ctor h1'
          cases he
          rcases hxs with _ | ⟨hx0, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
          refine .intro rfl (ev_int2 (P := (· = ·)) hook_intEq (ev_var (PatVal.var_inv h0)) (ev_var (PatVal.var_inv hx0))) ?_
          rw [decide_eq_false h1]
          exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)
        · refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨h0, _ | ⟨h1', _⟩⟩
          obtain ⟨xs, he, hxs⟩ := pv_ctor h1'
          cases he
          rcases hxs with _ | ⟨hx0, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
          refine .intro rfl (ev_int2 (P := (· ≠ ·)) hook_intNe (ev_var (PatVal.var_inv h0)) (ev_var (PatVal.var_inv hx0))) ?_
          rw [decide_eq_false h2]
          exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)
        · refine .intro fun σ _ hm => ?_
          rcases hm with _ | ⟨_, _ | ⟨h1, _⟩⟩
          obtain ⟨xs, he, -⟩ := pv_ctor h1
          exact absurd (GroundTerm.ctor.inj he).1 (by decide)

theorem lookup.eval_iff (f : Int) (fs : List (Int × GroundTerm)) (h : ∀ p ∈ fs, c₀.sortOf p.2 = some 35)
    {r : Option GroundTerm} :
    Eval c₀ 485 [.dv 3 (.int f), fnsOf fs] r ↔ r = (lookupC f fs).map lookOf :=
  ⟨fun h' => Eval.functional coherent h' (lookup.eval f fs h), fun e => e ▸ lookup.eval f fs h⟩

/-! ## `mkInj` -/

/-- kore.k's `mkInj` as a cascade. -/
def mkInjC (a b t : GroundTerm) : Option GroundTerm :=
  match t with
  | .ctor 424 [c, _, u] => some (.ctor 424 [c, b, u])
  | _ =>
    match t with
    | .ctor 412 [] => some t
    | _ => some (.ctor 424 [a, b, t])

spike_hb in
theorem mkInj.eval (a b t : GroundTerm) (ha : c₀.sortOf a = some 3) (hb : c₀.sortOf b = some 3)
    (ht : c₀.sortOf t = some 33) : Eval c₀ 493 [a, b, t] (mkInjC a b t) := by
  unfold mkInjC
  split
  · next c x u =>
    -- inj-compose
    obtain ⟨hc, hr⟩ := sorts_cons_inv (sort_args ht (as := [3, 3, 33]) (by decide +kernel))
    obtain ⟨hx, hr⟩ := sorts_cons_inv hr
    obtain ⟨hu, -⟩ := sorts_cons_inv hr
    refine Eval.clause (cl := injCompose) (σ := enumFrom 0 [c, x, u, a, b]) lookup_mkInj (by simp [fnMkInj])
      (ws_enum (.cons hc (.cons hx (.cons hu (.cons ha (.cons hb .nil))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor (by decide +kernel)
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) .nil)))
      (fun _ h => by cases h) Holds.top ?_ rfl
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (fun _ h => by cases h) Holds.top
    intro cl' hm _ hp
    simp only [fnMkInj, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
  · next hn1 =>
    split
    · -- inj-bot
      refine Eval.clause (cl := injBot) (σ := enumFrom 0 [b, .ctor 412 [], a]) lookup_mkInj (by simp [fnMkInj])
        (ws_enum (.cons hb (.cons ht (.cons ha .nil))))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor (by decide +kernel) .nil) rfl) .nil)))
        (fun _ h => by cases h) Holds.top ?_ rfl (ev_var rfl) (fun _ h => by cases h) Holds.top
      intro cl' hm _ hp
      simp only [fnMkInj, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
    · next hn2 =>
      -- inj-new
      refine Eval.clause (cl := injNew) (σ := enumFrom 0 [a, b, t]) lookup_mkInj (by simp [fnMkInj])
        (ws_enum (.cons ha (.cons hb (.cons ht .nil))))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (fun _ h => by cases h) Holds.top ?_ rfl
        (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (fun _ h => by cases h) Holds.top
      intro cl' hm _ hp
      simp only [fnMkInj, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · refine .intro fun σ _ hm => ?_
        rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h2, _⟩⟩⟩
        obtain ⟨xs, he, hxs⟩ := pv_ctor h2
        rcases hxs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
        exact (hn1 _ _ _ he).elim
      · refine .intro fun σ _ hm => ?_
        rcases hm with _ | ⟨_, _ | ⟨_, _ | ⟨h2, _⟩⟩⟩
        obtain ⟨xs, he, hxs⟩ := pv_ctor (PatVal.as_inv h2).1
        rcases hxs with _ | _
        exact (hn2 he).elim
      · exact absurd hp (by decide)

theorem mkInj.eval_iff (a b t : GroundTerm) (ha : c₀.sortOf a = some 3) (hb : c₀.sortOf b = some 3)
    (ht : c₀.sortOf t = some 33) {r : Option GroundTerm} :
    Eval c₀ 493 [a, b, t] r ↔ r = mkInjC a b t :=
  ⟨fun h => Eval.functional coherent h (mkInj.eval a b t ha hb ht), fun e => e ▸ mkInj.eval a b t ha hb ht⟩

/-! ## `match` where only `m-fail` applies -/

spike_hb in
/-- `match(iv(I), bv(Y), B, S)` is `.Ms`: the branch of `match`'s cascade at `iv` against `bv`. -/
theorem match.eval_iv_bv (i y b s : GroundTerm) (hi : c₀.sortOf i = some 3) (hy : c₀.sortOf y = some 2)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) :
    Eval c₀ 486 [.ctor 425 [i], .ctor 413 [y], b, s] (some (.ctor 403 [])) := by
  -- m-fail
  refine Eval.clause (cl := mFail) (σ := enumFrom 0 [.ctor 425 [i], .ctor 413 [y], b, s]) lookup_match (by simp [fnMatch])
    (ws_enum (.cons (sort_ctor (by decide +kernel) (sorts_cons hi sorts_nil))
      (.cons (sort_ctor (by decide +kernel) (sorts_cons hy sorts_nil)) (.cons hb (.cons hs .nil)))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) Holds.top ?_ rfl (ev_ctor .nil) (fun _ h => by cases h) Holds.top
  intro cl' hm _ hp
  simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨_, _ | ⟨h1, _⟩⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h1
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · exact absurd hp (by decide)

theorem match.eval_iv_bv_iff (i y b s : GroundTerm) (hi : c₀.sortOf i = some 3) (hy : c₀.sortOf y = some 2)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) {r : Option GroundTerm} :
    Eval c₀ 486 [.ctor 425 [i], .ctor 413 [y], b, s] r ↔ r = some (.ctor 403 []) :=
  ⟨fun h => Eval.functional coherent h (match.eval_iv_bv i y b s hi hy hb hs),
   fun e => e ▸ match.eval_iv_bv i y b s hi hy hb hs⟩

spike_hb in
/-- `match(iv(I), iv(J), B, S)` is `.Ms` where I and J differ: the branch of `match`'s cascade at
`iv` against `iv` where `m-int`'s `requires` is `false`. -/
theorem match.eval_iv_ne (i j : Int) (b s : GroundTerm) (hij : ¬ i = j)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) :
    Eval c₀ 486 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s] (some (.ctor 403 [])) := by
  -- m-fail
  refine Eval.clause (cl := mFail) (σ := enumFrom 0 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s])
    lookup_match (by simp [fnMatch])
    (ws_enum (.cons (sort_ctor (by decide +kernel) (sorts_cons (sort_int i) sorts_nil))
      (.cons (sort_ctor (by decide +kernel) (sorts_cons (sort_int j) sorts_nil)) (.cons hb (.cons hs .nil)))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) Holds.top ?_ rfl (ev_ctor .nil) (fun _ h => by cases h) Holds.top
  intro cl' hm _ hp
  simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _ | ⟨h1, _⟩⟩
    obtain ⟨xs, he, hxs⟩ := pv_ctor h0
    cases he
    rcases hxs with _ | ⟨hx0, _ | _⟩
    obtain ⟨ys, he, hys⟩ := pv_ctor h1
    cases he
    rcases hys with _ | ⟨hy0, _ | _⟩
    refine .intro rfl (ev_int2 (P := (· = ·)) hook_intEq (ev_var (PatVal.var_inv hx0)) (ev_var (PatVal.var_inv hy0))) ?_
    rw [decide_eq_false hij]
    exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => ?_
    rcases hm with _ | ⟨h0, _⟩
    obtain ⟨xs, he, -⟩ := pv_ctor h0
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · exact absurd hp (by decide)

theorem match.eval_iv_ne_iff (i j : Int) (b s : GroundTerm) (hij : ¬ i = j)
    (hb : c₀.sortOf b = some 46) (hs : c₀.sortOf s = some 32) {r : Option GroundTerm} :
    Eval c₀ 486 [.ctor 425 [.dv 3 (.int i)], .ctor 425 [.dv 3 (.int j)], b, s] r ↔ r = some (.ctor 403 []) :=
  ⟨fun h => Eval.functional coherent h (match.eval_iv_ne i j b s hij hb hs),
   fun e => e ▸ match.eval_iv_ne i j b s hij hb hs⟩

end KK.Spike.Cascade
