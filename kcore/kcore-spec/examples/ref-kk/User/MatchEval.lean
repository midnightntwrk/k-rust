/-
  kore.k's `match`, `matchTs` and `matchK` on embedded mirrors: their value at `K₀ sig` is the
  mirror's (`matchF`, `matchTsF`, `matchKF`, KKMatchF.lean), with no hypothesis on the subsort
  table, for a pattern without a collection pattern (`noCb`).

  `match_eval`: `match(emb p, emb a, embB B, embS S)` evaluates to `(matchF S p a B).map embMs`.
  The proof follows the pattern: one step per constructor of the pattern (`matchAt_vr_kme`, …), each
  taking the evaluation of `match` or `matchTs` at the pattern's parts, and the steps are put
  together by induction on the pattern (`matchAt_noCb_kme`) and on lists (`matchTsAt_of_kme`).
  In each step the equation of `match` that applies is `Eval.clause` at that equation; where none of
  priority 50 applies, `m-fail` (`match_fail_kme`) with each other equation failing on its first
  pattern's head (`fails1_kme`), or on its second pattern or its `requires` (`mInt_fails_kme`, …).
  `m-inj-sub`'s `requires` calls `leq`, whose value is `leqF` at every table (`leq_eval_leqF`): so
  `m-inj-sub` applies exactly where `matchF` takes its branch, whether or not the table is
  transitive. `matchTs` at two lists of different lengths has no equation and no value (`Eval.rest`
  and `fnRest_none`), as `matchTsF` gives `none`; a call at an argument without a value has none
  (`EvalTerm.callUndef`), as `matchF` propagates `none`.

  A collection pattern's step (`matchAt_cb_kme`) takes `matchCol`'s evaluation as a hypothesis.
-/
import User.HelpTerms
import User.Leq
import User.SpikeBase

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

/-- Symbols 486 to 489 are kore.k's `match`, `matchCol`, `matchK` and `matchTs`. -/
theorem matchEval_names_kme :
    RefKk.defn.sem.symName 486 =
      "Lblmatch'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Term'Unds'Term'Unds'Bind'Unds'Subs" ∧
    RefKk.defn.sem.symName 487 =
      "LblmatchCol'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Kind'Unds'Int'Unds'Ts'Unds'Ts'Unds'Bind'Unds'Subs" ∧
    RefKk.defn.sem.symName 488 =
      "LblmatchK'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Ms'Unds'Ts'Unds'Ts'Unds'Subs" ∧
    RefKk.defn.sem.symName 489 =
      "LblmatchTs'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Ts'Unds'Ts'Unds'Bind'Unds'Subs" := by
  decide +kernel

/-! ## The clauses of `matchTs` and `matchK`, as the semantics holds them

`match`'s are User.SpikeBase's `fnMatch`. -/

namespace MatchClauses
open _root_.KK Terms

/-- `ms-nil`. -/
def msNil : Clause := plainCl [46, 32] [.app 406 [], .app 406 [], .var 0, .var 1] (.app 428 [.var 0, .app 403 []])

/-- `ms-cons`. -/
def msCons : Clause :=
  plainCl [33, 43, 33, 43, 46, 32] [.app 407 [.var 0, .var 1], .app 407 [.var 2, .var 3], .var 4, .var 5]
    (.app 488 [.app 486 [.var 0, .var 2, .var 4, .var 5], .var 1, .var 3, .var 5])

/-- `matchTs` (489). -/
def matchTsDef : Fn :=
  { label := 489, args := [43, 43, 46, 32], result := 37, total := false, clauses := [msNil, msCons] }

/-- `mk-fail`. -/
def mkFail : Clause := plainCl [37, 43, 43, 32] [.as (.app 403 []) 0, .var 1, .var 2, .var 3] (.var 0)

/-- `mk-ok`. -/
def mkOk : Clause :=
  plainCl [46, 37, 43, 43, 32] [.app 428 [.var 0, .var 1], .var 2, .var 3, .var 4]
    (.app 453 [.app 489 [.var 2, .var 3, .var 0, .var 4], .app 488 [.var 1, .var 2, .var 3, .var 4]])

/-- `matchK` (488). -/
def matchKDef : Fn :=
  { label := 488, args := [37, 43, 43, 32], result := 37, total := false, clauses := [mkFail, mkOk] }

theorem matchTsDef_lookup : c₀.lookupFn 489 = some matchTsDef := by kernel_rfl
theorem matchKDef_lookup : c₀.lookupFn 488 = some matchKDef := by kernel_rfl

end MatchClauses

/-! ## Shared steps -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts _root_.KK.Spike

/-- A constructor pattern that denotes `emb t` is at `t`'s head, and its arguments denote `t`'s. -/
theorem pv_emb_kme {σ : Subst} {g : Sym} {qs : List Term} {t : T} (h : PatVal c₀ σ (.app g qs) (emb t))
    (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) :
    headOf t = g ∧ PatVals c₀ σ qs (argsOf t) := by
  obtain ⟨xs, he, hxs⟩ := pv_ctor h hc hk
  rw [emb_ctor] at he
  obtain ⟨h1, h2⟩ := GroundTerm.ctor.inj he
  exact ⟨h1, by rw [h2]; exact hxs⟩

/-- A clause whose first pattern is at another head than the first argument fails. -/
theorem fails1_kme {cl : Clause} {g : Sym} {ps rest : List Term} {p : T} {vs : List GroundTerm}
    (hp : cl.pats = .app g ps :: rest) (hg : headOf p ≠ g) (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ (emb p :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨_, _, he, hv, -⟩ := PatVals.cons_inv hm
  cases he
  exact absurd (pv_emb_kme hv hc hk).1 hg

/-- A clause whose second pattern is at another head than the second argument fails. -/
theorem fails2_kme {cl : Clause} {g : Sym} {q : Term} {ps rest : List Term} {w : GroundTerm} {t : T}
    {vs : List GroundTerm} (hp : cl.pats = q :: .app g ps :: rest) (hg : headOf t ≠ g)
    (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ (w :: emb t :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨_, _, he, -, hm'⟩ := PatVals.cons_inv hm
  cases he
  obtain ⟨_, _, he, hv, -⟩ := PatVals.cons_inv hm'
  cases he
  exact absurd (pv_emb_kme hv hc hk).1 hg

/-- A constructor pattern denotes no constructor term of another head. -/
theorem failsCtor_kme {cl : Clause} {g h : Sym} {ps rest : List Term} {us vs : List GroundTerm}
    (hp : cl.pats = .app g ps :: rest) (hg : g ≠ h) (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ (.ctor h us :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨_, _, he, hv, -⟩ := PatVals.cons_inv hm
  cases he
  obtain ⟨_, he, -⟩ := pv_ctor hv hc hk
  exact (hg (GroundTerm.ctor.inj he).1.symm).elim

theorem failsCtor2_kme {cl : Clause} {g h : Sym} {q : Term} {ps rest : List Term} {w : GroundTerm}
    {us vs : List GroundTerm} (hp : cl.pats = q :: .app g ps :: rest) (hg : g ≠ h)
    (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ (w :: .ctor h us :: vs) cl := by
  refine .intro fun σ _ hm => ?_
  rw [hp] at hm
  obtain ⟨_, _, he, -, hm'⟩ := PatVals.cons_inv hm
  cases he
  obtain ⟨_, _, he, hv, -⟩ := PatVals.cons_inv hm'
  cases he
  obtain ⟨_, he, -⟩ := pv_ctor hv hc hk
  exact (hg (GroundTerm.ctor.inj he).1.symm).elim

/-- A hooked symbol of two arguments at their values. -/
theorem ev_hook2_kme {σ : Subst} {f : Sym} {t u : Term} {x y r : GroundTerm}
    (ht : EvalTerm c₀ σ t (some x)) (hu : EvalTerm c₀ σ u (some y)) (hh : hook f [x, y] = some (some r))
    (hc : c₀.isCtor f = false := by decide +kernel) (hk : isHook f = true := by decide +kernel) :
    EvalTerm c₀ σ (.app f [t, u]) (some r) := by
  refine .hook hc hk (EvArgs.terms (.cons ht (.cons hu .nil))) (fun vs hvs => ?_) (fun hn => ?_)
  · rw [_root_.KCore.allSome_map_some] at hvs
    cases hvs
    exact Semantics.hookRes_of_value hh
  · rw [_root_.KCore.allSome_map_some] at hn; cases hn

theorem hook_boolEq_kme (x y : Bool) : hook boolEq [.dv 2 (.bool x), .dv 2 (.bool y)] = some (some (bool (x == y))) :=
  rfl

theorem hook_boolAnd_kme (x y : Bool) : hook boolAnd [bool x, bool y] = some (some (bool (x && y))) := rfl

theorem hook_stringEq_kme (x y : String) :
    hook stringEq [.dv 10 (.tok x), .dv 10 (.tok y)] = some (some (bool (decide (x = y)))) := by
  have h : hook stringEq [.dv 10 (.tok x), .dv 10 (.tok y)] = some (some (bool (x.toList == y.toList))) := rfl
  rw [h]
  by_cases e : x = y
  · subst e; simp
  · have : (x.toList == y.toList) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => e (String.toList_injective h)
    rw [this, decide_eq_false e]

/-- `I ==Int J` at two variables. -/
theorem req_intEq_kme {σ : Subst} {i j : Nat} {x y : Int} (hi : σ.lookup i = some (.dv 3 (.int x)))
    (hj : σ.lookup j = some (.dv 3 (.int y))) :
    EvalTerm c₀ σ (.app 23 [.var i, .var j]) (some (bool (decide (x = y)))) :=
  ev_int2 (P := (· = ·)) hook_intEq (ev_var hi) (ev_var hj) notCtor_23 isHook_23

/-- `X ==Bool Y` at two variables. -/
theorem req_boolEq_kme {σ : Subst} {i j : Nat} {x y : Bool} (hi : σ.lookup i = some (.dv 2 (.bool x)))
    (hj : σ.lookup j = some (.dv 2 (.bool y))) :
    EvalTerm c₀ σ (.app 10 [.var i, .var j]) (some (bool (x == y))) :=
  ev_hook2_kme (ev_var hi) (ev_var hj) (hook_boolEq_kme x y)

/-- `m-tok`'s `requires`: `S ==Int T andBool X ==String Y`. -/
theorem req_tok_kme {σ : Subst} {s t : Int} {x y : String} (h2 : σ.lookup 2 = some (.dv 3 (.int s)))
    (h3 : σ.lookup 3 = some (.dv 10 (.tok x))) (h4 : σ.lookup 4 = some (.dv 3 (.int t)))
    (h5 : σ.lookup 5 = some (.dv 10 (.tok y))) :
    EvalTerm c₀ σ (.app 4 [.app 23 [.var 2, .var 4], .app 285 [.var 3, .var 5]])
      (some (bool (decide (s = t) && decide (x = y)))) :=
  ev_hook2_kme (req_intEq_kme h2 h4) (ev_hook2_kme (ev_var h3) (ev_var h5) (hook_stringEq_kme x y))
    (hook_boolAnd_kme _ _)

/-- `m-inj-sub`'s `requires`: `A =/=Int C andBool leq(C, A, S)`. -/
theorem req_injSub_kme {σ : Subst} {a c : Int} {S : List (Int × Int)}
    (h0 : σ.lookup 0 = some (.dv 3 (.int a))) (h7 : σ.lookup 7 = some (.dv 3 (.int c)))
    (h4 : σ.lookup 4 = some (embS S)) :
    EvalTerm c₀ σ (.app 4 [.app 24 [.var 0, .var 7], .app 482 [.var 7, .var 0, .var 4]])
      (some (bool (decide (a ≠ c) && leqF c a S))) :=
  ev_hook2_kme (ev_int2 (P := (· ≠ ·)) hook_intNe (ev_var h0) (ev_var h7) notCtor_24 isHook_24)
    (ev_call (.cons (ev_var h7) (.cons (ev_var h0) (.cons (ev_var h4) .nil))) (leq_eval_leqF c a S)
      notCtor_482 notHook_482 notParam_482)
    (hook_boolAnd_kme _ _)

theorem req_intEq_true_kme {σ : Subst} {i j : Nat} {x : Int} (hi : σ.lookup i = some (.dv 3 (.int x)))
    (hj : σ.lookup j = some (.dv 3 (.int x))) : EvalTerm c₀ σ (.app 23 [.var i, .var j]) (some (bool true)) := by
  have h := req_intEq_kme hi hj
  rwa [decide_eq_true rfl] at h

theorem req_boolEq_true_kme {σ : Subst} {i j : Nat} {x : Bool} (hi : σ.lookup i = some (.dv 2 (.bool x)))
    (hj : σ.lookup j = some (.dv 2 (.bool x))) : EvalTerm c₀ σ (.app 10 [.var i, .var j]) (some (bool true)) := by
  have h := req_boolEq_kme hi hj
  rwa [beq_self_eq_true] at h

theorem req_tok_true_kme {σ : Subst} {s : Int} {x : String} (h2 : σ.lookup 2 = some (.dv 3 (.int s)))
    (h3 : σ.lookup 3 = some (.dv 10 (.tok x))) (h4 : σ.lookup 4 = some (.dv 3 (.int s)))
    (h5 : σ.lookup 5 = some (.dv 10 (.tok x))) :
    EvalTerm c₀ σ (.app 4 [.app 23 [.var 2, .var 4], .app 285 [.var 3, .var 5]]) (some (bool true)) := by
  have h := req_tok_kme h2 h3 h4 h5
  rwa [decide_eq_true rfl, decide_eq_true rfl] at h

theorem req_injSub_true_kme {σ : Subst} {a c : Int} {S : List (Int × Int)} (hac : a ≠ c)
    (hle : leqF c a S = true) (h0 : σ.lookup 0 = some (.dv 3 (.int a))) (h7 : σ.lookup 7 = some (.dv 3 (.int c)))
    (h4 : σ.lookup 4 = some (embS S)) :
    EvalTerm c₀ σ (.app 4 [.app 24 [.var 0, .var 7], .app 482 [.var 7, .var 0, .var 4]]) (some (bool true)) := by
  have h := req_injSub_kme (S := S) h0 h7 h4
  rwa [decide_eq_true hac, hle] at h

theorem fnMatch_mem_kme {cl : Clause} (n : Nat) (h : fnMatch.clauses[n]? = some cl) : cl ∈ fnMatch.clauses :=
  List.mem_of_getElem? h

theorem bool_ne_true_kme {b : Bool} (h : b = false) : some (bool b) ≠ some (bool true) := by
  subst h; exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)

/-- Where every equation of `match` of priority 50 fails, `m-fail` gives no substitution. -/
theorem match_fail_kme {p t : T} {B : Bind} {S : List (Int × Int)}
    (h : ∀ cl ∈ fnMatch.clauses, cl.prio < 200 → Fails c₀ [emb p, emb t, embB B, embS S] cl) :
    Eval c₀ 486 [emb p, emb t, embB B, embS S] (some (embMs [])) :=
  .clause (cl := mFail) (σ := enumFrom 0 [emb p, emb t, embB B, embS S]) lookup_match (fnMatch_mem_kme 11 rfl)
    (ws_enum (.cons (emb_sorted_c₀ p) (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B)
      (.cons (embS_sorted_c₀ S) .nil)))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) .top (fun cl hm _ hlt => h cl hm hlt) rfl (ev_ctor .nil ctor_403)
    (fun _ h => by cases h) .top

end Kit

set_option hygiene false in
/-- The equations of `match` other than `m-fail`, at arguments whose first is `emb p`: each whose
first pattern is at another head than `p` fails; the others are left as goals, in the order of the
semantics' clause list. -/
macro "kme_heads" : tactic => `(tactic| (
  intro cl hm hlt
  simp only [_root_.KK.Spike.fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hlt (by decide)
    | (refine fails1_kme rfl ?_; simp [headOf]; done)
    | skip))

/-! ## The equations that apply at a pattern's own head and do not decide -/

section Own
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts _root_.KK.Spike

theorem mInt_fails_kme {i : Int} {t : T} {b s : GroundTerm} (h : ∀ j, t = .iv j → i ≠ j) :
    Fails c₀ [emb (.iv i), emb t, b, s] mInt := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨j, rfl⟩ := headOf_eq_iv.mp hh
  rcases hx with _ | ⟨hx, -⟩
  rcases hy with _ | ⟨hy, -⟩
  exact .intro rfl (req_intEq_kme (PatVal.var_inv hx) (PatVal.var_inv hy))
    (bool_ne_true_kme (decide_eq_false (h j rfl)))

theorem mBool_fails_kme {x : Bool} {t : T} {b s : GroundTerm} (h : ∀ y, t = .bv y → x ≠ y) :
    Fails c₀ [emb (.bv x), emb t, b, s] mBool := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨y, rfl⟩ := headOf_eq_bv.mp hh
  rcases hx with _ | ⟨hx, -⟩
  rcases hy with _ | ⟨hy, -⟩
  exact .intro rfl (req_boolEq_kme (PatVal.var_inv hx) (PatVal.var_inv hy))
    (bool_ne_true_kme (beq_eq_false_iff_ne.mpr (h y rfl)))

theorem mTok_fails_kme {s : Int} {x : String} {t : T} {b w : GroundTerm}
    (h : ∀ s' y, t = .tk s' y → ¬ (s = s' ∧ x = y)) : Fails c₀ [emb (.tk s x), emb t, b, w] mTok := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨s', y, rfl⟩ := headOf_eq_tk.mp hh
  rcases hx with _ | ⟨hx2, _ | ⟨hx3, -⟩⟩
  rcases hy with _ | ⟨hy4, _ | ⟨hy5, -⟩⟩
  refine .intro rfl (req_tok_kme (PatVal.var_inv hx2) (PatVal.var_inv hx3) (PatVal.var_inv hy4)
    (PatVal.var_inv hy5)) (bool_ne_true_kme ?_)
  have := h s' y rfl
  rw [Bool.and_eq_false_iff]
  by_cases e : s = s'
  · exact .inr (decide_eq_false fun e' => this ⟨e, e'⟩)
  · exact .inl (decide_eq_false e)

theorem mApp_fails_kme {f : Int} {ps : List T} {t : T} {b s : GroundTerm} (h : ∀ g ts, t = .ap g ts → f ≠ g) :
    Fails c₀ [emb (.ap f ps), emb t, b, s] mApp := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨g, ts, rfl⟩ := headOf_eq_ap.mp hh
  rcases hx with _ | ⟨hx, -⟩
  rcases hy with _ | ⟨hy, -⟩
  exact .intro rfl (req_intEq_kme (PatVal.var_inv hx) (PatVal.var_inv hy))
    (bool_ne_true_kme (decide_eq_false (h g ts rfl)))

theorem mInjSame_fails_kme {a b : Int} {p t : T} {w s : GroundTerm} (h : ∀ c e u, t = .ij c e u → a ≠ c) :
    Fails c₀ [emb (.ij a b p), emb t, w, s] mInjSame := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨c, e, u, rfl⟩ := headOf_eq_ij.mp hh
  rcases hx with _ | ⟨hx, -⟩
  rcases hy with _ | ⟨hy, -⟩
  exact .intro rfl (req_intEq_kme (PatVal.var_inv hx) (PatVal.var_inv hy))
    (bool_ne_true_kme (decide_eq_false (h c e u rfl)))

theorem mInjSub_fails_kme {a b : Int} {p t : T} {w : GroundTerm} {S : List (Int × Int)}
    (h : ∀ c e u, t = .ij c e u → a = c ∨ leqF c a S = false) :
    Fails c₀ [emb (.ij a b p), emb t, w, embS S] mInjSub := by
  refine .intro fun σ _ hm => ?_
  rcases hm with _ | ⟨h0, _ | ⟨h1, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩⟩
  obtain ⟨-, hx⟩ := pv_emb_kme h0
  obtain ⟨hh, hy⟩ := pv_emb_kme h1
  obtain ⟨c, e, u, rfl⟩ := headOf_eq_ij.mp hh
  rcases hx with _ | ⟨hx, -⟩
  rcases hy with _ | ⟨hy, -⟩
  refine .intro rfl (req_injSub_kme (PatVal.var_inv hx) (PatVal.var_inv hy) (PatVal.var_inv h3))
    (bool_ne_true_kme ?_)
  rcases h c e u rfl with hac | hle
  · subst hac; simp
  · rw [hle]; simp

theorem mKv_fails_kme {p q t : T} {w s : GroundTerm} (h : ∀ k v, t ≠ .kv k v) :
    Fails c₀ [emb (.kv p q), emb t, w, s] mKv :=
  fails2_kme rfl fun e => by obtain ⟨k, v, rfl⟩ := headOf_eq_kv.mp e; exact h k v rfl

theorem mEl_fails_kme {p t : T} {w s : GroundTerm} (h : ∀ x, t ≠ .el x) :
    Fails c₀ [emb (.el p), emb t, w, s] mEl :=
  fails2_kme rfl fun e => by obtain ⟨x, rfl⟩ := headOf_eq_el.mp e; exact h x rfl

theorem mCol_fails_kme {k : Kind} {c : Int} {ps : List T} {t : T} {w s : GroundTerm}
    (h : ∀ l e es, t ≠ .co l e es) : Fails c₀ [emb (.cb k c ps), emb t, w, s] mCol :=
  fails2_kme rfl fun e => by obtain ⟨l, e', es, rfl⟩ := headOf_eq_co.mp e; exact h l e' es rfl

end Own

/-! ## One step per head of the pattern -/

/-- `match` at the pattern `p`, against every term and substitution, evaluates to `matchF`'s
substitutions. -/
def MatchAtKme (S : List (Int × Int)) (p : T) : Prop :=
  ∀ t B, Eval _root_.KK.c₀ 486 [emb p, emb t, embB B, embS S] ((matchF S p t B).map embMs)

/-- `matchTs` at the patterns `ps`, against every list of terms and substitution, evaluates to
`matchTsF`'s substitutions. -/
def MatchTsAtKme (S : List (Int × Int)) (ps : List T) : Prop :=
  ∀ ts B, Eval _root_.KK.c₀ 489 [embTs ps, embTs ts, embB B, embS S] ((matchTsF S ps ts B).map embMs)

section Steps
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts _root_.KK.Spike Terms MatchClauses

variable (S : List (Int × Int))

/-- `m-var`. -/
theorem matchAt_vr_kme (x : Int) : MatchAtKme S (.vr x) := by
  intro t B
  rw [matchF_vr]
  exact clause_kht (cl := mVar) (σ := enumFrom 0 [.dv 3 (.int x), emb t, embB B, embS S]) lookup_match
    (fnMatch_mem_kme 10 rfl)
    (ws_enum (.cons (sort_int x) (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))))
    (.cons (.ctor ctor_445 (.cons (.var rfl) .nil)) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
        (.cons (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (look_eval_kht x B)
          notCtor_484 notHook_484 notParam_484) .nil))))
      (bindVarF_eval_c₀ x t B (lookF x B)) notCtor_452 notHook_452 notParam_452)

/-- `m-as`: `bindAfter` of the inner match, undefined where that is. -/
theorem matchAt_as_kme {p : T} (x : Int) (ih : MatchAtKme S p) : MatchAtKme S (.as p x) := by
  intro t B
  rw [matchF_as]
  have hin := ev_call (σ := enumFrom 0 [emb t, embB B, embS S, emb p, .dv 3 (.int x)]) (f := 486)
    (ts := [.var 3, .var 0, .var 1, .var 2])
    (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih t B)
    notCtor_486 notHook_486 notParam_486
  refine clause_kht (cl := mAs) (σ := enumFrom 0 [emb t, embB B, embS S, emb p, .dv 3 (.int x)]) lookup_match
    (fnMatch_mem_kme 1 rfl)
    (ws_enum (.cons (emb_sorted_c₀ t) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S)
      (.cons (emb_sorted_c₀ p) (.cons (sort_int x) .nil))))))
    (.cons (.ctor ctor_409 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
  generalize matchF S p t B = o at hin ⊢
  cases o with
  | none =>
    exact .callUndef notCtor_451 notHook_451 (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons hin .nil))) rfl
      notParam_451
  | some ms =>
    exact ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons hin .nil))) (bindAfterF_eval_c₀ x t ms)
      notCtor_451 notHook_451 notParam_451

/-- `m-int`, else `m-fail`. -/
theorem matchAt_iv_kme (i : Int) : MatchAtKme S (.iv i) := by
  intro t B
  rw [matchF_iv]
  by_cases ht : t = .iv i
  · subst ht
    rw [ite_pos rfl]
    exact clause_kht (cl := mInt) (σ := enumFrom 0 [.dv 3 (.int i), .dv 3 (.int i), embB B, embS S]) lookup_match
      (fnMatch_mem_kme 7 rfl)
      (ws_enum (.cons (sort_int i) (.cons (sort_int i) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))))
      (.cons (.ctor ctor_425 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_425 (.cons (.var rfl) .nil))
        (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun q hq => by cases hq; exact req_intEq_true_kme rfl rfl) (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  · rw [ite_neg ht]
    apply match_fail_kme
    kme_heads
    exact mInt_fails_kme fun j h hij => ht (by rw [h, hij])

/-- `m-bool`, else `m-fail`. -/
theorem matchAt_bv_kme (x : Bool) : MatchAtKme S (.bv x) := by
  intro t B
  rw [matchF_bv]
  by_cases ht : t = .bv x
  · subst ht
    rw [ite_pos rfl]
    exact clause_kht (cl := mBool) (σ := enumFrom 0 [embB B, .dv 2 (.bool x), .dv 2 (.bool x), embS S])
      lookup_match (fnMatch_mem_kme 2 rfl)
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (sort_bool x) (.cons (sort_bool x) (.cons (embS_sorted_c₀ S) .nil)))))
      (.cons (.ctor ctor_413 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_413 (.cons (.var rfl) .nil))
        (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun q hq => by cases hq; exact req_boolEq_true_kme rfl rfl) (by decide)
      ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  · rw [ite_neg ht]
    apply match_fail_kme
    kme_heads
    exact mBool_fails_kme fun y h hxy => ht (by rw [h, hxy])

/-- `m-tok`, else `m-fail`. -/
theorem matchAt_tk_kme (s : Int) (x : String) : MatchAtKme S (.tk s x) := by
  intro t B
  rw [matchF_tk]
  by_cases ht : t = .tk s x
  · subst ht
    rw [ite_pos rfl]
    exact clause_kht (cl := mTok)
      (σ := enumFrom 0 [embB B, embS S, .dv 3 (.int s), .dv 10 (.tok x), .dv 3 (.int s), .dv 10 (.tok x)])
      lookup_match (fnMatch_mem_kme 9 rfl)
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) (.cons (sort_int s) (.cons (sort_string_kemb x)
        (.cons (sort_int s) (.cons (sort_string_kemb x) .nil)))))))
      (.cons (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_443 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun q hq => by cases hq; exact req_tok_true_kme rfl rfl rfl rfl)
      (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  · rw [ite_neg ht]
    apply match_fail_kme
    kme_heads
    exact mTok_fails_kme fun s' y h ⟨hs, hxy⟩ => ht (by rw [h, hs, hxy])

/-- `m-app`, else `m-fail`. -/
theorem matchAt_ap_kme (f : Int) {ps : List T} (ih : MatchTsAtKme S ps) : MatchAtKme S (.ap f ps) := by
  intro u B
  by_cases hu : ∃ ts, u = .ap f ts
  · obtain ⟨ts, rfl⟩ := hu
    rw [matchF_ap_ap, ite_pos rfl]
    exact clause_kht (cl := mApp)
      (σ := enumFrom 0 [.dv 3 (.int f), embS S, embTs ps, .dv 3 (.int f), embTs ts, embB B])
      lookup_match (fnMatch_mem_kme 0 rfl)
      (ws_enum (.cons (sort_int f) (.cons (embS_sorted_c₀ S) (.cons (embTs_sorted_c₀ ps) (.cons (sort_int f)
        (.cons (embTs_sorted_c₀ ts) (.cons (embB_sorted_c₀ B) .nil)))))))
      (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_408 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun q hq => by cases hq; exact req_intEq_true_kme rfl rfl) (by decide)
      ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih ts B)
        notCtor_489 notHook_489 notParam_489)
  · have e : matchF S (.ap f ps) u B = some [] := by
      cases u with
      | ap g ts => rw [matchF_ap_ap, ite_neg fun h => hu ⟨ts, by rw [h]⟩]
      | _ => unfold matchF; rfl
    rw [e]
    apply match_fail_kme
    kme_heads
    exact mApp_fails_kme fun g ts h hfg => hu ⟨ts, by rw [h, hfg]⟩

/-- `m-inj-same`, `m-inj-sub`, else `m-fail`. -/
theorem matchAt_ij_kme {p : T} (a b : Int) (ih : MatchAtKme S p) : MatchAtKme S (.ij a b p) := by
  intro u B
  by_cases hu : ∃ c e t, u = .ij c e t
  · obtain ⟨c, e, t, rfl⟩ := hu
    rw [matchF_ij_ij]
    by_cases hac : a = c
    · subst hac
      rw [ite_pos rfl]
      exact clause_kht (cl := mInjSame)
        (σ := enumFrom 0 [.dv 3 (.int a), embB B, embS S, emb p, .dv 3 (.int a), .dv 3 (.int e), emb t,
          .dv 3 (.int b)])
        lookup_match (fnMatch_mem_kme 5 rfl)
        (ws_enum (.cons (sort_int a) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) (.cons (emb_sorted_c₀ p)
          (.cons (sort_int a) (.cons (sort_int e) (.cons (emb_sorted_c₀ t) (.cons (sort_int b) .nil)))))))))
        (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
          (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
            (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (fun q hq => by cases hq; exact req_intEq_true_kme rfl rfl) (by decide)
        ⟨rfl, rfl, rfl, rfl⟩
        (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih t B)
          notCtor_486 notHook_486 notParam_486)
    · rw [ite_neg hac]
      by_cases hle : leqF c a S = true
      · rw [ite_pos hle]
        exact clause_kht (cl := mInjSub)
          (σ := enumFrom 0 [.dv 3 (.int a), .dv 3 (.int b), emb p, embB B, embS S, .dv 3 (.int e), emb t,
            .dv 3 (.int c)])
          lookup_match (fnMatch_mem_kme 6 rfl)
          (ws_enum (.cons (sort_int a) (.cons (sort_int b) (.cons (emb_sorted_c₀ p) (.cons (embB_sorted_c₀ B)
            (.cons (embS_sorted_c₀ S) (.cons (sort_int e) (.cons (emb_sorted_c₀ t) (.cons (sort_int c) .nil)))))))))
          (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
            (.cons (.ctor ctor_424 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
              (.cons (.var rfl) (.cons (.var rfl) .nil))))
          (fun q hq => by cases hq; exact req_injSub_true_kme hac hle rfl rfl rfl)
          (by decide) ⟨rfl, rfl, rfl, rfl⟩
          (ev_call (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))
              ctor_424) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih (.ij c a t) B)
            notCtor_486 notHook_486 notParam_486)
      · rw [ite_neg hle]
        apply match_fail_kme
        kme_heads
        · exact mInjSame_fails_kme fun c' e' t' h => by cases h; exact hac
        · exact mInjSub_fails_kme fun c' e' t' h => by cases h; exact .inr (by simpa using hle)
  · have e : matchF S (.ij a b p) u B = some [] := by
      cases u with
      | ij c e t => exact absurd ⟨c, e, t, rfl⟩ hu
      | _ => unfold matchF; rfl
    rw [e]
    apply match_fail_kme
    kme_heads
    · exact mInjSame_fails_kme fun c' e' t' h => absurd ⟨c', e', t', h⟩ hu
    · exact mInjSub_fails_kme fun c' e' t' h => absurd ⟨c', e', t', h⟩ hu

/-- `m-kv`, else `m-fail`. -/
theorem matchAt_kv_kme {p q : T} (ih : MatchTsAtKme S [p, q]) : MatchAtKme S (.kv p q) := by
  intro u B
  by_cases hu : ∃ k v, u = .kv k v
  · obtain ⟨k, v, rfl⟩ := hu
    rw [matchF_kv_kv]
    exact clause_kht (cl := mKv) (σ := enumFrom 0 [embS S, emb q, emb k, emb v, embB B, emb p])
      lookup_match (fnMatch_mem_kme 8 rfl)
      (ws_enum (.cons (embS_sorted_c₀ S) (.cons (emb_sorted_c₀ q) (.cons (emb_sorted_c₀ k) (.cons (emb_sorted_c₀ v)
        (.cons (embB_sorted_c₀ B) (.cons (emb_sorted_c₀ p) .nil)))))))
      (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_426 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406)
          .nil)) ctor_407) .nil)) ctor_407)
        (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406)
          .nil)) ctor_407) .nil)) ctor_407)
        (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih [k, v] B) notCtor_489 notHook_489 notParam_489)
  · have e : matchF S (.kv p q) u B = some [] := by
      cases u with
      | kv k v => exact absurd ⟨k, v, rfl⟩ hu
      | _ => unfold matchF; rfl
    rw [e]
    apply match_fail_kme
    kme_heads
    exact mKv_fails_kme fun k v h => hu ⟨k, v, h⟩

/-- `m-el`, else `m-fail`. -/
theorem matchAt_el_kme {p : T} (ih : MatchAtKme S p) : MatchAtKme S (.el p) := by
  intro u B
  by_cases hu : ∃ x, u = .el x
  · obtain ⟨x, rfl⟩ := hu
    rw [matchF_el_el]
    exact clause_kht (cl := mEl) (σ := enumFrom 0 [embS S, emb p, emb x, embB B])
      lookup_match (fnMatch_mem_kme 4 rfl)
      (ws_enum (.cons (embS_sorted_c₀ S) (.cons (emb_sorted_c₀ p) (.cons (emb_sorted_c₀ x) (.cons (embB_sorted_c₀ B)
        .nil)))))
      (.cons (.ctor ctor_419 (.cons (.var rfl) .nil)) (.cons (.ctor ctor_419 (.cons (.var rfl) .nil))
        (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih x B)
        notCtor_486 notHook_486 notParam_486)
  · have e : matchF S (.el p) u B = some [] := by
      cases u with
      | el x => exact absurd ⟨x, rfl⟩ hu
      | _ => unfold matchF; rfl
    rw [e]
    apply match_fail_kme
    kme_heads
    exact mEl_fails_kme fun x h => hu ⟨x, h⟩

/-- `m-col` at `matchCol`'s value, else `m-fail`. -/
theorem matchAt_cb_kme (k : Kind) (c : Int) (ps : List T)
    (hcol : ∀ es B, Eval c₀ 487 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S]
      ((matchColF S k c ps es B).map embMs)) : MatchAtKme S (.cb k c ps) := by
  intro u B
  by_cases hu : ∃ l e es, u = .co l e es
  · obtain ⟨l, e, es, rfl⟩ := hu
    rw [matchF_cb_co]
    exact clause_kht (cl := mCol)
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embK l, embS S, embB B, .dv 3 (.int e), embTs es])
      lookup_match (fnMatch_mem_kme 3 rfl)
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) (.cons (embK_sorted_c₀ l)
        (.cons (embS_sorted_c₀ S) (.cons (embB_sorted_c₀ B) (.cons (sort_int e) (.cons (embTs_sorted_c₀ es) .nil)))))))))
      (.cons (.ctor ctor_414 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
        (.cons (.ctor ctor_416 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
          (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
        (.cons (ev_var rfl) .nil)))))) (hcol es B) notCtor_487 notHook_487 notParam_487)
  · have e : matchF S (.cb k c ps) u B = some [] := by
      cases u with
      | co l e es => exact absurd ⟨l, e, es, rfl⟩ hu
      | _ => unfold matchF; rfl
    rw [e]
    apply match_fail_kme
    kme_heads
    exact mCol_fails_kme fun l e es h => hu ⟨l, e, es, h⟩

/-- `m-fail` at an operation. -/
theorem matchAt_hk_kme (o : Int) (as : List T) : MatchAtKme S (.hk o as) := by
  intro t B
  rw [matchF_hk]
  apply match_fail_kme
  kme_heads

/-- `m-fail` at `bot`. -/
theorem matchAt_bot_kme : MatchAtKme S .bot := by
  intro t B
  rw [matchF_bot]
  apply match_fail_kme
  kme_heads

/-- `m-fail` at a collection value. -/
theorem matchAt_co_kme (k : Kind) (c : Int) (es : List T) : MatchAtKme S (.co k c es) := by
  intro t B
  rw [matchF_co]
  apply match_fail_kme
  kme_heads

/-- `m-fail` at a right side with its ensures. -/
theorem matchAt_en_kme (u e : T) : MatchAtKme S (.en u e) := by
  intro t B
  rw [matchF_en]
  apply match_fail_kme
  kme_heads

/-! ### `matchTs` and `matchK` -/

/-- `matchK` under each substitution of a list, from `matchTs` at the same patterns. -/
theorem matchK_eval_kme {ps : List T} (ih : MatchTsAtKme S ps) : ∀ (ms : Ms) (ts : List T),
    Eval c₀ 488 [embMs ms, embTs ps, embTs ts, embS S] ((matchKF S ms ps ts).map embMs)
  | [], ts => by
    rw [matchKF_nil]
    exact clause_kht (cl := mkFail) (σ := enumFrom 0 [embMs [], embTs ps, embTs ts, embS S]) matchKDef_lookup
      (List.mem_cons_self ..)
      (ws_enum (.cons (embMs_sorted_c₀ []) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ ts)
        (.cons (embS_sorted_c₀ S) .nil)))))
      (.cons (.as (.ctor ctor_403 .nil) rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | B :: ms, ts => by
    have h1 := ev_call (σ := enumFrom 0 [embB B, embMs ms, embTs ps, embTs ts, embS S]) (f := 489)
      (ts := [.var 2, .var 3, .var 0, .var 4])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ih ts B)
      notCtor_489 notHook_489 notParam_489
    have h2 := ev_call (σ := enumFrom 0 [embB B, embMs ms, embTs ps, embTs ts, embS S]) (f := 488)
      (ts := [.var 1, .var 2, .var 3, .var 4])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))
      (matchK_eval_kme ih ms ts) notCtor_488 notHook_488 notParam_488
    rw [matchKF_cons]
    refine clause_kht (cl := mkOk) (σ := enumFrom 0 [embB B, embMs ms, embTs ps, embTs ts, embS S])
      matchKDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (embMs_sorted_c₀ ms) (.cons (embTs_sorted_c₀ ps)
        (.cons (embTs_sorted_c₀ ts) (.cons (embS_sorted_c₀ S) .nil))))))
      (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    generalize matchTsF S ps ts B = o₁ at h1 ⊢
    generalize matchKF S ms ps ts = o₂ at h2 ⊢
    cases o₁ <;> cases o₂
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact ev_call (.cons h1 (.cons h2 .nil)) (catF_eval_c₀ _ _) notCtor_453 notHook_453 notParam_453

/-- `ms-nil`; at a non-empty subject list no equation, so no value. -/
theorem matchTsAt_nil_kme : MatchTsAtKme S [] := by
  intro ts B
  cases ts with
  | nil =>
    rw [matchTsF_nil]
    exact clause_kht (cl := msNil) (σ := enumFrom 0 [embB B, embS S]) matchTsDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))
      (.cons (.ctor ctor_406 .nil) (.cons (.ctor ctor_406 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  | cons t ts =>
    rw [matchTsF_nil_cons]
    refine Eval.rest matchTsDef_lookup fun cl hm => ?_
    simp only [matchTsDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact failsCtor2_kme rfl (by decide)
    · exact failsCtor_kme rfl (by decide)

/-- `ms-cons`; at an empty subject list no equation, so no value. -/
theorem matchTsAt_cons_kme {p : T} {ps : List T} (ihp : MatchAtKme S p) (ihs : MatchTsAtKme S ps) :
    MatchTsAtKme S (p :: ps) := by
  intro us B
  cases us with
  | nil =>
    rw [matchTsF_cons_nil]
    refine Eval.rest matchTsDef_lookup fun cl hm => ?_
    simp only [matchTsDef, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact failsCtor_kme rfl (by decide)
    · exact failsCtor2_kme rfl (by decide)
  | cons t ts =>
    have hin := ev_call (σ := enumFrom 0 [emb p, embTs ps, emb t, embTs ts, embB B, embS S]) (f := 486)
      (ts := [.var 0, .var 2, .var 4, .var 5])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ihp t B)
      notCtor_486 notHook_486 notParam_486
    rw [matchTsF_cons]
    refine clause_kht (cl := msCons) (σ := enumFrom 0 [emb p, embTs ps, emb t, embTs ts, embB B, embS S])
      matchTsDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps) (.cons (emb_sorted_c₀ t)
        (.cons (embTs_sorted_c₀ ts) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))))))
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    generalize matchF S p t B = o at hin ⊢
    cases o with
    | none =>
      exact .callUndef notCtor_488 notHook_488
        (.cons hin (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) rfl notParam_488
    | some ms =>
      exact ev_call (.cons hin (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))
        (matchK_eval_kme S ihs ms ts) notCtor_488 notHook_488 notParam_488

/-- `matchTs` at a list each of whose patterns `match` evaluates. -/
theorem matchTsAt_of_kme : ∀ ps : List T, (∀ p ∈ ps, MatchAtKme S p) → MatchTsAtKme S ps
  | [], _ => matchTsAt_nil_kme S
  | p :: ps, h =>
    matchTsAt_cons_kme S (h p (List.mem_cons_self ..))
      (matchTsAt_of_kme ps fun q hq => h q (List.mem_cons_of_mem _ hq))

end Steps

/-! ## Patterns without a collection pattern -/

theorem noCbL_mem_kme : ∀ {ts : List T}, noCbL ts = true → ∀ t ∈ ts, noCb t = true
  | [], _, _, h => nomatch h
  | u :: us, h, t, ht => by
    rw [noCbL, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h.1
    · exact noCbL_mem_kme h.2 t ht

/-- `match` evaluates to `matchF` at every pattern without a collection pattern. -/
theorem matchAt_noCb_kme (S : List (Int × Int)) (p : T) : noCb p = true → MatchAtKme S p := by
  induction p using tInd_kkc with
  | hap f as ih =>
    intro h
    rw [noCb] at h
    exact matchAt_ap_kme S f (matchTsAt_of_kme S as fun a ha => ih a ha (noCbL_mem_kme h a ha))
  | hiv i => intro _; exact matchAt_iv_kme S i
  | hbv b => intro _; exact matchAt_bv_kme S b
  | htk s x => intro _; exact matchAt_tk_kme S s x
  | hij a b t ih => intro h; rw [noCb] at h; exact matchAt_ij_kme S a b (ih h)
  | hvr i => intro _; exact matchAt_vr_kme S i
  | has p i ih => intro h; rw [noCb] at h; exact matchAt_as_kme S i (ih h)
  | hhk o as _ => intro _; exact matchAt_hk_kme S o as
  | hbot => intro _; exact matchAt_bot_kme S
  | hcb k c ps _ => intro h; rw [noCb] at h; cases h
  | hco k c es _ => intro _; exact matchAt_co_kme S k c es
  | hen t e _ _ => intro _; exact matchAt_en_kme S t e
  | hkv a v iha ihv =>
    intro h
    rw [noCb, Bool.and_eq_true] at h
    refine matchAt_kv_kme S (matchTsAt_of_kme S [a, v] fun q hq => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact iha h.1
    · exact ihv h.2
  | hel x ih => intro h; rw [noCb] at h; exact matchAt_el_kme S (ih h)

/-! ## At `K₀ sig` -/

/-- **`match` on embedded mirrors is `matchF`**: at a pattern without a collection pattern, every
subject, substitution and subsort table. -/
theorem match_eval (S : List (Int × Int)) {p : T} (hp : noCb p = true) (a : T) (B : Bind) :
    Eval (K₀ sig) 486 [emb p, emb a, embB B, embS S] ((matchF S p a B).map embMs) :=
  matchAt_noCb_kme S p hp a B

theorem match_eval_iff (S : List (Int × Int)) {p : T} (hp : noCb p = true) (a : T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 486 [emb p, emb a, embB B, embS S] r ↔ r = (matchF S p a B).map embMs :=
  evalF_iff (match_eval S hp a B)

/-- `matchTs` on embedded mirrors is `matchTsF`, at patterns without a collection pattern. -/
theorem matchTs_eval (S : List (Int × Int)) {ps : List T} (hps : noCbL ps = true) (ts : List T) (B : Bind) :
    Eval (K₀ sig) 489 [embTs ps, embTs ts, embB B, embS S] ((matchTsF S ps ts B).map embMs) :=
  matchTsAt_of_kme S ps (fun p hp => matchAt_noCb_kme S p (noCbL_mem_kme hps p hp)) ts B

theorem matchTs_eval_iff (S : List (Int × Int)) {ps : List T} (hps : noCbL ps = true) (ts : List T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 489 [embTs ps, embTs ts, embB B, embS S] r ↔ r = (matchTsF S ps ts B).map embMs :=
  evalF_iff (matchTs_eval S hps ts B)

/-- `matchK` on embedded mirrors is `matchKF`, at patterns without a collection pattern. -/
theorem matchK_eval (S : List (Int × Int)) {ps : List T} (hps : noCbL ps = true) (ms : Ms) (ts : List T) :
    Eval (K₀ sig) 488 [embMs ms, embTs ps, embTs ts, embS S] ((matchKF S ms ps ts).map embMs) :=
  matchK_eval_kme S (matchTsAt_of_kme S ps fun p hp => matchAt_noCb_kme S p (noCbL_mem_kme hps p hp)) ms ts

theorem matchK_eval_iff (S : List (Int × Int)) {ps : List T} (hps : noCbL ps = true) (ms : Ms) (ts : List T)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 488 [embMs ms, embTs ps, embTs ts, embS S] r ↔ r = (matchKF S ms ps ts).map embMs :=
  evalF_iff (matchK_eval S hps ms ts)

/-! ## Checks -/

#check @match_eval
#check @match_eval_iff
#check @matchTs_eval
#check @matchTs_eval_iff
#check @matchK_eval
#check @matchK_eval_iff
#check @matchAt_cb_kme
#check @matchAt_noCb_kme

open Lean in
#eval show CoreM Unit from do
  for n in [``matchEval_names_kme, ``match_eval, ``match_eval_iff, ``matchTs_eval, ``matchTs_eval_iff,
      ``matchK_eval, ``matchK_eval_iff, ``matchAt_cb_kme] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
