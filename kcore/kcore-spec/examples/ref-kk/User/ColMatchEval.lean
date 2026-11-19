/-
  kore.k's `matchCol`, `choose`, `split`, `splitOn` and `rest` on embedded mirrors: their value at
  `K₀ sig` is the mirror's (`matchColF`, `chooseF`, `splitF`, `splitOnF`, `restF`, KKMatchF.lean),
  and with them `match`, `matchTs` and `matchK` evaluate to `matchF`, `matchTsF` and `matchKF` at
  every pattern, a collection pattern included, with no hypothesis on the subsort table.

  The proof follows the pattern. `matchCol` at a list of parts is proved by induction on that list
  (`colAt_kcm2`), given `match` at each part: at the parts after the first, `rest` evaluates by
  induction on its list of substitutions (`rest_eval_kcm2`); `choose` and `split` evaluate by
  induction on the elements still to try (`choose_eval_kcm2`, `split_eval_kcm2`), `splitOn` through
  `split` at a shorter list. At the first part, the equation of `matchCol` that applies is the one
  `matchColF` takes: `mc-done` at no part and no element, `mc-choose` at an element part of a Map or
  a Set, `mc-head` at a List's element part and a first element, `mc-frame` at a last part that is
  no element, `mc-split` at a List's part that is no element with parts after it. Everywhere else
  (`matchColF` gives no substitution) each equation of priority 50 fails, on a pattern of another
  head or on its `requires` (`isElem`, `K =/=K list`), and `mc-fail` (`[owise]`) applies. `match`
  at every pattern then follows by induction on the pattern, MatchEval.lean's step at a collection
  pattern taking `matchCol`'s evaluation (`matchAt_kcm2`).
-/
import User.MatchEval
import User.HelpColl

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

/-- Symbols 454, 501, 504 and 505 are kore.k's `choose`, `rest`, `split` and `splitOn`. -/
theorem colMatchEval_names_kcm2 :
    RefKk.defn.sem.symName 454 =
      "Lblchoose'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Kind'Unds'Int'Unds'Term'Unds'Ts'Unds'Ts'Unds'Ts'Unds'Bind'Unds'Subs" ∧
    RefKk.defn.sem.symName 501 =
      "Lblrest'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Kind'Unds'Int'Unds'Ts'Unds'Ts'Unds'Ms'Unds'Subs" ∧
    RefKk.defn.sem.symName 504 =
      "Lblsplit'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Int'Unds'Term'Unds'Ts'Unds'Ts'Unds'Ts'Unds'Bind'Unds'Subs" ∧
    RefKk.defn.sem.symName 505 =
      "LblsplitOn'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Int'Unds'Term'Unds'Ts'Unds'Ts'Unds'Ts'Unds'Bind'Unds'Subs" := by
  decide +kernel

/-! ## The clauses of `choose`, `rest`, `split` and `splitOn`, as the semantics holds them

`matchCol`'s are User.Coherent's `fnMatchCol`. -/

namespace ColClauses
open _root_.KK Terms

/-- `ch-nil`. -/
def chNil : Clause :=
  plainCl [34, 3, 33, 43, 43, 46, 32] [.var 0, .var 1, .var 2, .var 3, .var 4, .app 406 [], .var 5, .var 6]
    (.app 403 [])

/-- `ch-cons`. -/
def chCons : Clause :=
  plainCl [34, 3, 33, 43, 43, 33, 43, 46, 32]
    [.var 0, .var 1, .var 2, .var 3, .var 4, .app 407 [.var 5, .var 6], .var 7, .var 8]
    (.app 453 [.app 501 [.var 0, .var 1, .var 3, .app 447 [.var 4, .var 6], .app 486 [.var 2, .var 5, .var 7, .var 8],
        .var 8],
      .app 454 [.var 0, .var 1, .var 2, .var 3, .app 447 [.var 4, .app 407 [.var 5, .app 406 []]], .var 6, .var 7,
        .var 8]])

/-- `choose` (454). -/
def chooseDef : Fn :=
  { label := 454, args := [34, 3, 33, 43, 43, 43, 46, 32], result := 37, total := false,
    clauses := [chCons, chNil] }

/-- `rest-cons`. -/
def restCons : Clause :=
  plainCl [34, 3, 43, 43, 46, 37, 32] [.var 0, .var 1, .var 2, .var 3, .app 428 [.var 4, .var 5], .var 6]
    (.app 453 [.app 487 [.var 0, .var 1, .var 2, .var 3, .var 4, .var 6],
      .app 501 [.var 0, .var 1, .var 2, .var 3, .var 5, .var 6]])

/-- `rest-nil`. -/
def restNil : Clause :=
  plainCl [34, 3, 43, 43, 37, 32] [.var 0, .var 1, .var 2, .var 3, .as (.app 403 []) 4, .var 5] (.var 4)

/-- `rest` (501). -/
def restDef : Fn :=
  { label := 501, args := [34, 3, 43, 43, 37, 32], result := 37, total := false, clauses := [restCons, restNil] }

/-- `sp-here`. -/
def spHere : Clause :=
  plainCl [3, 33, 43, 43, 43, 46, 32] [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6]
    (.app 453 [.app 501 [.app 427 [], .var 0, .var 2, .var 4,
        .app 486 [.var 1, .app 416 [.app 427 [], .var 0, .var 3], .var 5, .var 6], .var 6],
      .app 505 [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6]])

/-- `split` (504). -/
def splitDef : Fn :=
  { label := 504, args := [3, 33, 43, 43, 43, 46, 32], result := 37, total := false, clauses := [spHere] }

/-- `sp-end`. -/
def spEnd : Clause :=
  plainCl [3, 33, 43, 43, 46, 32] [.var 0, .var 1, .var 2, .var 3, .app 406 [], .var 4, .var 5] (.app 403 [])

/-- `sp-next`. -/
def spNext : Clause :=
  plainCl [3, 33, 43, 43, 33, 43, 46, 32] [.var 0, .var 1, .var 2, .var 3, .app 407 [.var 4, .var 5], .var 6, .var 7]
    (.app 504 [.var 0, .var 1, .var 2, .app 447 [.var 3, .app 407 [.var 4, .app 406 []]], .var 5, .var 6, .var 7])

/-- `splitOn` (505). -/
def splitOnDef : Fn :=
  { label := 505, args := [3, 33, 43, 43, 43, 46, 32], result := 37, total := false, clauses := [spNext, spEnd] }

theorem chooseDef_lookup : c₀.lookupFn 454 = some chooseDef := by kernel_rfl
theorem restDef_lookup : c₀.lookupFn 501 = some restDef := by kernel_rfl
theorem splitDef_lookup : c₀.lookupFn 504 = some splitDef := by kernel_rfl
theorem splitOnDef_lookup : c₀.lookupFn 505 = some splitOnDef := by kernel_rfl

end ColClauses

/-! ## Failing clauses -/

section Kit
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts

/-- Patterns that denote values denote them position by position. -/
theorem pvs_at_kcm2 {σ : Subst} : ∀ {ps : List Term} {vs : List GroundTerm}, PatVals c₀ σ ps vs →
    ∀ {n : Nat} {p : Term} {v : GroundTerm}, ps[n]? = some p → vs[n]? = some v → PatVal c₀ σ p v
  | _, _, .nil, _, _, _, hp, _ => nomatch hp
  | _, _, .cons h _, 0, _, _, hp, hv => by cases hp; cases hv; exact h
  | _, _, .cons _ hs, n + 1, _, _, hp, hv => pvs_at_kcm2 hs hp hv

/-- A clause whose pattern at position `n` is a constructor other than the head of the argument there
fails. -/
theorem failsAt_kcm2 {cl : Clause} {vs : List GroundTerm} (n : Nat) {g h : Sym} {qs : List Term}
    {us : List GroundTerm} (hp : cl.pats[n]? = some (.app g qs)) (hv : vs[n]? = some (.ctor h us))
    (hgh : g ≠ h) (hc : c₀.isCtor g = true := by decide +kernel)
    (hk : patternHooks.contains g = false := by decide +kernel) : Fails c₀ vs cl :=
  .intro fun _ _ hm => by
    obtain ⟨_, he, -⟩ := pv_ctor (pvs_at_kcm2 hm hp hv) hc hk
    exact (hgh (GroundTerm.ctor.inj he).1.symm).elim

/-- A pattern variable at position `n` holds the argument there. -/
theorem varAt_kcm2 {σ : Subst} {ps : List Term} {vs : List GroundTerm} (hm : PatVals c₀ σ ps vs) {n i : Nat}
    {v : GroundTerm} (hp : ps[n]? = some (.var i)) (hv : vs[n]? = some v) : σ.lookup i = some v :=
  PatVal.var_inv (pvs_at_kcm2 hm hp hv)

/-- A pattern `cons(V i, _)` at position `n` holds in `V i` the first of the list there. -/
theorem headAt_kcm2 {σ : Subst} {ps : List Term} {vs : List GroundTerm} (hm : PatVals c₀ σ ps vs) {n i : Nat}
    {q : Term} {t : T} {ts : List T} (hp : ps[n]? = some (.app 407 [.var i, q]))
    (hv : vs[n]? = some (embTs (t :: ts))) : σ.lookup i = some (emb t) := by
  obtain ⟨ws, he, hws⟩ := pv_ctor (pvs_at_kcm2 hm hp hv)
  cases he
  rcases hws with _ | ⟨h0, -⟩
  exact PatVal.var_inv h0

theorem ne_true_kcm2 {b : Bool} (h : b = false) : some (bool b) ≠ some (bool true) := by
  subst h; exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)

theorem embK_ne_list_kcm2 {k : Kind} (hk : k ≠ .list) : ∃ h us, embK k = .ctor h us ∧ (427 : Sym) ≠ h := by
  cases k with
  | map => exact ⟨429, [], rfl, by decide⟩
  | set => exact ⟨438, [], rfl, by decide⟩
  | list => exact absurd rfl hk

theorem fnMatchCol_mem_kcm2 {cl : Clause} (n : Nat) (h : fnMatchCol.clauses[n]? = some cl) :
    cl ∈ fnMatchCol.clauses :=
  List.mem_of_getElem? h

/-- Where every equation of `matchCol` of priority 50 fails, `mc-fail` gives no substitution. -/
theorem matchCol_fail_kcm2 {k : Kind} {c : Int} {ps es : List T} {B : Bind} {S : List (Int × Int)}
    (h : ∀ cl ∈ fnMatchCol.clauses, cl.prio < 200 →
      Fails c₀ [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S] cl) :
    Eval c₀ 487 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S] (some (embMs [])) :=
  .clause (cl := mcFail) (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S])
    lookup_matchCol (fnMatchCol_mem_kcm2 5 rfl)
    (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ es)
      (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))
    (fun _ h => by cases h) .top (fun cl hm _ hlt => h cl hm hlt) rfl (ev_ctor .nil ctor_403)
    (fun _ h => by cases h) .top

end Kit

set_option hygiene false in
/-- The equations of `matchCol` other than `mc-fail`, introduced and named by their rule; each is
left as a goal, in the order of the semantics' clause list (`mc-head`, `mc-frame`, `mc-choose`,
`mc-done`, `mc-split`). -/
macro "kcm2_heads" : tactic => `(tactic| (
  intro cl hm hlt
  simp only [_root_.KK.fnMatchCol, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hlt (by decide)
    | skip))

/-! ## `rest`, `choose`, `split`, `splitOn` and `matchCol` -/

/-- `matchCol` at the parts `ps`, against every list of elements and substitution, evaluates to
`matchColF`'s substitutions. -/
def ColAtKcm2 (S : List (Int × Int)) (k : Kind) (c : Int) (ps : List T) : Prop :=
  ∀ es B, Eval _root_.KK.c₀ 487 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S]
    ((matchColF S k c ps es B).map embMs)

section Steps
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms ColClauses Coll

variable (S : List (Int × Int))

/-- `rest-nil`, `rest-cons`: `matchCol` under each substitution of the list, concatenated. -/
theorem rest_eval_kcm2 {k : Kind} {c : Int} {ps : List T} (ih : ColAtKcm2 S k c ps) (es : List T) :
    ∀ ms : Ms, Eval c₀ 501 [embK k, .dv 3 (.int c), embTs ps, embTs es, embMs ms, embS S]
      ((restF S k c ps es ms).map embMs)
  | [] => by
    rw [restF_nil]
    exact clause_kht (cl := restNil) (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embTs es, embMs [], embS S])
      restDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ es)
        (.cons (embMs_sorted_c₀ []) (.cons (embS_sorted_c₀ S) .nil)))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.as (.ctor ctor_403 .nil) rfl)
        (.cons (.var rfl) .nil))))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_var rfl)
  | B :: ms => by
    have h1 := ev_call (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embMs ms, embS S])
      (f := 487) (ts := [.var 0, .var 1, .var 2, .var 3, .var 4, .var 6])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
        (.cons (ev_var rfl) .nil)))))) (ih es B) notCtor_487 notHook_487 notParam_487
    have h2 := ev_call (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embMs ms, embS S])
      (f := 501) (ts := [.var 0, .var 1, .var 2, .var 3, .var 5, .var 6])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
        (.cons (ev_var rfl) .nil)))))) (rest_eval_kcm2 ih es ms) notCtor_501 notHook_501 notParam_501
    rw [restF_cons]
    refine clause_kht (cl := restCons)
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embMs ms, embS S])
      restDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ es)
        (.cons (embB_sorted_c₀ B) (.cons (embMs_sorted_c₀ ms) (.cons (embS_sorted_c₀ S) .nil))))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    generalize matchColF S k c ps es B = o₁ at h1 ⊢
    generalize restF S k c ps es ms = o₂ at h2 ⊢
    cases o₁ <;> cases o₂
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact ev_call (.cons h1 (.cons h2 .nil)) (catF_eval_c₀ _ _) notCtor_453 notHook_453 notParam_453

/-- `ch-nil`, `ch-cons`: the element part against each element still to try, the other parts
against the rest. -/
theorem choose_eval_kcm2 {k : Kind} {c : Int} {p : T} {ps : List T} (ihp : MatchAtKme S p)
    (ih : ColAtKcm2 S k c ps) : ∀ (post pre : List T) (B : Bind),
    Eval c₀ 454 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((chooseF S k c p ps pre post B).map embMs)
  | [], pre, B => by
    rw [chooseF_nil]
    exact clause_kht (cl := chNil)
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, embB B, embS S])
      chooseDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps)
        (.cons (embTs_sorted_c₀ pre) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil))))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_406 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil))))))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_403)
  | e :: post, pre, B => by
    have hm := ev_call
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
      (f := 486) (ts := [.var 2, .var 5, .var 7, .var 8])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ihp e B)
      notCtor_486 notHook_486 notParam_486
    have happ := ev_call
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
      (f := 447) (ts := [.var 4, .var 6]) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)) (app_eval_khc pre post)
      notCtor_447 notHook_447 notParam_447
    have happ' := ev_call
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
      (f := 447) (ts := [.var 4, .app 407 [.var 5, .app 406 []]])
      (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406) .nil)) ctor_407) .nil))
      (app_eval_khc pre [e]) notCtor_447 notHook_447 notParam_447
    have h2 := ev_call
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
      (f := 454) (ts := [.var 0, .var 1, .var 2, .var 3, .app 447 [.var 4, .app 407 [.var 5, .app 406 []]], .var 6,
        .var 7, .var 8])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons happ'
        (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))))))
      (choose_eval_kcm2 ihp ih post (pre ++ [e]) B) notCtor_454 notHook_454 notParam_454
    rw [chooseF_cons]
    refine clause_kht (cl := chCons)
      (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
      chooseDef_lookup (List.mem_cons_self ..)
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps)
        (.cons (embTs_sorted_c₀ pre) (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ post) (.cons (embB_sorted_c₀ B)
          (.cons (embS_sorted_c₀ S) .nil))))))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    generalize chooseF S k c p ps (pre ++ [e]) post B = o₂ at h2 ⊢
    generalize matchF S p e B = o at hm ⊢
    cases o with
    | none =>
      have h1 := EvalTerm.callUndef (c := c₀)
        (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
        (f := 501) (ts := [.var 0, .var 1, .var 3, .app 447 [.var 4, .var 6], .app 486 [.var 2, .var 5, .var 7, .var 8],
          .var 8]) notCtor_501 notHook_501
        (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons happ (.cons hm (.cons (ev_var rfl) .nil))))))
        rfl notParam_501
      cases o₂
      · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
      · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    | some ms =>
      dsimp only
      have h1 := ev_call
        (σ := enumFrom 0 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
        (f := 501) (ts := [.var 0, .var 1, .var 3, .app 447 [.var 4, .var 6], .app 486 [.var 2, .var 5, .var 7, .var 8],
          .var 8])
        (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons happ (.cons hm (.cons (ev_var rfl) .nil))))))
        (rest_eval_kcm2 S ih (pre ++ post) ms) notCtor_501 notHook_501 notParam_501
      generalize restF S k c ps (pre ++ post) ms = o₁ at h1 ⊢
      cases o₁ <;> cases o₂
      · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
      · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
      · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
      · exact ev_call (.cons h1 (.cons h2 .nil)) (catF_eval_c₀ _ _) notCtor_453 notHook_453 notParam_453

/-- `sp-end`: no longer prefix. -/
theorem splitOn_nil_eval_kcm2 (c : Int) (f : T) (ps pre : List T) (B : Bind) :
    Eval c₀ 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs [], embB B, embS S]
      ((splitOnF S c f ps pre [] B).map embMs) := by
  rw [splitOnF_nil]
  exact clause_kht (cl := spEnd) (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embB B, embS S])
    splitOnDef_lookup (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (ws_enum (.cons (sort_int c) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ pre)
      (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil)))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
      (.cons (.ctor ctor_406 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil)))))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil ctor_403)

/-- `sp-next`: `split` with the first element moved to the end of the prefix. -/
theorem splitOn_cons_eval_kcm2 {c : Int} {f : T} {ps pre : List T} {e : T} {post : List T} {B : Bind}
    {r : Option GroundTerm} (h : Eval c₀ 504 [.dv 3 (.int c), emb f, embTs ps, embTs (pre ++ [e]), embTs post,
      embB B, embS S] r) :
    Eval c₀ 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs (e :: post), embB B, embS S] r := by
  have happ := ev_call
    (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
    (f := 447) (ts := [.var 3, .app 407 [.var 4, .app 406 []]])
    (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406) .nil)) ctor_407) .nil))
    (app_eval_khc pre [e]) notCtor_447 notHook_447 notParam_447
  exact clause_kht (cl := spNext)
    (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, emb e, embTs post, embB B, embS S])
    splitOnDef_lookup (List.mem_cons_self ..)
    (ws_enum (.cons (sort_int c) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ pre)
      (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ post) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S)
        .nil)))))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
      (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil)))))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons happ (.cons (ev_var rfl)
      (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))))) h notCtor_504 notHook_504 notParam_504)

/-- `sp-here`: the frame against the prefix and the other parts against the rest, then `splitOn`. -/
theorem split_step_kcm2 {c : Int} {f : T} {ps : List T} (ihf : MatchAtKme S f) (ih : ColAtKcm2 S .list c ps)
    (post pre : List T) (B : Bind)
    (hon : Eval c₀ 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitOnF S c f ps pre post B).map embMs)) :
    Eval c₀ 504 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitF S c f ps pre post B).map embMs) := by
  have hm := ev_call (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S])
    (f := 486) (ts := [.var 1, .app 416 [.app 427 [], .var 0, .var 3], .var 5, .var 6])
    (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_ctor .nil ctor_427) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))
      ctor_416) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ihf (.co .list c pre) B)
    notCtor_486 notHook_486 notParam_486
  have h2 := ev_call (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S])
    (f := 505) (ts := [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6])
    (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
      (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))))) hon notCtor_505 notHook_505 notParam_505
  rw [splitF_eq]
  refine clause_kht (cl := spHere)
    (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S])
    splitDef_lookup (List.mem_cons_self ..)
    (ws_enum (.cons (sort_int c) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ pre)
      (.cons (embTs_sorted_c₀ post) (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) .nil))))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
      (.cons (.var rfl) (.cons (.var rfl) .nil)))))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
  generalize splitOnF S c f ps pre post B = o₂ at h2 ⊢
  generalize matchF S f (.co .list c pre) B = o at hm ⊢
  cases o with
  | none =>
    have h1 := EvalTerm.callUndef (c := c₀)
      (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S])
      (f := 501) (ts := [.app 427 [], .var 0, .var 2, .var 4,
        .app 486 [.var 1, .app 416 [.app 427 [], .var 0, .var 3], .var 5, .var 6], .var 6]) notCtor_501 notHook_501
      (.cons (ev_ctor .nil ctor_427) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons hm
        (.cons (ev_var rfl) .nil)))))) rfl notParam_501
    cases o₂
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
  | some ms =>
    dsimp only
    have h1 := ev_call (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S])
      (f := 501) (ts := [.app 427 [], .var 0, .var 2, .var 4,
        .app 486 [.var 1, .app 416 [.app 427 [], .var 0, .var 3], .var 5, .var 6], .var 6])
      (.cons (ev_ctor .nil ctor_427) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl)
        (.cons hm (.cons (ev_var rfl) .nil)))))) (rest_eval_kcm2 S ih post ms) notCtor_501 notHook_501 notParam_501
    generalize restF S .list c ps post ms = o₁ at h1 ⊢
    cases o₁ <;> cases o₂
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact .callUndef notCtor_453 notHook_453 (.cons h1 (.cons h2 .nil)) rfl notParam_453
    · exact ev_call (.cons h1 (.cons h2 .nil)) (catF_eval_c₀ _ _) notCtor_453 notHook_453 notParam_453

/-- `split` at every list, by induction on the elements after the prefix. -/
theorem split_eval_kcm2 {c : Int} {f : T} {ps : List T} (ihf : MatchAtKme S f) (ih : ColAtKcm2 S .list c ps) :
    ∀ (post pre : List T) (B : Bind),
    Eval c₀ 504 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitF S c f ps pre post B).map embMs)
  | [], pre, B => split_step_kcm2 S ihf ih [] pre B (splitOn_nil_eval_kcm2 S c f ps pre B)
  | e :: post, pre, B => by
    refine split_step_kcm2 S ihf ih (e :: post) pre B ?_
    rw [splitOnF_cons]
    exact splitOn_cons_eval_kcm2 S (split_eval_kcm2 ihf ih post (pre ++ [e]) B)

/-- `splitOn` at every list, from `split`. -/
theorem splitOn_eval_kcm2 {c : Int} {f : T} {ps : List T} (ihf : MatchAtKme S f) (ih : ColAtKcm2 S .list c ps) :
    ∀ (pre post : List T) (B : Bind),
    Eval c₀ 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitOnF S c f ps pre post B).map embMs)
  | pre, [], B => splitOn_nil_eval_kcm2 S c f ps pre B
  | pre, e :: post, B => by
    rw [splitOnF_cons]
    exact splitOn_cons_eval_kcm2 S (split_eval_kcm2 S ihf ih post (pre ++ [e]) B)

/-- `matchCol` at no part: `mc-done` at no element, else `mc-fail`. -/
theorem colAt_nil_kcm2 (k : Kind) (c : Int) : ColAtKcm2 S k c [] := by
  intro es B
  rw [matchColF_nil]
  cases es with
  | nil =>
    rw [ite_pos (rfl : ([] : List T) = [])]
    exact clause_kht (cl := mcDone) (σ := enumFrom 0 [embK k, .dv 3 (.int c), embS S, embB B]) lookup_matchCol
      (fnMatchCol_mem_kcm2 3 rfl)
      (ws_enum (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (embS_sorted_c₀ S) (.cons (embB_sorted_c₀ B) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) (.cons (.ctor ctor_406 .nil)
        (.cons (.var rfl) (.cons (.var rfl) .nil))))))
      (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩
      (ev_ctor (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_403) .nil)) ctor_428)
  | cons e es =>
    rw [ite_neg (List.cons_ne_nil e es)]
    apply matchCol_fail_kcm2
    kcm2_heads
    · exact failsAt_kcm2 2 rfl rfl (by decide)
    · exact failsAt_kcm2 2 rfl rfl (by decide)
    · exact failsAt_kcm2 2 rfl rfl (by decide)
    · exact failsAt_kcm2 3 rfl rfl (by decide)
    · exact failsAt_kcm2 2 rfl rfl (by decide)

/-- `mc-choose`: an element part of a Map or a Set. -/
theorem colAt_choose_kcm2 {k : Kind} (hk : k ≠ .list) (c : Int) {p : T} {ps : List T} (hp : isElemT p = true)
    (ihp : MatchAtKme S p) (ih : ColAtKcm2 S k c ps) : ColAtKcm2 S k c (p :: ps) := by
  intro es B
  rw [matchColF_choose S hp hk]
  refine clause_kht (cl := mcChoose)
    (σ := enumFrom 0 [embTs ps, embTs es, embB B, embS S, embK k, .dv 3 (.int c), emb p]) lookup_matchCol
    (fnMatchCol_mem_kcm2 2 rfl)
    (ws_enum (.cons (embTs_sorted_c₀ ps) (.cons (embTs_sorted_c₀ es) (.cons (embB_sorted_c₀ B)
      (.cons (embS_sorted_c₀ S) (.cons (embK_sorted_c₀ k) (.cons (sort_int c) (.cons (emb_sorted_c₀ p) .nil))))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))
    (fun t hq => by
      cases hq
      have h := ev_and_khc (ev_isElem_khc (ev_var (σ := enumFrom 0 [embTs ps, embTs es, embB B, embS S, embK k,
        .dv 3 (.int c), emb p]) (i := 6) rfl)) (ev_kindNeT_khc (ev_var (i := 4) rfl))
      rwa [hp, decide_eq_false hk] at h)
    (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406)
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil))))))))
      (choose_eval_kcm2 S ihp ih es [] B) notCtor_454 notHook_454 notParam_454)

/-- `mc-head`: a List's element part against the first element; `mc-fail` at no element. -/
theorem colAt_head_kcm2 (c : Int) {p : T} {ps : List T} (hp : isElemT p = true) (ihp : MatchAtKme S p)
    (ih : ColAtKcm2 S .list c ps) : ColAtKcm2 S .list c (p :: ps) := by
  intro es B
  cases es with
  | cons e es =>
    rw [matchColF_head S hp]
    have hm := ev_call
      (σ := enumFrom 0 [embB B, embS S, emb p, embTs ps, emb e, embTs es, .dv 3 (.int c), embK .list])
      (f := 486) (ts := [.var 2, .var 4, .var 0, .var 1])
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ihp e B)
      notCtor_486 notHook_486 notParam_486
    refine clause_kht (cl := mcHead)
      (σ := enumFrom 0 [embB B, embS S, emb p, embTs ps, emb e, embTs es, .dv 3 (.int c), embK .list])
      lookup_matchCol (fnMatchCol_mem_kcm2 0 rfl)
      (ws_enum (.cons (embB_sorted_c₀ B) (.cons (embS_sorted_c₀ S) (.cons (emb_sorted_c₀ p) (.cons (embTs_sorted_c₀ ps)
        (.cons (emb_sorted_c₀ e) (.cons (embTs_sorted_c₀ es) (.cons (sort_int c) (.cons (embK_sorted_c₀ .list) .nil)))))))))
      (.cons (.as (.ctor ctor_427 .nil) rfl) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) (.cons (.var rfl) .nil))))))
      (fun t hq => by
        cases hq
        have h := ev_isElem_khc (ev_var (σ := enumFrom 0 [embB B, embS S, emb p, embTs ps, emb e, embTs es,
          .dv 3 (.int c), embK .list]) (i := 2) rfl)
        rwa [hp] at h)
      (by decide) ⟨rfl, rfl, rfl, rfl⟩ ?_
    generalize matchF S p e B = o at hm ⊢
    cases o with
    | none =>
      exact .callUndef notCtor_501 notHook_501
        (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons hm (.cons (ev_var rfl) .nil))))))
        rfl notParam_501
    | some ms =>
      exact ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons hm
        (.cons (ev_var rfl) .nil)))))) (rest_eval_kcm2 S ih es ms) notCtor_501 notHook_501 notParam_501
  | nil =>
    rw [matchColF_head_nil S hp]
    apply matchCol_fail_kcm2
    kcm2_heads
    · exact failsAt_kcm2 3 rfl rfl (by decide)
    · refine .intro fun σ _ hm => .intro rfl (ev_not_khc (ev_isElem_khc (ev_var (headAt_kcm2 hm (n := 2) (i := 1) rfl rfl))))
        (ne_true_kcm2 (by simp [hp]))
    · refine .intro fun σ _ hm => .intro rfl (ev_and_khc (ev_isElem_khc (ev_var (headAt_kcm2 hm (n := 2) (i := 6) rfl rfl)))
        (ev_kindNeT_khc (ev_var (varAt_kcm2 hm (n := 0) (i := 4) rfl rfl)))) (ne_true_kcm2 (by simp))
    · exact failsAt_kcm2 2 rfl rfl (by decide)
    · refine .intro fun σ _ hm => .intro rfl (ev_not_khc (ev_isElem_khc (ev_var (headAt_kcm2 hm (n := 2) (i := 1) rfl rfl))))
        (ne_true_kcm2 (by simp [hp]))

/-- `mc-frame`: a last part that is no element takes the elements left. -/
theorem colAt_frame_kcm2 (k : Kind) (c : Int) {f : T} (hf : isElemT f = false) (ihf : MatchAtKme S f) :
    ColAtKcm2 S k c [f] := by
  intro es B
  rw [matchColF_frame S hf]
  exact clause_kht (cl := mcFrame)
    (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs es, embB B, embK k, embS S]) lookup_matchCol
    (fnMatchCol_mem_kcm2 1 rfl)
    (ws_enum (.cons (sort_int c) (.cons (emb_sorted_c₀ f) (.cons (embTs_sorted_c₀ es) (.cons (embB_sorted_c₀ B)
      (.cons (embK_sorted_c₀ k) (.cons (embS_sorted_c₀ S) .nil)))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl) (.cons (.ctor ctor_406 .nil) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))
    (fun t hq => by
      cases hq
      have h := ev_not_khc (ev_isElem_khc (ev_var (σ := enumFrom 0 [.dv 3 (.int c), emb f, embTs es, embB B,
        embK k, embS S]) (i := 1) rfl))
      rwa [hf] at h)
    (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_ctor (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))
      ctor_416) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))) (ihf (.co k c es) B)
      notCtor_486 notHook_486 notParam_486)

/-- `mc-split`: a List's part that is no element, with parts after it, against each prefix. -/
theorem colAt_split_kcm2 (c : Int) {f q : T} {qs : List T} (hf : isElemT f = false) (ihf : MatchAtKme S f)
    (ih : ColAtKcm2 S .list c (q :: qs)) : ColAtKcm2 S .list c (f :: q :: qs) := by
  intro es B
  rw [matchColF_split S hf]
  exact clause_kht (cl := mcSplit)
    (σ := enumFrom 0 [.dv 3 (.int c), emb f, emb q, embB B, embS S, embTs qs, embTs (q :: qs), embTs es])
    lookup_matchCol (fnMatchCol_mem_kcm2 4 rfl)
    (ws_enum (.cons (sort_int c) (.cons (emb_sorted_c₀ f) (.cons (emb_sorted_c₀ q) (.cons (embB_sorted_c₀ B)
      (.cons (embS_sorted_c₀ S) (.cons (embTs_sorted_c₀ qs) (.cons (embTs_sorted_c₀ (q :: qs))
        (.cons (embTs_sorted_c₀ es) .nil)))))))))
    (.cons (.ctor ctor_427 .nil) (.cons (.var rfl) (.cons (.ctor ctor_407 (.cons (.var rfl)
      (.cons (.as (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil)))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))
    (fun t hq => by
      cases hq
      have h := ev_not_khc (ev_isElem_khc (ev_var (σ := enumFrom 0 [.dv 3 (.int c), emb f, emb q, embB B, embS S,
        embTs qs, embTs (q :: qs), embTs es]) (i := 1) rfl))
      rwa [hf] at h)
    (by decide) ⟨rfl, rfl, rfl, rfl⟩
    (ev_call (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_ctor .nil ctor_406)
      (.cons (ev_var rfl) (.cons (ev_var rfl) (.cons (ev_var rfl) .nil)))))))
      (split_eval_kcm2 S ihf ih es [] B) notCtor_504 notHook_504 notParam_504)

/-- `mc-fail` at a Map's or a Set's part that is no element with parts after it. -/
theorem colAt_frameMore_kcm2 {k : Kind} (hk : k ≠ .list) (c : Int) {f q : T} {qs : List T}
    (hf : isElemT f = false) : ColAtKcm2 S k c (f :: q :: qs) := by
  intro es B
  rw [matchColF_frame_more S hf hk]
  apply matchCol_fail_kcm2
  obtain ⟨h, us, hkh, hne⟩ := embK_ne_list_kcm2 hk
  kcm2_heads
  · refine .intro fun σ _ hm => .intro rfl (ev_isElem_khc (ev_var (headAt_kcm2 hm (n := 2) (i := 2) rfl rfl)))
      (ne_true_kcm2 hf)
  · refine .intro fun σ _ hm => ?_
    obtain ⟨ws, he, hws⟩ := pv_ctor (pvs_at_kcm2 hm (n := 2) rfl rfl)
    cases he
    rcases hws with _ | ⟨-, _ | ⟨h1, -⟩⟩
    obtain ⟨_, he, -⟩ := pv_ctor h1
    exact absurd (GroundTerm.ctor.inj he).1 (by decide)
  · refine .intro fun σ _ hm => .intro rfl (ev_and_khc (ev_isElem_khc (ev_var (headAt_kcm2 hm (n := 2) (i := 6) rfl rfl)))
      (ev_kindNeT_khc (ev_var (varAt_kcm2 hm (n := 0) (i := 4) rfl rfl)))) (ne_true_kcm2 (by simp [hf]))
  · exact failsAt_kcm2 2 rfl rfl (by decide)
  · exact failsAt_kcm2 0 (h := h) (us := us) rfl (by rw [List.getElem?_cons_zero, hkh]) hne

/-- `matchCol` at every list of parts each of which `match` evaluates, by induction on the list:
the equation that applies at the first part is the one `matchColF` takes. -/
theorem colAt_kcm2 : ∀ ps : List T, (∀ q ∈ ps, MatchAtKme S q) → ∀ k c, ColAtKcm2 S k c ps
  | [], _, k, c => colAt_nil_kcm2 S k c
  | p :: ps, h, k, c => by
    have ihp := h p (List.mem_cons_self ..)
    have ih := colAt_kcm2 ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    cases hp : isElemT p with
    | true =>
      by_cases hk : k = .list
      · subst hk; exact colAt_head_kcm2 S c hp ihp (ih .list c)
      · exact colAt_choose_kcm2 S hk c hp ihp (ih k c)
    | false =>
      cases ps with
      | nil => exact colAt_frame_kcm2 S k c hp ihp
      | cons q qs =>
        by_cases hk : k = .list
        · subst hk; exact colAt_split_kcm2 S c hp ihp (ih .list c)
        · exact colAt_frameMore_kcm2 S hk c hp

end Steps

/-! ## Every pattern -/

section All
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts

/-- `match` evaluates to `matchF` at every pattern. -/
theorem matchAt_kcm2 (S : List (Int × Int)) (p : T) : MatchAtKme S p := by
  induction p using tInd_kkc with
  | hap f as ih => exact matchAt_ap_kme S f (matchTsAt_of_kme S as ih)
  | hiv i => exact matchAt_iv_kme S i
  | hbv b => exact matchAt_bv_kme S b
  | htk s x => exact matchAt_tk_kme S s x
  | hij a b t ih => exact matchAt_ij_kme S a b ih
  | hvr i => exact matchAt_vr_kme S i
  | has p i ih => exact matchAt_as_kme S i ih
  | hhk o as _ => exact matchAt_hk_kme S o as
  | hbot => exact matchAt_bot_kme S
  | hcb k c ps ih => exact matchAt_cb_kme S k c ps (colAt_kcm2 S ps ih k c)
  | hco k c es _ => exact matchAt_co_kme S k c es
  | hen t e _ _ => exact matchAt_en_kme S t e
  | hkv a v iha ihv =>
    refine matchAt_kv_kme S (matchTsAt_of_kme S [a, v] fun q hq => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact iha
    · exact ihv
  | hel x ih => exact matchAt_el_kme S ih

end All

/-! ## At `K₀ sig` -/

/-- **`match` on embedded mirrors is `matchF`**, at every pattern, a collection pattern included,
every subject, substitution and subsort table. -/
theorem match_eval_col (S : List (Int × Int)) (p a : T) (B : Bind) :
    Eval (K₀ sig) 486 [emb p, emb a, embB B, embS S] ((matchF S p a B).map embMs) :=
  matchAt_kcm2 S p a B

theorem match_eval_col_iff (S : List (Int × Int)) (p a : T) (B : Bind) {r : Option GroundTerm} :
    Eval (K₀ sig) 486 [emb p, emb a, embB B, embS S] r ↔ r = (matchF S p a B).map embMs :=
  evalF_iff (match_eval_col S p a B)

/-- `matchTs` on embedded mirrors is `matchTsF` at every list of patterns. -/
theorem matchTs_eval_col (S : List (Int × Int)) (ps ts : List T) (B : Bind) :
    Eval (K₀ sig) 489 [embTs ps, embTs ts, embB B, embS S] ((matchTsF S ps ts B).map embMs) :=
  matchTsAt_of_kme S ps (fun p _ => matchAt_kcm2 S p) ts B

theorem matchTs_eval_col_iff (S : List (Int × Int)) (ps ts : List T) (B : Bind) {r : Option GroundTerm} :
    Eval (K₀ sig) 489 [embTs ps, embTs ts, embB B, embS S] r ↔ r = (matchTsF S ps ts B).map embMs :=
  evalF_iff (matchTs_eval_col S ps ts B)

/-- `matchK` on embedded mirrors is `matchKF` at every list of patterns. -/
theorem matchK_eval_col (S : List (Int × Int)) (ms : Ms) (ps ts : List T) :
    Eval (K₀ sig) 488 [embMs ms, embTs ps, embTs ts, embS S] ((matchKF S ms ps ts).map embMs) :=
  matchK_eval_kme S (matchTsAt_of_kme S ps fun p _ => matchAt_kcm2 S p) ms ts

theorem matchK_eval_col_iff (S : List (Int × Int)) (ms : Ms) (ps ts : List T) {r : Option GroundTerm} :
    Eval (K₀ sig) 488 [embMs ms, embTs ps, embTs ts, embS S] r ↔ r = (matchKF S ms ps ts).map embMs :=
  evalF_iff (matchK_eval_col S ms ps ts)

/-- **`matchCol` on embedded mirrors is `matchColF`.** -/
theorem matchColF.eval (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (B : Bind) :
    Eval (K₀ sig) 487 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S]
      ((matchColF S k c ps es B).map embMs) :=
  colAt_kcm2 S ps (fun p _ => matchAt_kcm2 S p) k c es B

theorem matchColF.eval_iff (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 487 [embK k, .dv 3 (.int c), embTs ps, embTs es, embB B, embS S] r ↔
      r = (matchColF S k c ps es B).map embMs :=
  evalF_iff (matchColF.eval S k c ps es B)

/-- `rest` on embedded mirrors is `restF`. -/
theorem restF.eval (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (ms : Ms) :
    Eval (K₀ sig) 501 [embK k, .dv 3 (.int c), embTs ps, embTs es, embMs ms, embS S]
      ((restF S k c ps es ms).map embMs) :=
  rest_eval_kcm2 S (colAt_kcm2 S ps (fun p _ => matchAt_kcm2 S p) k c) es ms

theorem restF.eval_iff (S : List (Int × Int)) (k : Kind) (c : Int) (ps es : List T) (ms : Ms)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 501 [embK k, .dv 3 (.int c), embTs ps, embTs es, embMs ms, embS S] r ↔
      r = (restF S k c ps es ms).map embMs :=
  evalF_iff (restF.eval S k c ps es ms)

/-- `choose` on embedded mirrors is `chooseF`. -/
theorem chooseF.eval (S : List (Int × Int)) (k : Kind) (c : Int) (p : T) (ps pre post : List T) (B : Bind) :
    Eval (K₀ sig) 454 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((chooseF S k c p ps pre post B).map embMs) :=
  choose_eval_kcm2 S (matchAt_kcm2 S p) (colAt_kcm2 S ps (fun q _ => matchAt_kcm2 S q) k c) post pre B

theorem chooseF.eval_iff (S : List (Int × Int)) (k : Kind) (c : Int) (p : T) (ps pre post : List T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 454 [embK k, .dv 3 (.int c), emb p, embTs ps, embTs pre, embTs post, embB B, embS S] r ↔
      r = (chooseF S k c p ps pre post B).map embMs :=
  evalF_iff (chooseF.eval S k c p ps pre post B)

/-- `split` on embedded mirrors is `splitF`. -/
theorem splitF.eval (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind) :
    Eval (K₀ sig) 504 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitF S c f ps pre post B).map embMs) :=
  split_eval_kcm2 S (matchAt_kcm2 S f) (colAt_kcm2 S ps (fun q _ => matchAt_kcm2 S q) .list c) post pre B

theorem splitF.eval_iff (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 504 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S] r ↔
      r = (splitF S c f ps pre post B).map embMs :=
  evalF_iff (splitF.eval S c f ps pre post B)

/-- `splitOn` on embedded mirrors is `splitOnF`. -/
theorem splitOnF.eval (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind) :
    Eval (K₀ sig) 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S]
      ((splitOnF S c f ps pre post B).map embMs) :=
  splitOn_eval_kcm2 S (matchAt_kcm2 S f) (colAt_kcm2 S ps (fun q _ => matchAt_kcm2 S q) .list c) pre post B

theorem splitOnF.eval_iff (S : List (Int × Int)) (c : Int) (f : T) (ps pre post : List T) (B : Bind)
    {r : Option GroundTerm} :
    Eval (K₀ sig) 505 [.dv 3 (.int c), emb f, embTs ps, embTs pre, embTs post, embB B, embS S] r ↔
      r = (splitOnF S c f ps pre post B).map embMs :=
  evalF_iff (splitOnF.eval S c f ps pre post B)

/-! ## Checks -/

#check @match_eval_col
#check @match_eval_col_iff
#check @matchTs_eval_col
#check @matchK_eval_col
#check @matchColF.eval
#check @restF.eval
#check @chooseF.eval
#check @splitF.eval
#check @splitOnF.eval

open Lean in
#eval show CoreM Unit from do
  for n in [``colMatchEval_names_kcm2, ``match_eval_col, ``match_eval_col_iff, ``matchTs_eval_col,
      ``matchTs_eval_col_iff, ``matchK_eval_col, ``matchK_eval_col_iff, ``matchColF.eval, ``matchColF.eval_iff,
      ``restF.eval, ``restF.eval_iff, ``chooseF.eval, ``chooseF.eval_iff, ``splitF.eval, ``splitF.eval_iff,
      ``splitOnF.eval, ``splitOnF.eval_iff] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
