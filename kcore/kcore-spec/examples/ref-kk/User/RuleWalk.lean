/-
  kore.k's walk of the rewrite rules (`succs`, `stepAt`, `stepIf`, `fireAt`, `fire`, `fireM`)
  against the object semantics `d₀ d`, for `d` that `execReady` accepts with the kore.k definition
  `E` (`rule_walk`).

  kore.k's `succs` walks the priorities of the rules in ascending order (`nextRl`). At a priority
  `P` it lists, for each rule of priority `P` in the order of the text, for each substitution
  `match` gives its left side at the configuration whose `requires` is true, the right side's
  result (`fireAt`, `fire`, `fireM`). Where the list is empty it goes to the next priority
  (`stepIf`, `step-next`); else the successors are the list without `bot` (`step-some`); where no
  priority is left, the configuration is `stuck`.

  What a listed result is (`FiredBy_krw`): the encoding of the right side's result under a
  well-sorted substitution under which the left side denotes the configuration and the `requires`
  is true, or `bot` where the ensures is not true. What the walk has shown at a priority
  (`RuleBelow_krw`): no rule of a smaller priority applies. What the list at a priority is
  (`FiredAt_krw`): each member is a result of a rule of the priority, and each match of each rule
  of the priority fails its `requires` or has its result listed.

  `rule_walk`: either the result is `stuck` and no rule applies, or it is `next` of the list
  without `bot` at a priority `P` where the list is not empty, no rule below `P` applies, and the
  list is that of the rules at `P`. A listed result other than `bot` is a step of `d₀ d`
  (`firedBy_step_krw`); a non-empty list has a rule at `P` that applies (`firedAt_applies_krw`);
  an empty one has none (`firedAt_nil_krw`). "Stuck exactly when no rule applies" holds here in one
  direction only: the converse needs that a `requires` has one result, `hco`'s
  (kk-succs-char).

  The shapes of the rules (no existential variable, `\top` predicates, a left side that binds
  every variable) are C12's (`shapesOK`), read from `encDef d = some E`.

  The route: `fireM`, `fire`, `fireAt` recurse on lists and are proved by induction on them;
  `stepAt` and `stepIf` call each other along the priorities, and are proved by a second
  `Eval.calls_induct` at `K₀ sig` with the motive `RSpec_krw`. The calls of `eval` are read by
  `Spec` (User.SpecAll's `spec_all`).
-/
import User.SpecAll

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option Elab.async false

namespace KCore.KK

/-! ## The functions of the rule walk, as the semantics holds them -/

namespace WalkR
open _root_.KK Terms

/-- `succs` (510): `succs`. -/
def succsDef_krw : Fn :=
  { label := 510, args := [45, 33], result := 38, total := false, clauses := [
    plainCl [32, 39, 42, 45, 33] [.as (.app 417 [.var 0, .var 1, .var 2]) 3, .var 4]
      (.app 506 [.var 3, .var 2, .var 4, .app 496 [.var 2, .app 431 []]])] }

/-- `stepAt` (506): `step-at`, `step-none`. -/
def stepAtDef_krw : Fn :=
  { label := 506, args := [45, 42, 33, 36], result := 38, total := false, clauses := [
    plainCl [45, 42, 33, 3] [.var 0, .var 1, .var 2, .app 410 [.var 3]]
      (.app 507 [.var 0, .var 1, .var 2, .var 3, .app 469 [.var 0, .var 1, .var 2, .var 3]]),
    plainCl [45, 42, 33] [.var 0, .var 1, .var 2, .app 431 []] (.app 441 [])] }

/-- `stepIf` (507): `step-next`, `step-some`. -/
def stepIfDef_krw : Fn :=
  { label := 507, args := [45, 42, 33, 3, 43], result := 38, total := false, clauses := [
    plainCl [45, 42, 33, 3] [.var 0, .var 1, .var 2, .var 3, .app 406 []]
      (.app 506 [.var 0, .var 1, .var 2, .app 496 [.var 1, .app 410 [.var 3]]]),
    plainCl [45, 42, 33, 3, 33, 43, 43]
      [.var 0, .var 1, .var 2, .var 3, .as (.app 407 [.var 4, .var 5]) 6]
      (.app 430 [.app 462 [.app 412 [], .var 6]])] }

/-- `fireAt` (469): `fa-take`, `fa-skip`, `fa-nil`. -/
def fireAtDef_krw : Fn :=
  { label := 469, args := [45, 42, 33, 3], result := 43, total := false, clauses := [
    plainCl [45, 3, 2, 33, 33, 33, 42, 33, 3]
      [.var 0, .app 436 [.var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .var 7, .var 8]
      (.app 447 [.app 468 [.var 0, .var 3, .var 4, .var 5, .var 7], .app 469 [.var 0, .var 6, .var 7, .var 8]])
      (req := some (.app 23 [.app 503 [.var 1, .var 2], .var 8])),
    plainCl [45, 3, 2, 33, 33, 33, 42, 33, 3]
      [.var 0, .app 436 [.var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .var 7, .var 8]
      (.app 469 [.var 0, .var 6, .var 7, .var 8])
      (req := some (.app 24 [.app 503 [.var 1, .var 2], .var 8])),
    plainCl [45, 33, 3] [.var 0, .app 404 [], .var 1, .var 2] (.app 406 [])] }

/-- `fire` (468): `fire`. -/
def fireDef_krw : Fn :=
  { label := 468, args := [45, 33, 33, 33, 33], result := 43, total := false, clauses := [
    plainCl [45, 33, 33, 33, 33] [.var 0, .var 1, .var 2, .var 3, .var 4]
      (.app 470 [.var 0, .var 2, .var 3, .app 486 [.var 1, .var 4, .app 400 [], .app 509 [.var 0]]])] }

/-- `fireM` (470): `fire-holds`, `fire-refuted`, `fire-nomatch`. Its `requires` are `tryM`'s. -/
def fireMDef_krw : Fn :=
  { label := 470, args := [45, 33, 33, 37], result := 43, total := false, clauses := [
    plainCl [45, 33, 33, 46, 37] [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]]
      (.app 407 [.app 464 [.var 0, .app 476 [.var 2, .var 3]], .app 470 [.var 0, .var 1, .var 2, .var 4]])
      (req := some (WalkV.reqT_ksc 29 0 1 3)),
    plainCl [45, 33, 33, 46, 37] [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]]
      (.app 470 [.var 0, .var 1, .var 2, .var 4]) (req := some (WalkV.reqT_ksc 30 0 1 3)),
    plainCl [45, 33, 33] [.var 0, .var 1, .var 2, .app 403 []] (.app 406 [])] }

theorem succsDef_lookup_krw : c₀.lookupFn 510 = some succsDef_krw := by kernel_rfl
theorem stepAtDef_lookup_krw : c₀.lookupFn 506 = some stepAtDef_krw := by kernel_rfl
theorem stepIfDef_lookup_krw : c₀.lookupFn 507 = some stepIfDef_krw := by kernel_rfl
theorem fireAtDef_lookup_krw : c₀.lookupFn 469 = some fireAtDef_krw := by kernel_rfl
theorem fireDef_lookup_krw : c₀.lookupFn 468 = some fireDef_krw := by kernel_rfl
theorem fireMDef_lookup_krw : c₀.lookupFn 470 = some fireMDef_krw := by kernel_rfl

/-- Each symbol number of the walk has the KORE name of the function. -/
theorem walk_names_krw :
    RefKk.defn.sem.symName 506 = "LblstepAt'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Step'Unds'Def'Unds'Rules'Unds'Term'Unds'Prio" ∧
    RefKk.defn.sem.symName 507 = "LblstepIf'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Step'Unds'Def'Unds'Rules'Unds'Term'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 469 = "LblfireAt'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Def'Unds'Rules'Unds'Term'Unds'Int" ∧
    RefKk.defn.sem.symName 468 = "Lblfire'LParUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Def'Unds'Term'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 470 = "LblfireM'LParUndsCommUndsCommUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Def'Unds'Term'Unds'Term'Unds'Ms" ∧
    RefKk.defn.sem.symName 447 = "Lblapp'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Ts'Unds'Ts" ∧
    RefKk.defn.sem.symName 462 = "Lbldrop'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 496 = "LblnextRl'LParUndsCommUndsRParUnds'KORE'Unds'Prio'Unds'Rules'Unds'Prio" ∧
    RefKk.defn.sem.symName 503 = "Lblrprio'LParUndsCommUndsRParUnds'KORE'Unds'Int'Unds'Int'Unds'Bool" := by
  decide +kernel

end WalkR

/-! ## Inverting a call of the walk -/

section Inv
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

variable {R : CallRel}

/-- kore.k's `app` over the mirrors is the append. -/
theorem appF_eq_krw : ∀ xs ys : List T, Gen.appF xs ys = some (xs ++ ys)
  | [], _ => rfl
  | x :: xs, ys => by simp only [Gen.appF, appF_eq_krw xs ys]; rfl

theorem succsPlain_krw : ∀ cl ∈ WalkR.succsDef_krw.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkR.succsDef_krw
theorem stepAtPlain_krw : ∀ cl ∈ WalkR.stepAtDef_krw.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkR.stepAtDef_krw
theorem stepIfPlain_krw : ∀ cl ∈ WalkR.stepIfDef_krw.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkR.stepIfDef_krw
theorem firePlain_krw : ∀ cl ∈ WalkR.fireDef_krw.clauses,
    cl.req = none ∧ cl.ens = none ∧ cl.exs = [] ∧ cl.pre = .top := by ksc_plain WalkR.fireDef_krw
theorem fireAtPlain_krw : ∀ cl ∈ WalkR.fireAtDef_krw.clauses, cl.ens = none ∧ cl.exs = [] := by
  intro cl hcl
  simp only [WalkR.fireAtDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
theorem fireMPlain_krw : ∀ cl ∈ WalkR.fireMDef_krw.clauses, cl.ens = none ∧ cl.exs = [] := by
  intro cl hcl
  simp only [WalkR.fireMDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **`succs` inverted**: `stepAt` at the rules and the first priority. -/
theorem succs_inv_krw (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {t : T}
    {r : Option GroundTerm} (hb : ByClause c₀ R 510 [embD E, emb t] r) :
    R 506 [embD E, embRls E.rules, emb t, embPrio (nextRlF E.rules none)] r := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.succsDef_lookup_krw succsPlain_krw
    (List.mem_cons_self ..)
    (σ₀ := enumFrom 0 [embS E.subs, embFns E.fns, embRls E.rules, embD E, emb t])
    (ws_enum (.cons (embS_sorted_c₀ E.subs) (.cons (embFns_sorted_c₀ E.fns)
      (.cons (embRls_sorted_c₀ E.rules) (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ t) .nil))))))
    (.cons (.as (.ctor ctor_417 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))) rfl)
      (.cons (.var rfl) .nil))
  simp only [WalkR.succsDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  rcases hmatch with _ | ⟨h0, _ | ⟨h4, _ | _⟩⟩
  obtain ⟨h0, h3⟩ := PatVal.as_inv h0
  obtain ⟨xs, he, hxs⟩ := pv_ctor h0
  cases he
  rcases hxs with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | _⟩⟩⟩
  have h2 := PatVal.var_inv h2
  have h4 := PatVal.var_inv h4
  obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 3, .var 2, .var 4]) notCtor_506
    notHook_506 notParam_506 (by decide +kernel) (.cons h3 (.cons h2 (.cons h4 .nil))) hrhs
  have hv := EvalTermR.helper_val_ksc hR hq
    (ev_call (.cons (ev_var h2) (.cons (ev_ctor .nil (f := 431)) .nil)) (nextRlF.eval E.rules none))
  subst hv
  rcases hcase with ⟨y, hy, hR'⟩ | ⟨hn, -⟩
  · cases hy; exact hR'
  · cases hn

/-- **`stepAt` inverted**: at `noP`, `stuck`; at `at(P)`, `fireAt` at `P`, then `stepIf`. -/
theorem stepAt_inv_krw {E : D} {rs : List Rl} {t : T} {p : Option Int} {r : Option GroundTerm}
    (hb : ByClause c₀ R 506 [embD E, embRls rs, emb t, embPrio p] r) :
    (p = none ∧ r = some (embSt .stuck)) ∨
      ∃ P, p = some P ∧ ∃ q, R 469 [embD E, embRls rs, emb t, .dv 3 (.int P)] q ∧
        ((∃ y, q = some y ∧ R 507 [embD E, embRls rs, emb t, .dv 3 (.int P), y] r) ∨
          (q = none ∧ r = none)) := by
  cases p with
  | none =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.stepAtDef_lookup_krw
      stepAtPlain_krw (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, embRls rs, emb t])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embRls_sorted_c₀ rs) (.cons (emb_sorted_c₀ t) .nil))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_431 .nil) .nil))))
    simp only [WalkR.stepAtDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
    · obtain ⟨rs', hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
      cases hrs
      exact .inl ⟨rfl, rfl⟩
  | some P =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.stepAtDef_lookup_krw
      stepAtPlain_krw (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [embD E, embRls rs, emb t, .dv 3 (.int P)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embRls_sorted_c₀ rs) (.cons (emb_sorted_c₀ t)
        (.cons (sort_int P) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_410 (.cons (.var rfl) .nil)) .nil))))
    simp only [WalkR.stepAtDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
    · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
      cases he
      rcases hxs with _ | ⟨h3, _ | _⟩
      have hv : VarsAre_ksc σ [.var 0, .var 1, .var 2, .var 3]
          [embD E, embRls rs, emb t, .dv 3 (.int P)] :=
        .cons (PatVal.var_inv h0) (.cons (PatVal.var_inv h1) (.cons (PatVal.var_inv h2)
          (.cons (PatVal.var_inv h3) .nil)))
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc notCtor_507 notHook_507 notParam_507
        (by decide +kernel) hv hrhs
      exact .inr ⟨P, rfl, q, EvalTermR.callVars_ksc notCtor_469 notHook_469 notParam_469
        (by decide +kernel) hv hq, hcase⟩
    · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim

/-- **`stepIf` inverted**: at `.Ts`, `stepAt` at the next priority; at a list that is not
empty, `next` of the list without `bot`. -/
theorem stepIf_inv_krw (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {rs : List Rl} {t : T}
    {P : Int} {us : List T} {r : Option GroundTerm}
    (hb : ByClause c₀ R 507 [embD E, embRls rs, emb t, .dv 3 (.int P), embTs us] r) :
    (us = [] ∧ R 506 [embD E, embRls rs, emb t, embPrio (nextRlF rs (some P))] r) ∨
      (us ≠ [] ∧ r = some (embSt (.next (dropF .bot us)))) := by
  cases us with
  | nil =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.stepIfDef_lookup_krw
      stepIfPlain_krw (List.mem_cons_self ..)
      (σ₀ := enumFrom 0 [embD E, embRls rs, emb t, .dv 3 (.int P)])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embRls_sorted_c₀ rs) (.cons (emb_sorted_c₀ t)
        (.cons (sort_int P) .nil)))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.ctor ctor_406 .nil) .nil)))))
    simp only [WalkR.stepIfDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;>
      rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
    · have h0 := PatVal.var_inv h0
      have h1 := PatVal.var_inv h1
      have h2 := PatVal.var_inv h2
      have h3 := PatVal.var_inv h3
      obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 0, .var 1, .var 2]) notCtor_506
        notHook_506 notParam_506 (by decide +kernel) (.cons h0 (.cons h1 (.cons h2 .nil))) hrhs
      have hv := EvalTermR.helper_val_ksc hR hq
        (ev_call (.cons (ev_var h1) (.cons (ev_ctor (.cons (ev_var h3) .nil)) .nil))
          (nextRlF.eval rs (some P)))
      subst hv
      rcases hcase with ⟨y, hy, hR'⟩ | ⟨hn, -⟩
      · cases hy; exact .inl ⟨rfl, hR'⟩
      · cases hn
    · exact (patCtor_ne_kht (PatVal.as_inv h4).1 (fun ws h => by cases h)).elim
  | cons u us' =>
    obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.stepIfDef_lookup_krw
      stepIfPlain_krw (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (σ₀ := enumFrom 0 [embD E, embRls rs, emb t, .dv 3 (.int P), emb u, embTs us', embTs (u :: us')])
      (ws_enum (.cons (embD_sorted_c₀ E) (.cons (embRls_sorted_c₀ rs) (.cons (emb_sorted_c₀ t)
        (.cons (sort_int P) (.cons (emb_sorted_c₀ u) (.cons (embTs_sorted_c₀ us')
          (.cons (embTs_sorted_c₀ _) .nil))))))))
      (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
        (.cons (.as (.ctor ctor_407 (.cons (.var rfl) (.cons (.var rfl) .nil))) rfl) .nil)))))
    simp only [WalkR.stepIfDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;>
      rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
    · exact (patCtor_ne_kht h4 (fun ws h => by cases h)).elim
    · have h6 := (PatVal.as_inv h4).2
      refine .inr ⟨List.cons_ne_nil _ _, EvalTermR.helper_val_ksc hR hrhs ?_⟩
      exact ev_ctor (.cons (ev_call (.cons (ev_ctor .nil (f := 412)) (.cons (ev_var h6) .nil))
        (dropF.eval .bot (u :: us'))) .nil)

/-- `rprio(Q, O) ==Int P` and `=/=Int`, forward. -/
theorem rprioCmp_eval_krw {σ : Subst} {p : Int} {o : Bool} {P : Int}
    (h1 : σ.lookup 1 = some (.dv 3 (.int p))) (h2 : σ.lookup 2 = some (.dv 2 (.bool o)))
    (h8 : σ.lookup 8 = some (.dv 3 (.int P))) :
    EvalTerm c₀ σ (.app 23 [.app 503 [.var 1, .var 2], .var 8]) (some (bool (decide (rprioF p o = P)))) ∧
    EvalTerm c₀ σ (.app 24 [.app 503 [.var 1, .var 2], .var 8]) (some (bool (decide (rprioF p o ≠ P)))) :=
  have hc := ev_call (σ := σ) (.cons (ev_var h1) (.cons (ev_var h2) .nil)) (rprioF.eval p o)
  ⟨ev_int2 (P := (· = ·)) hook_intEq hc (ev_var h8), ev_int2 (P := (· ≠ ·)) hook_intNe hc (ev_var h8)⟩

/-- **`fireAt` inverted**: at `.Rules`, `.Ts`; at a rule of priority `P`, `fire` at it and
`fireAt` at the rest, appended; at a rule of another priority, `fireAt` at the rest. -/
theorem fireAt_inv_krw (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {rs : List Rl} {t : T}
    {P : Int} {r : Option GroundTerm}
    (hb : ByClause c₀ R 469 [embD E, embRls rs, emb t, .dv 3 (.int P)] r) :
    (rs = [] ∧ r = some (embTs [])) ∨
      ∃ c rs', rs = c :: rs' ∧
        ((rprioF c.prio c.owise = P ∧ ∃ q₁ q₂,
            R 468 [embD E, emb c.lhs, emb c.req, emb c.rhs, emb t] q₁ ∧
            R 469 [embD E, embRls rs', emb t, .dv 3 (.int P)] q₂ ∧
            ∀ us₁ us₂, q₁ = some (embTs us₁) → q₂ = some (embTs us₂) → r = some (embTs (us₁ ++ us₂))) ∨
         (rprioF c.prio c.owise ≠ P ∧ R 469 [embD E, embRls rs', emb t, .dv 3 (.int P)] r)) := by
  have hcases := byClause_cases_ksc hb WalkR.fireAtDef_lookup_krw fireAtPlain_krw
  cases rs with
  | nil =>
    refine .inl ⟨rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, -, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkR.fireAtDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨-, _ | ⟨h1, _ | ⟨-, _ | ⟨-, _ | _⟩⟩⟩⟩
      · exact (patCtor_ne_kht h1 (fun ws h => by cases h)).elim
      · exact (patCtor_ne_kht h1 (fun ws h => by cases h)).elim
      · obtain ⟨rs', hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
        cases hrs; rfl
    · obtain ⟨_, _, hq, -⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl
        (σ := enumFrom 0 [embD E, emb t, .dv 3 (.int P)])
        (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ t) (.cons (sort_int P) .nil))))
        (.cons (.var rfl) (.cons (.ctor ctor_404 .nil) (.cons (.var rfl) (.cons (.var rfl) .nil))))
      cases hq
  | cons c rs' =>
    refine .inr ⟨c, rs', rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, hreq, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkR.fireAtDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h7, _ | ⟨h8, _ | _⟩⟩⟩⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h1
        cases he
        rcases hxs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | _⟩⟩⟩⟩⟩⟩
        have h0 := PatVal.var_inv h0
        have h7 := PatVal.var_inv h7
        have h8 := PatVal.var_inv h8
        have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
          (rprioCmp_eval_krw (PatVal.var_inv g1) (PatVal.var_inv g2) h8).1
        have hP : rprioF c.prio c.owise = P := by simpa [bool] using hq
        obtain ⟨qs, hts, hcase⟩ := EvalTermR.call_inv_kst notCtor_447 notHook_447 notParam_447
          (by decide +kernel) hrhs
        rcases hts with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩
        rename_i q₁ q₂
        refine .inl ⟨hP, q₁, q₂,
          EvalTermR.callVars_ksc notCtor_468 notHook_468 notParam_468 (by decide +kernel)
            (.cons h0 (.cons (PatVal.var_inv g3) (.cons (PatVal.var_inv g4) (.cons (PatVal.var_inv g5)
              (.cons h7 .nil))))) a1,
          EvalTermR.callVars_ksc notCtor_469 notHook_469 notParam_469 (by decide +kernel)
            (.cons h0 (.cons (PatVal.var_inv g6) (.cons h7 (.cons h8 .nil)))) a2,
          fun us₁ us₂ e1 e2 => ?_⟩
        subst e1 e2
        rcases hcase with ⟨vs, hvs, hR'⟩ | ⟨hn, -⟩
        · cases hvs
          have := (Gen.appF.eval_iff us₁ us₂).mp (hR _ _ _ hR')
          rw [this, appF_eq_krw]; rfl
        · cases hn
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h1
        cases he
        rcases hxs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | _⟩⟩⟩⟩⟩⟩
        have h0 := PatVal.var_inv h0
        have h7 := PatVal.var_inv h7
        have h8 := PatVal.var_inv h8
        have hq := EvalTermR.helper_val_ksc hR (hreq _ rfl)
          (rprioCmp_eval_krw (PatVal.var_inv g1) (PatVal.var_inv g2) h8).2
        have hP : rprioF c.prio c.owise ≠ P := by simpa [bool] using hq
        exact .inr ⟨hP, EvalTermR.callVars_ksc notCtor_469 notHook_469 notParam_469 (by decide +kernel)
          (.cons h0 (.cons (PatVal.var_inv g6) (.cons h7 (.cons h8 .nil)))) hrhs⟩
      · exact (patCtor_ne_kht h1 (fun ws h => by cases h)).elim
    · have hσ₀ := ws_enum (vars := [45, 3, 2, 33, 33, 33, 42, 33, 3]) (.cons (embD_sorted_c₀ E)
        (.cons (sort_int c.prio) (.cons (sort_bool c.owise) (.cons (emb_sorted_c₀ c.lhs)
          (.cons (emb_sorted_c₀ c.req) (.cons (emb_sorted_c₀ c.rhs) (.cons (embRls_sorted_c₀ rs')
            (.cons (emb_sorted_c₀ t) (.cons (sort_int P) .nil)))))))))
      have hp₀ : PatVals c₀ (enumFrom 0 [embD E, .dv 3 (.int c.prio), .dv 2 (.bool c.owise),
            emb c.lhs, emb c.req, emb c.rhs, embRls rs', emb t, .dv 3 (.int P)])
          [.var 0, .app 436 [.var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .var 7, .var 8]
          [embD E, embRls (c :: rs'), emb t, .dv 3 (.int P)] :=
        .cons (.var rfl) (.cons (.ctor ctor_436 (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
          (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))))))) (.cons (.var rfl) (.cons (.var rfl) .nil)))
      obtain ⟨t1, r1, he1, hr1, hne1⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_self ..)) rfl hσ₀ hp₀
      obtain ⟨t2, r2, he2, hr2, hne2⟩ := FailsR.req_ksc
        (hfail _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl hσ₀ hp₀
      cases he1
      cases he2
      have hc := rprioCmp_eval_krw (σ := enumFrom 0 [embD E, .dv 3 (.int c.prio),
        .dv 2 (.bool c.owise), emb c.lhs, emb c.req, emb c.rhs, embRls rs', emb t, .dv 3 (.int P)])
        rfl rfl rfl
      rw [EvalTermR.helper_val_ksc hR hr1 hc.1] at hne1
      rw [EvalTermR.helper_val_ksc hR hr2 hc.2] at hne2
      by_cases h : rprioF c.prio c.owise = P
      · exact (hne1 (by simp [h])).elim
      · exact (hne2 (by simp [h])).elim

/-- **`fire` inverted**: `fireM` at what `match` gives the rule's left side, none where it gives
none. -/
theorem fire_inv_krw (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {lhs req rhs t : T}
    {r : Option GroundTerm} (hb : ByClause c₀ R 468 [embD E, emb lhs, emb req, emb rhs, emb t] r) :
    (∃ M, matchF E.subs lhs t [] = some M ∧ R 470 [embD E, emb req, emb rhs, embMs M] r) ∨
      (matchF E.subs lhs t [] = none ∧ r = none) := by
  obtain ⟨cl, hmem, σ, hmatch, hrhs⟩ := byClause_plain_kst hb WalkR.fireDef_lookup_krw firePlain_krw
    (List.mem_cons_self ..)
    (σ₀ := enumFrom 0 [embD E, emb lhs, emb req, emb rhs, emb t])
    (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ lhs) (.cons (emb_sorted_c₀ req)
      (.cons (emb_sorted_c₀ rhs) (.cons (emb_sorted_c₀ t) .nil))))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))))
  simp only [WalkR.fireDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | _⟩⟩⟩⟩⟩
  have h0 := PatVal.var_inv h0
  have h1 := PatVal.var_inv h1
  have h2 := PatVal.var_inv h2
  have h3 := PatVal.var_inv h3
  have h4 := PatVal.var_inv h4
  obtain ⟨q, hq, hcase⟩ := EvalTermR.callVarsT_ksc (ts := [.var 0, .var 2, .var 3]) notCtor_470
    notHook_470 notParam_470 (by decide +kernel) (.cons h0 (.cons h2 (.cons h3 .nil))) hrhs
  have hsubs : EvalTerm c₀ σ (.app 509 [.var 0]) (some (embS E.subs)) :=
    ev_call (.cons (ev_var h0) .nil) (Gen.subsOfF.eval E)
  have hv := EvalTermR.helper_val_ksc hR hq
    (ev_call (.cons (ev_var h1) (.cons (ev_var h4) (.cons (ev_ctor .nil (f := 400)) (.cons hsubs .nil))))
      (match_eval_col E.subs lhs t []))
  subst hv
  cases hM : matchF E.subs lhs t [] with
  | none =>
    rw [hM] at hcase
    rcases hcase with ⟨_, hy, -⟩ | ⟨-, hr⟩
    · cases hy
    · exact .inr ⟨rfl, hr⟩
  | some M =>
    rw [hM] at hcase
    rcases hcase with ⟨_, hy, hR'⟩ | ⟨hn, -⟩
    · cases hy; exact .inl ⟨M, rfl, hR'⟩
    · cases hn

/-- **`fireM` inverted.** At `.Ms`, `.Ts`. At `m(B, Ms)` and an instance `t` of the `requires`'
form under `B`: `fire-holds` (the call of `eval` at `t` gives `bv(true)`, and the result is the
list of `eval` at the right side's instance and `fireM` at `Ms`), `fire-refuted` (it gives no
`bv(true)`, and the result is `fireM` at `Ms`), or neither applies (two calls of `eval` at `t`,
one giving `bv(true)` and one not). -/
theorem fireM_inv_krw (hR : ∀ g ws q, R g ws q → Eval c₀ g ws q) {E : D} {req rhs : T} {ms : Ms}
    {r : Option GroundTerm} (hb : ByClause c₀ R 470 [embD E, emb req, emb rhs, embMs ms] r) :
    (ms = [] ∧ r = some (embTs [])) ∨
    ∃ B ms', ms = B :: ms' ∧ ∀ t, instF req B = some t →
      (∃ q, R 464 [embD E, emb t] q ∧ (∀ u, q = some (emb u) → u = .bv true) ∧
        ∃ q' q'', R 470 [embD E, emb req, emb rhs, embMs ms'] q'' ∧
          r = (allSome [q', q'']).map (.ctor 407) ∧
          ((instF rhs B = none ∧ q' = none) ∨
            ∃ t', instF rhs B = some t' ∧ R 464 [embD E, emb t'] q')) ∨
      (∃ q, R 464 [embD E, emb t] q ∧ (∀ u, q = some (emb u) → u ≠ .bv true) ∧
        R 470 [embD E, emb req, emb rhs, embMs ms'] r) ∨
      (∃ q q', R 464 [embD E, emb t] q ∧ R 464 [embD E, emb t] q' ∧
        (∀ u, q = some (emb u) → u = .bv true) ∧ (∀ u, q' = some (emb u) → u ≠ .bv true)) := by
  have hcases := byClause_cases_ksc hb WalkR.fireMDef_lookup_krw fireMPlain_krw
  cases ms with
  | nil =>
    refine .inl ⟨rfl, ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, -, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkR.fireMDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨-, _ | ⟨h3, _ | _⟩⟩⟩⟩
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
      · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
        cases hrs; rfl
    · obtain ⟨_, _, hq, -⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl
        (σ := enumFrom 0 [embD E, emb req, emb rhs])
        (ws_enum (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ req) (.cons (emb_sorted_c₀ rhs) .nil))))
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_403 .nil) .nil))))
      cases hq
  | cons B ms' =>
    refine .inr ⟨B, ms', rfl, fun t ht => ?_⟩
    rcases hcases with ⟨cl, hmem, σ, -, hmatch, hreq, hrhs⟩ | ⟨-, hfail⟩
    · simp only [WalkR.fireMDef_krw, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
        cases he
        rcases hxs with _ | ⟨hB, _ | ⟨hms, _ | _⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h2 := PatVal.var_inv h2
        have hB := PatVal.var_inv hB
        have hms := PatVal.var_inv hms
        obtain ⟨q, hq, hv⟩ := reqEq_inv_ksc hR h0 h1 hB (hreq _ rfl) ht
        refine .inl ⟨q, hq, fun u hu => ?_, ?_⟩
        · have := hv u hu
          by_cases hne : u = .bv true
          · exact hne
          · simp [hne, bool] at this
        · obtain ⟨rs, hrs, rfl⟩ := EvalTermR.ctor_inv_kst (by decide +kernel) hrhs
          rcases hrs with _ | ⟨e0, _ | ⟨e1, _ | _⟩⟩
          rename_i q' q''
          refine ⟨q', q'', EvalTermR.callVars_ksc notCtor_470 notHook_470 notParam_470
            (by decide +kernel) (.cons h0 (.cons h1 (.cons h2 (.cons hms .nil)))) e1, rfl, ?_⟩
          rcases instCall_inv_ksc hR h0 h2 hB e0 with ⟨hn, rfl⟩ | ⟨t', ht', hR'⟩
          · exact .inl ⟨hn, rfl⟩
          · exact .inr ⟨t', ht', hR'⟩
      · obtain ⟨xs, he, hxs⟩ := pv_ctor h3
        cases he
        rcases hxs with _ | ⟨hB, _ | ⟨hms, _ | _⟩⟩
        have h0 := PatVal.var_inv h0
        have h1 := PatVal.var_inv h1
        have h2 := PatVal.var_inv h2
        have hB := PatVal.var_inv hB
        have hms := PatVal.var_inv hms
        obtain ⟨q, hq, hv⟩ := reqNe_inv_ksc hR h0 h1 hB (hreq _ rfl) ht
        refine .inr (.inl ⟨q, hq, fun u hu he => ?_, EvalTermR.callVars_ksc notCtor_470 notHook_470
          notParam_470 (by decide +kernel) (.cons h0 (.cons h1 (.cons h2 (.cons hms .nil)))) hrhs⟩)
        have := hv u hu
        subst he
        simp [bool] at this
      · exact (patCtor_ne_kht h3 (fun ws h => by cases h)).elim
    · have hσ₀ := ws_enum (vars := [45, 33, 33, 46, 37]) (.cons (embD_sorted_c₀ E)
        (.cons (emb_sorted_c₀ req) (.cons (emb_sorted_c₀ rhs) (.cons (embB_sorted_c₀ B)
          (.cons (embMs_sorted_c₀ ms') .nil)))))
      have hp₀ : PatVals c₀ (enumFrom 0 [embD E, emb req, emb rhs, embB B, embMs ms'])
          [.var 0, .var 1, .var 2, .app 428 [.var 3, .var 4]] [embD E, emb req, emb rhs, embMs (B :: ms')] :=
        .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl)
          (.cons (.ctor ctor_428 (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil)))
      obtain ⟨t1, r1, he1, hr1, hne1⟩ := FailsR.req_ksc (hfail _ (List.mem_cons_self ..)) rfl hσ₀ hp₀
      obtain ⟨t2, r2, he2, hr2, hne2⟩ := FailsR.req_ksc
        (hfail _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl hσ₀ hp₀
      cases he1
      cases he2
      obtain ⟨q, hq, hv⟩ := reqEq_inv_ksc hR rfl rfl rfl hr1 ht
      obtain ⟨q', hq', hv'⟩ := reqNe_inv_ksc hR rfl rfl rfl hr2 ht
      refine .inr (.inr ⟨q', q, hq', hq, fun u hu => ?_, fun u hu he => ?_⟩)
      · rw [hv' u hu] at hne2
        by_cases hne : u = .bv true
        · exact hne
        · exact (hne2 (by simp [hne])).elim
      · rw [hv u hu] at hne1
        exact hne1 (by simp [he])

end Inv

end KCore.KK
