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

/-! ## The rules of `d₀ d` -/

section Rules
variable {d : Semantics}

theorem rules_d₀_krw (d : Semantics) : (d₀ d).rules = d.rules := rfl

/-- **C12 at a rule**: no existential variable, `\top` predicates, and the left side binds every
variable. -/
theorem ruleShape_krw (hc : encodable d = true) {r : Rule} (hm : r ∈ d.rules) :
    r.exs = [] ∧ r.pre = .top ∧ r.post = .top ∧ binds r.vars.length (varOccs r.lhs) = true := by
  have h12 : shapesOK d = true := by
    simp only [encodable, Bool.and_eq_true] at hc
    exact hc.1.2
  simp only [shapesOK, Bool.and_eq_true, List.all_eq_true] at h12
  have h := h12.1 r hm
  simp only [ruleShapeOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ho, he⟩, hpre⟩, hpost⟩ := h
  refine ⟨List.isEmpty_iff.mp he, Cond.eq_top_of_isTop hpre, Cond.eq_top_of_isTop hpost, ?_⟩
  rw [← opens_isEmpty_iff_binds]
  exact ho

/-- **The terms of a rule, sorted over function signatures**: the right side at the top cell
sort, the `requires` and the ensures at `Bool`. -/
theorem ruleTerms_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) :
    ∃ L, HeadsOK (d₀ d) L ∧ sortOfTerm ((d₀ d).rhsCtx L) r.vars r.rhs = some topCellSort ∧
      (∀ t, r.req = some t → sortOfTerm ((d₀ d).rhsCtx L) r.vars t = some Srt.bool) ∧
      (∀ e, r.ens = some e → sortOfTerm ((d₀ d).rhsCtx L) r.vars e = some Srt.bool) := by
  obtain ⟨hok, -, -, -⟩ := d₀_facts_kkv hr hc
  obtain ⟨hreq, hrhs⟩ := CExec.ruleSorted_of hok (show r ∈ (d₀ d).rules from hm)
  have hens := CExec.ruleSorted_ens_of hok (show r ∈ (d₀ d).rules from hm)
  exact ⟨_, headsOK_fns_kkv _, hrhs, fun t ht => reqOK_some_kkv hreq ht,
    fun e he => reqOK_some_kkv hens he⟩

/-- **The forms of a rule's terms** are those `encDef` writes, the `requires`, right side and
ensures without an alias, and the left side's `Map` and `Set` patterns of C8's shape. -/
theorem ruleEnc_krw (hc : encodable d = true) {r : Rule} (hm : r ∈ d.rules) :
    encTerm d r.lhs = some (encRl d r).lhs ∧ colPatOK (encRl d r).lhs = true ∧
      (∀ t, r.req = some t → encTerm d t = some (encReq d r.req) ∧ asFree t = true) ∧
      encTerm d r.rhs = some (encT d r.rhs) ∧ asFree r.rhs = true ∧
      (∀ e, r.ens = some e → encTerm d e = some (encT d e) ∧ asFree e = true) := by
  have hl : r.lhs ∈ lhsTerms d := by
    simp only [lhsTerms, List.mem_append, List.mem_map]
    exact .inl ⟨r, hm, rfl⟩
  have hreqm : ∀ t, r.req = some t → t ∈ rhsTerms d := fun t ht => by
    simp only [rhsTerms, List.mem_append, List.mem_flatMap]
    exact .inl ⟨r, hm, by simp [ht]⟩
  have hrhsm : r.rhs ∈ rhsTerms d := by
    simp only [rhsTerms, List.mem_append, List.mem_flatMap]
    exact .inl ⟨r, hm, by simp⟩
  have hensm : ∀ e, r.ens = some e → e ∈ ensTerms d := fun e he => by
    simp only [ensTerms, List.mem_append]
    exact .inl (List.mem_filterMap.mpr ⟨r, hm, he⟩)
  have hc' := hc
  simp only [encodable, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, h8⟩, h10⟩, h11⟩, -⟩, -⟩ := hc'
  simp only [colPatsOK, List.all_eq_true] at h8
  simp only [asOK, List.all_eq_true] at h10
  simp only [ensOK, List.all_eq_true, Bool.and_eq_true] at h11
  have hle : encTerm d r.lhs = some (encT d r.lhs) := encTerm_of_encodable hc (by simp [hl])
  refine ⟨hle, ?_, fun t ht => ⟨?_, h10 t (hreqm t ht)⟩,
    encTerm_of_encodable hc (by simp [hrhsm]), h10 _ hrhsm,
    fun e he => ⟨encTerm_of_encodable hc (by simp [hensm e he]), (h11 e (hensm e he)).2⟩⟩
  · have := h8 _ hl
    rw [hle] at this
    exact this
  · simp only [encReq, ht]
    exact encTerm_of_encodable hc (by simp [hreqm t ht])

/-- The left side of a rule binds every variable. -/
theorem ruleBinds_krw (hc : encodable d = true) {r : Rule} (hm : r ∈ d.rules) :
    binds r.vars.length (varOccs r.lhs) = true :=
  (ruleShape_krw hc hm).2.2.2

/-- A rule's variables have sorts other than `Float`: each is a variable of the left side. -/
theorem ruleVarsNF_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) : VarsNF_ksc r.vars :=
  fun i hi => rule_patVar_sort_kpv hr hc hm (Exec.binds_all (ruleBinds_krw hc hm) i hi)

/-- The instance of a rule's `requires` has a value where the binding has an entry for every
variable of the rule. -/
theorem ruleReqInst_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) {B : Bind} (hB : Covers_ksm B (List.range r.vars.length)) :
    ∃ t, instF (encRl d r).req B = some t := by
  obtain ⟨L, -, -, hreq, -⟩ := ruleTerms_krw hr hc hm
  obtain ⟨-, -, he, -⟩ := ruleEnc_krw hc hm
  cases hq : r.req with
  | none => exact ⟨.bv true, by show instF (encReq d r.req) B = _; rw [hq]; rfl⟩
  | some tq =>
    obtain ⟨h1, h2⟩ := he tq hq
    have h1' : encTerm d tq = some (encRl d r).req := h1
    exact Option.isSome_iff_exists.mp (instF_isSome_ksc h1' h2 fun i hi =>
      hB i (List.mem_range.mpr (Faithful.varOccs_lt tq (hreq tq hq) i hi)))

/-- The instance of a rule's right side with its ensures has a value where the binding has an
entry for every variable of the rule. -/
theorem ruleRhsInst_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) {B : Bind} (hB : Covers_ksm B (List.range r.vars.length)) :
    ∃ t, instF (encRl d r).rhs B = some t := by
  obtain ⟨L, -, hrhs, -, hens⟩ := ruleTerms_krw hr hc hm
  obtain ⟨-, -, -, h1, h2, he⟩ := ruleEnc_krw hc hm
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (instF_isSome_ksc h1 h2 fun i hi =>
    hB i (List.mem_range.mpr (Faithful.varOccs_lt r.rhs hrhs i hi)))
  cases hq : r.ens with
  | none =>
    refine ⟨u, ?_⟩
    show instF (encRhs d r.rhs r.ens) B = some u
    rw [hq]; exact hu
  | some e =>
    obtain ⟨g1, g2⟩ := he e hq
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (instF_isSome_ksc g1 g2 fun i hi =>
      hB i (List.mem_range.mpr (Faithful.varOccs_lt e (hens e hq) i hi)))
    refine ⟨.en u w, ?_⟩
    show instF (encRhs d r.rhs r.ens) B = some (.en u w)
    rw [hq, encRhs, instF, hu, hw]; rfl

variable {E : D}

/-- `reqEval_spec_ksc` at a rule of `d`. -/
theorem ruleReqEval_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) {B : Bind} {t : T} (ht : instF (encRl d r).req B = some t) {σ₀ : Subst}
    (hB₀ : BindAgree B σ₀) (hσ₀ : (d₀ d).WellSorted r.vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ (r.req = none → u = .bv true) ∧
      ∀ tq, r.req = some tq → ∀ σ, BindAgree B σ → (d₀ d).WellSorted r.vars σ →
        ∃ o, u = encR o ∧ EvalTerm (d₀ d) σ tq o := by
  obtain ⟨L, hL, -, hreq, -⟩ := ruleTerms_krw hr hc hm
  obtain ⟨-, -, he, -⟩ := ruleEnc_krw hc hm
  exact reqEval_spec_ksc hc hL hreq (fun t h => (he t h).1) (ruleVarsNF_krw hr hc hm) ht hB₀ hσ₀ hq

/-- `rhsEval_spec_ksc` at a rule of `d`. -/
theorem ruleRhsEval_krw (hr : CExec.execReady d = true) (hc : encodable d = true) {r : Rule}
    (hm : r ∈ d.rules) {B : Bind} {t : T} (ht : instF (encRl d r).rhs B = some t) {σ₀ : Subst}
    (hB₀ : BindAgree B σ₀) (hσ₀ : (d₀ d).WellSorted r.vars σ₀) {q : Option GroundTerm}
    (hq : Called d E 464 [embD E, emb t] q) :
    ∃ u, q = some (emb u) ∧ ∀ σ, BindAgree B σ → (d₀ d).WellSorted r.vars σ →
      ∃ o, EvalTerm (d₀ d) σ r.rhs o ∧
        ((r.ens = none ∧ u = encR o) ∨
          ∃ e w, r.ens = some e ∧ EvalTerm (d₀ d) σ e w ∧ u = ensureF (encR w) (encR o)) := by
  obtain ⟨L, hL, hrhs, -, hens⟩ := ruleTerms_krw hr hc hm
  obtain ⟨-, -, -, h1, -, he⟩ := ruleEnc_krw hc hm
  exact rhsEval_spec_ksc hc hL hrhs hens h1 (fun e h => (he e h).1) (ruleVarsNF_krw hr hc hm)
    ht hB₀ hσ₀ hq

end Rules

/-! ## What the walk lists -/

section Fired
variable (d : Semantics)

/-- **A result kore.k lists for the rule `r` under `σ` at `x`**: `σ` is a well-sorted match of
the left side whose `requires` is true, and `u` is the encoding of the right side's result, or
`ensure` of the ensures' result and the right side's. -/
def FiredBy_krw (r : Rule) (σ : Subst) (x : GroundTerm) (u : T) : Prop :=
  (d₀ d).WellSorted r.vars σ ∧ PatVal (d₀ d) σ r.lhs x ∧
  (∀ t, r.req = some t → EvalTerm (d₀ d) σ t (some (bool true))) ∧
  ∃ o, EvalTerm (d₀ d) σ r.rhs o ∧
    ((r.ens = none ∧ u = encR o) ∨
     ∃ e w, r.ens = some e ∧ EvalTerm (d₀ d) σ e w ∧ u = ensureF (encR w) (encR o))

/-- **What the walk has shown at the priority `p`**: no rule of a smaller priority applies (at
`noP`: no rule). -/
def RuleBelow_krw (x : GroundTerm) (p : Option Int) : Prop :=
  ∀ r ∈ d.rules, (∀ P, p = some P → (r.prio : Int) < P) → NotApplies (d₀ d) r x

/-- **What the rules `rs` of the priority `P` give at `x`**: each member of `us` is a result of
one of them under a match, and each match of each of them fails its `requires` or has its result
in `us`. -/
def FiredAt_krw (x : GroundTerm) (rs : List Rule) (P : Int) (us : List T) : Prop :=
  (∀ u ∈ us, ∃ r ∈ rs, (r.prio : Int) = P ∧ ∃ σ, FiredBy_krw d r σ x u) ∧
  (∀ r ∈ rs, (r.prio : Int) = P → ∀ σ, (d₀ d).WellSorted r.vars σ → PatVal (d₀ d) σ r.lhs x →
    RuleReqFails (d₀ d) σ r ∨ ∃ u ∈ us, FiredBy_krw d r σ x u)

/-- What `rule_walk` concludes of the result `res` of the walk at `x`. -/
def WalkRes_krw (x : GroundTerm) (res : Option GroundTerm) : Prop :=
  (res = some (embSt .stuck) ∧ ∀ r ∈ d.rules, NotApplies (d₀ d) r x) ∨
  ∃ (P : Int) (us : List T), res = some (embSt (.next (dropF .bot us))) ∧ us ≠ [] ∧
    RuleBelow_krw d x (some P) ∧ FiredAt_krw d x d.rules P us

end Fired

section FiredLemmas
variable {d : Semantics}

theorem FiredAt_krw.nil {x : GroundTerm} {P : Int} : FiredAt_krw d x [] P [] :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- The rules of a priority, one at a time: the lists of a rule and of the rules after it. -/
theorem FiredAt_krw.cons {x : GroundTerm} {r : Rule} {rs : List Rule} {P : Int} {us₁ us₂ : List T}
    (h₁ : FiredAt_krw d x [r] P us₁) (h₂ : FiredAt_krw d x rs P us₂) :
    FiredAt_krw d x (r :: rs) P (us₁ ++ us₂) := by
  refine ⟨fun u hu => ?_, fun r' hr' hp σ hσ hx => ?_⟩
  · rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨r', hr', hp, hf⟩ := h₁.1 u hu
      exact ⟨r', by simp at hr'; simp [hr'], hp, hf⟩
    · obtain ⟨r', hr', hp, hf⟩ := h₂.1 u hu
      exact ⟨r', List.mem_cons_of_mem _ hr', hp, hf⟩
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · rcases h₁.2 r' (List.mem_cons_self ..) hp σ hσ hx with h | ⟨u, hu, hf⟩
      · exact .inl h
      · exact .inr ⟨u, List.mem_append_left _ hu, hf⟩
    · rcases h₂.2 r' hr' hp σ hσ hx with h | ⟨u, hu, hf⟩
      · exact .inl h
      · exact .inr ⟨u, List.mem_append_right _ hu, hf⟩

/-- A rule of another priority: the list of the rules after it. -/
theorem FiredAt_krw.skip {x : GroundTerm} {r : Rule} {rs : List Rule} {P : Int} {us : List T}
    (hp : (r.prio : Int) ≠ P) (h : FiredAt_krw d x rs P us) : FiredAt_krw d x (r :: rs) P us := by
  refine ⟨fun u hu => ?_, fun r' hr' hp' σ hσ hx => ?_⟩
  · obtain ⟨r', hr', hp, hf⟩ := h.1 u hu
    exact ⟨r', List.mem_cons_of_mem _ hr', hp, hf⟩
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · exact absurd hp' hp
    · exact h.2 r' hr' hp' σ hσ hx

/-- **No listed result: no rule of the priority applies.** -/
theorem firedAt_nil_krw {E : D} (hE : encDef d = some E) {x : GroundTerm} {P : Int}
    (h : FiredAt_krw d x d.rules P []) :
    ∀ r ∈ d.rules, (r.prio : Int) = P → NotApplies (d₀ d) r x := fun r hm hp =>
  NotApplies.of_wellSorted (ruleBinds_krw (encodable_of_encDef_ksc hE) hm) fun σ hσ hx => by
    rcases h.2 r hm hp σ hσ hx with h | ⟨u, hu, -⟩
    · exact h
    · exact (nomatch hu)

/-- **A listed result: a rule of the priority applies.** -/
theorem firedAt_applies_krw {E : D} (hE : encDef d = some E) {x : GroundTerm} {P : Int} {us : List T}
    (h : FiredAt_krw d x d.rules P us) (hne : us ≠ []) :
    ∃ r ∈ d.rules, (r.prio : Int) = P ∧ RuleApplies (d₀ d) r x := by
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil us hne
  obtain ⟨r, hm, hp, σ, hσ, hx, hreq, -⟩ := h.1 u hu
  have hpre := (ruleShape_krw (encodable_of_encDef_ksc hE) hm).2.1
  exact ⟨r, hm, hp, σ, hσ.at _, hx, hreq, by rw [hpre]; exact .top⟩

/-- **A listed result other than `bot` is a step** of `d₀ d` from `x`, where no rule below the
rule's priority applies. -/
theorem firedBy_step_krw {E : D} (hr : CExec.execReady d = true) (hE : encDef d = some E)
    {x : Config (d₀ d)} {r : Rule} (hm : r ∈ d.rules) {σ : Subst} {u : T}
    (hf : FiredBy_krw d r σ x.val u) (hu : u ≠ .bot)
    (hb : RuleBelow_krw d x.val (some (r.prio : Int))) :
    ∃ y : Config (d₀ d), enc y.val = u ∧ Step (d₀ d) x y := by
  have hc := encodable_of_encDef_ksc hE
  obtain ⟨hσ, hx, hreq, o, ho, hens⟩ := hf
  obtain ⟨hex, hpre, hpost, -⟩ := ruleShape_krw hc hm
  obtain ⟨L, hL, hrs, -, -⟩ := ruleTerms_krw hr hc hm
  -- the right side's result is a value, and the ensures (if any) is true
  obtain ⟨v, rfl, hu', hens'⟩ : ∃ v, o = some v ∧ enc v = u ∧
      ∀ t, r.ens = some t → EvalTerm (d₀ d) σ t (some (bool true)) := by
    rcases hens with ⟨hn, rfl⟩ | ⟨e, w, he, hew, rfl⟩
    · cases o with
      | none => exact absurd rfl hu
      | some v => exact ⟨v, rfl, rfl, fun t ht => by rw [hn] at ht; cases ht⟩
    · have hw : encR w = .bv true := by
        by_cases hne : encR w = .bv true
        · exact hne
        · exact absurd (by unfold ensureF; rw [if_neg hne]) hu
      have hw' := encR_eq_bv_ksc hw
      subst hw'
      have e1 : ensureF (encR (some (bool true))) (encR o) = encR o := by
        unfold ensureF; rw [if_pos hw]
      rw [e1] at hu ⊢
      cases o with
      | none => exact absurd rfl hu
      | some v => exact ⟨v, rfl, rfl, fun t ht => by rw [he] at ht; cases ht; exact hew⟩
  have hsort : (d₀ d).sortOf v = some topCellSort :=
    EvalTerm.sorted (sortCtx_kst hr hc) ho hL hσ hrs rfl
  refine ⟨⟨v, hsort⟩, hu', Step.rule_top r hm σ hpre hpost hσ hx hreq ho hens' fun r' hr' hlt => ?_⟩
  exact hb r' hr' fun P e => by cases e; exact Int.ofNat_lt.mpr hlt

/-- An encoded rule's priority is its own. -/
theorem rprio_encRl_krw (d : Semantics) (r : Rule) :
    rprioF (encRl d r).prio (encRl d r).owise = (r.prio : Int) := rfl

/-- **At the walk's first priority no rule is below.** -/
theorem ruleBelow_first_krw (x : GroundTerm) :
    RuleBelow_krw d x (nextRlF (d.rules.map (encRl d)) none) := by
  intro r hr hlt
  have hm : encRl d r ∈ d.rules.map (encRl d) := List.mem_map_of_mem hr
  obtain ⟨h1, h2⟩ := nextRlF_spec_ksc none (d.rules.map (encRl d))
  cases hq : nextRlF (d.rules.map (encRl d)) none with
  | none => exact absurd trivial (h1 hq _ hm)
  | some q =>
    have hl := hlt q hq
    have := (h2 q hq).2.2 _ hm trivial
    rw [rprio_encRl_krw] at this
    exact absurd hl (Int.not_lt.mpr this)

/-- **`step-next`**: where no rule below `P` and no rule at `P` applies, no rule below the next
priority applies. -/
theorem ruleBelow_next_krw {x : GroundTerm} {P : Int} (hb : RuleBelow_krw d x (some P))
    (hP : ∀ r ∈ d.rules, (r.prio : Int) = P → NotApplies (d₀ d) r x) :
    RuleBelow_krw d x (nextRlF (d.rules.map (encRl d)) (some P)) := by
  intro r hr hlt
  by_cases h1 : (r.prio : Int) < P
  · exact hb r hr fun P' e => by cases e; exact h1
  by_cases h2 : (r.prio : Int) = P
  · exact hP r hr h2
  have ha : Above_ksc (rprioF (encRl d r).prio (encRl d r).owise) (some P) := by
    show P < (r.prio : Int); omega
  have hm : encRl d r ∈ d.rules.map (encRl d) := List.mem_map_of_mem hr
  obtain ⟨g1, g2⟩ := nextRlF_spec_ksc (some P) (d.rules.map (encRl d))
  cases hq : nextRlF (d.rules.map (encRl d)) (some P) with
  | none => exact absurd ha (g1 hq _ hm)
  | some q =>
    have hl := hlt q hq
    have := (g2 q hq).2.2 _ hm ha
    rw [rprio_encRl_krw] at this
    exact absurd hl (Int.not_lt.mpr this)

theorem encDef_rules_krw {E : D} (hE : encDef d = some E) : E.rules = d.rules.map (encRl d) := by
  unfold encDef at hE
  split at hE
  · cases hE; rfl
  · cases hE

end FiredLemmas

/-! ## The rules of a priority: `fireM`, `fire`, `fireAt` -/

section Fire
open _root_.KK
variable {d : Semantics} {E : D}

/-- **`fireM` at the matches of a rule's left side**, each a binding with an entry for every
variable that agrees with a well-sorted substitution under which the left side denotes `x`: the
list of the results of the matches whose `requires` is true, and every substitution such a binding
agrees with fails the `requires` or has its result listed. -/
theorem fireM_spec_krw (hr : CExec.execReady d = true) (hE : encDef d = some E) {ru : Rule}
    (hm : ru ∈ d.rules) {x : GroundTerm} (ms : Ms) : ∀ {res : Option GroundTerm},
    Eval c₀ 470 [embD E, emb (encRl d ru).req, emb (encRl d ru).rhs, embMs ms] res →
    (∀ B ∈ ms, Covers_ksm B (List.range ru.vars.length) ∧
      ∃ σ, BindAgree B σ ∧ (d₀ d).WellSorted ru.vars σ ∧ PatVal (d₀ d) σ ru.lhs x) →
    ∃ us, res = some (embTs us) ∧ (∀ u ∈ us, ∃ σ, FiredBy_krw d ru σ x u) ∧
      ∀ B ∈ ms, ∀ σ, BindAgree B σ → (d₀ d).WellSorted ru.vars σ → PatVal (d₀ d) σ ru.lhs x →
        RuleReqFails (d₀ d) σ ru ∨ ∃ u ∈ us, FiredBy_krw d ru σ x u := by
  have hc := encodable_of_encDef_ksc hE
  induction ms with
  | nil =>
    intro res h _
    rcases fireM_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h) with
      ⟨-, hr'⟩ | ⟨B, ms', he, -⟩
    · exact ⟨[], hr', fun u hu => (nomatch hu), fun B hB => (nomatch hB)⟩
    · cases he
  | cons B ms' ih =>
    intro res h hms
    rcases fireM_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h) with
      ⟨he, -⟩ | ⟨B', ms'', he, hcase⟩
    · cases he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    obtain ⟨hcov, σ₀, hB₀, hσ₀, hp₀⟩ := hms B (List.mem_cons_self ..)
    have hms' := fun B' (hB' : B' ∈ ms') => hms B' (List.mem_cons_of_mem _ hB')
    obtain ⟨t, ht⟩ := ruleReqInst_krw hr hc hm hcov
    rcases hcase t ht with ⟨q, hq, heq, q', q'', hq'', hres, hrhs⟩ | ⟨q, hq, hne, hR⟩ |
        ⟨q, q', hq, hq', h1, h2⟩
    · -- `fire-holds`
      obtain ⟨u, rfl, -, hall⟩ := ruleReqEval_krw hr hc hm ht hB₀ hσ₀ ⟨hq, spec_all hr hE hq⟩
      have hu := heq u rfl
      rcases hrhs with ⟨hn, -⟩ | ⟨t', ht', hq'⟩
      · obtain ⟨t', ht'⟩ := ruleRhsInst_krw hr hc hm hcov
        rw [ht'] at hn; cases hn
      obtain ⟨u', rfl, hall'⟩ := ruleRhsEval_krw hr hc hm ht' hB₀ hσ₀ ⟨hq', spec_all hr hE hq'⟩
      obtain ⟨us, rfl, hf, hn⟩ := ih hq'' hms'
      have fired : ∀ σ, BindAgree B σ → (d₀ d).WellSorted ru.vars σ → PatVal (d₀ d) σ ru.lhs x →
          FiredBy_krw d ru σ x u' := fun σ hBσ hσ hp => by
        obtain ⟨o, ho, hens⟩ := hall' σ hBσ hσ
        refine ⟨hσ, hp, fun tq hrq => ?_, o, ho, hens⟩
        obtain ⟨o', ho', he'⟩ := hall tq hrq σ hBσ hσ
        rw [hu] at ho'
        rw [encR_eq_bv_ksc ho'.symm] at he'
        exact he'
      refine ⟨u' :: us, by rw [hres]; rfl, fun v hv => ?_, fun B' hB' σ hBσ hσ hp => ?_⟩
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨σ₀, fired σ₀ hB₀ hσ₀ hp₀⟩
        · exact hf v hv
      · rcases List.mem_cons.mp hB' with rfl | hB'
        · exact .inr ⟨_, List.mem_cons_self .., fired σ hBσ hσ hp⟩
        · rcases hn B' hB' σ hBσ hσ hp with h | ⟨v, hv, hfv⟩
          · exact .inl h
          · exact .inr ⟨v, List.mem_cons_of_mem _ hv, hfv⟩
    · -- `fire-refuted`
      obtain ⟨u, rfl, hnone, hall⟩ := ruleReqEval_krw hr hc hm ht hB₀ hσ₀ ⟨hq, spec_all hr hE hq⟩
      have hu := hne u rfl
      obtain ⟨us, rfl, hf, hn⟩ := ih hR hms'
      refine ⟨us, rfl, hf, fun B' hB' σ hBσ hσ hp => ?_⟩
      rcases List.mem_cons.mp hB' with rfl | hB'
      · cases hrq : ru.req with
        | none => exact absurd (hnone hrq) hu
        | some tq =>
          obtain ⟨o, rfl, ho⟩ := hall tq hrq σ hBσ hσ
          exact .inl (.intro hrq ho fun e => hu (by rw [e]; rfl))
      · exact hn B' hB' σ hBσ hσ hp
    · -- neither: one call of `eval`, one value
      obtain ⟨u, rfl, -, -⟩ := ruleReqEval_krw hr hc hm ht hB₀ hσ₀ ⟨hq, spec_all hr hE hq⟩
      have e : q' = some (emb u) := (evalF_iff hq).mp hq'
      exact absurd (h1 u rfl) (h2 u e)

/-- **`fire` at a rule and a configuration**: the list of the rule's results at `x`, as
`FiredAt_krw` at the rule alone. -/
theorem fire_spec_krw (hr : CExec.execReady d = true) (hE : encDef d = some E) {ru : Rule}
    (hm : ru ∈ d.rules) {x : GroundTerm} (hx : (d₀ d).sortOf x = some topCellSort)
    {res : Option GroundTerm}
    (h : Eval c₀ 468 [embD E, emb (encRl d ru).lhs, emb (encRl d ru).req, emb (encRl d ru).rhs,
      emb (enc x)] res) :
    ∃ us, res = some (embTs us) ∧ FiredAt_krw d x [ru] (ru.prio : Int) us := by
  have hc := encodable_of_encDef_ksc hE
  obtain ⟨hmc, hov⟩ := matchCtx_d₀ hr hc
  have hcs : Faithful.collsOK (d₀ d) = true := (encodable_colls_c13 hc).1
  obtain ⟨hle, hcp, -⟩ := ruleEnc_krw hc hm
  have hq : encTerm (d₀ d) ru.lhs = some (encRl d ru).lhs := by rw [encTerm_d₀]; exact hle
  have hp := rulePat_d₀ hr hc (show ru ∈ (d₀ d).rules from hm)
  have hbinds := ruleBinds_krw hc hm
  have hlv : litsV x = true := litsV_kst hr hc hx (by decide)
  have hsubs : E.subs = subsF (d₀ d) := (encDef_subs hE).trans (subsF_d₀ d).symm
  rcases fire_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h) with
    ⟨M, hM, hR⟩ | ⟨hM, -⟩
  · rw [hsubs] at hM
    have hprem : ∀ B ∈ M, Covers_ksm B (List.range ru.vars.length) ∧
        ∃ σ, BindAgree B σ ∧ (d₀ d).WellSorted ru.vars σ ∧ PatVal (d₀ d) σ ru.lhs x :=
      fun B hB => by
        obtain ⟨-, hcov, -, -⟩ := matchF_col_sound hmc hov hcs hq hp hx hlv hM hB
        obtain ⟨σ, hrep, hσ, hpv⟩ := matchF_col_wellSorted hmc hov hcs hq hp hx hlv hbinds hM hB
        exact ⟨fun i hi => hcov i (Exec.binds_all hbinds i (List.mem_range.mp hi)), σ,
          bindAgree_of_rep_ksc hrep, hσ, hpv⟩
    obtain ⟨us, hus, hf, hn⟩ := fireM_spec_krw hr hE hm M hR hprem
    refine ⟨us, hus, fun u hu => ⟨ru, List.mem_cons_self .., rfl, hf u hu⟩,
      fun r' hr' _ σ hσ hpv => ?_⟩
    rw [List.mem_singleton] at hr'
    subst hr'
    obtain ⟨M', hM', B', hB', hagree, -⟩ :=
      matchF_col_complete hmc hov hcs hσ hq hcp hp hlv hpv (bindAgree_nil σ)
    rw [hM] at hM'
    cases hM'
    exact hn B' hB' σ hagree hσ hpv
  · rw [hsubs] at hM
    have := matchF_total hov hq hp hx (subsF (d₀ d)) []
    rw [hM] at this
    cases this

/-- **`fireAt` at rules `suf` of `d`, a configuration and a priority**: the list of the results
of the rules of `suf` at that priority, as `FiredAt_krw`. -/
theorem fireAt_spec_krw (hr : CExec.execReady d = true) (hE : encDef d = some E) {x : GroundTerm}
    (hx : (d₀ d).sortOf x = some topCellSort) (P : Int) : ∀ (suf : List Rule)
    {res : Option GroundTerm}, (∀ ru ∈ suf, ru ∈ d.rules) →
    Eval c₀ 469 [embD E, embRls (suf.map (encRl d)), emb (enc x), .dv 3 (.int P)] res →
    ∃ us, res = some (embTs us) ∧ FiredAt_krw d x suf P us
  | [], res, _, h => by
    rcases fireAt_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h) with
      ⟨-, hr'⟩ | ⟨c, rs', he, -⟩
    · exact ⟨[], hr', FiredAt_krw.nil⟩
    · cases he
  | ru :: suf, res, hs, h => by
    have hm := hs ru (List.mem_cons_self ..)
    have hs' : ∀ r ∈ suf, r ∈ d.rules := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    rcases fireAt_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h) with
      ⟨he, -⟩ | ⟨c, rs', he, hcase⟩
    · cases he
    rw [List.map_cons] at he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    rcases hcase with ⟨hP, q₁, q₂, h₁, h₂, happ⟩ | ⟨hP, hR⟩
    · have hP' : (ru.prio : Int) = P := hP
      obtain ⟨us₁, rfl, hf₁⟩ := fire_spec_krw hr hE hm hx h₁
      obtain ⟨us₂, rfl, hf₂⟩ := fireAt_spec_krw hr hE hx P suf hs' h₂
      exact ⟨us₁ ++ us₂, happ us₁ us₂ rfl rfl, FiredAt_krw.cons (by rw [← hP']; exact hf₁) hf₂⟩
    · obtain ⟨us, rfl, hf⟩ := fireAt_spec_krw hr hE hx P suf hs' hR
      exact ⟨us, rfl, FiredAt_krw.skip hP hf⟩

end Fire

/-! ## The priorities: `stepAt` and `stepIf` -/

section Steps
open _root_.KK

/-- `stepAt(D, Rs, T, P)` at `d`'s rules, a configuration and a priority below which no rule
applies: what `rule_walk` concludes. -/
def SpecStepAt_krw (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (x : GroundTerm) (p : Option Int),
    vs = [embD E, embRls (d.rules.map (encRl d)), emb (enc x), embPrio p] →
    (d₀ d).sortOf x = some topCellSort → RuleBelow_krw d x p → WalkRes_krw d x r

/-- `stepIf(D, Rs, T, P, Us)` at what `fireAt` gave at `P`: what `rule_walk` concludes. -/
def SpecStepIf_krw (d : Semantics) (E : D) (vs : List GroundTerm) (r : Option GroundTerm) : Prop :=
  ∀ (x : GroundTerm) (P : Int) (us : List T),
    vs = [embD E, embRls (d.rules.map (encRl d)), emb (enc x), .dv 3 (.int P), embTs us] →
    (d₀ d).sortOf x = some topCellSort → RuleBelow_krw d x (some P) →
    FiredAt_krw d x d.rules P us → WalkRes_krw d x r

/-- **The motive of the walk of the priorities**: `stepAt`'s and `stepIf`'s clauses, `True` at
every other function. -/
def RSpec_krw (d : Semantics) (E : D) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) :
    Prop :=
  if f = 506 then SpecStepAt_krw d E vs r
  else if f = 507 then SpecStepIf_krw d E vs r
  else True

section
variable {d : Semantics} {E : D} {vs : List GroundTerm} {r : Option GroundTerm}

theorem RSpec_stepAt_krw : RSpec_krw d E 506 vs r ↔ SpecStepAt_krw d E vs r := by
  unfold RSpec_krw; rw [if_pos rfl]
theorem RSpec_stepIf_krw : RSpec_krw d E 507 vs r ↔ SpecStepIf_krw d E vs r := by
  unfold RSpec_krw; rw [if_neg (by decide), if_pos rfl]

/-- The calls of a step: evaluations of kore.k of which `RSpec_krw` holds. -/
abbrev RCalled_krw (d : Semantics) (E : D) : CallRel :=
  fun g ws q => Eval c₀ g ws q ∧ RSpec_krw d E g ws q

/-- **The step case at `stepAt`.** -/
theorem rstep_stepAt_krw (hr : CExec.execReady d = true) (hE : encDef d = some E)
    (hb : ByClause c₀ (RCalled_krw d E) 506 vs r) : SpecStepAt_krw d E vs r := by
  intro x p hvs hx hbelow
  subst hvs
  rcases stepAt_inv_krw hb with ⟨rfl, hr'⟩ | ⟨P, rfl, q, hq, hcase⟩
  · exact .inl ⟨hr', fun ru hm => hbelow ru hm fun P h => (nomatch h)⟩
  · obtain ⟨us, rfl, hf⟩ := fireAt_spec_krw hr hE hx P d.rules (fun _ h => h) hq.1
    rcases hcase with ⟨y, hy, hR⟩ | ⟨hn, -⟩
    · cases hy
      exact RSpec_stepIf_krw.mp hR.2 x P us rfl hx hbelow hf
    · cases hn

/-- **The step case at `stepIf`.** -/
theorem rstep_stepIf_krw (hE : encDef d = some E) (hb : ByClause c₀ (RCalled_krw d E) 507 vs r) :
    SpecStepIf_krw d E vs r := by
  intro x P us hvs hx hbelow hf
  subst hvs
  rcases stepIf_inv_krw (fun _ _ _ h => h.1) hb with ⟨rfl, hR⟩ | ⟨hne, hr'⟩
  · exact RSpec_stepAt_krw.mp hR.2 x _ rfl hx (ruleBelow_next_krw hbelow (firedAt_nil_krw hE hf))
  · exact .inr ⟨P, us, hr', hne, hbelow, hf⟩

/-- **`RSpec_krw` holds of every evaluation of kore.k**: the instance of `Eval.calls_induct` at
`K₀ sig` and `RSpec_krw d E`. -/
theorem rspec_of_steps_krw (hr : CExec.execReady d = true) (hE : encDef d = some E) {f : Sym}
    {vs : List GroundTerm} {r : Option GroundTerm} (h : Eval c₀ f vs r) : RSpec_krw d E f vs r :=
  Eval.calls_induct (c := c₀) (P := RSpec_krw d E) (fun f vs r hb => by
    by_cases h506 : f = 506
    · subst h506; exact RSpec_stepAt_krw.mpr (rstep_stepAt_krw hr hE hb)
    by_cases h507 : f = 507
    · subst h507; exact RSpec_stepIf_krw.mpr (rstep_stepIf_krw hE hb)
    unfold RSpec_krw
    rw [if_neg h506, if_neg h507]
    trivial) h

end

end Steps

/-! ## The rule walk -/

section Walk
open _root_.KK
variable {d : Semantics} {E : D}

/-- **The rule walk.** kore.k's `succs` at a configuration `x` of the top cell sort has the result
`stuck`, and no rule applies at `x`; or it has the result `next` of the list `us` without `bot`,
where `us` is not empty and is the list of the results of the rules of a priority `P` at `x`
(`FiredAt_krw`), and no rule below `P` applies. -/
theorem rule_walk (hr : CExec.execReady d = true) (hE : encDef d = some E) {x : GroundTerm}
    (hx : (d₀ d).sortOf x = some topCellSort) {res : Option GroundTerm}
    (h : Eval (K₀ sig) sig.succs [embD E, emb (enc x)] res) :
    (res = some (embSt .stuck) ∧ ∀ r ∈ d.rules, NotApplies (d₀ d) r x) ∨
    ∃ (P : Int) (us : List T), res = some (embSt (.next (dropF .bot us))) ∧ us ≠ [] ∧
      RuleBelow_krw d x (some P) ∧ FiredAt_krw d x d.rules P us := by
  have hR := succs_inv_krw (R := Eval c₀) (fun _ _ _ h => h) (Eval.byClause_iff.mp h)
  rw [encDef_rules_krw hE] at hR
  exact RSpec_stepAt_krw.mp (rspec_of_steps_krw hr hE hR) x _ rfl hx (ruleBelow_first_krw x)

end Walk

/-! ## Instances -/

section Instances
open KCore.Det _root_.KK _root_.KK.Kit _root_.KK.Facts Terms

/-- **`stepAt` at `noP` is `stuck`**, at any definition, rules and term (`step-none`). -/
theorem stepAt_noP_eval_krw (E : D) (rs : List Rl) (t : T) :
    Eval c₀ 506 [embD E, embRls rs, emb t, embPrio none] (some (embSt .stuck)) :=
  clause_kht WalkR.stepAtDef_lookup_krw (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (ws_enum (vars := [45, 42, 33]) (.cons (embD_sorted_c₀ E) (.cons (embRls_sorted_c₀ rs)
      (.cons (emb_sorted_c₀ t) .nil))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_431 .nil) .nil))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil)

/-- `stepAt_inv_krw` at `stepAt_noP_eval_krw`'s evaluation: the `noP` disjunct. -/
example (E : D) (rs : List Rl) (t : T) : True := by
  rcases stepAt_inv_krw (R := Eval c₀) (Eval.byClause_iff.mp (stepAt_noP_eval_krw E rs t)) with
    ⟨-, -⟩ | ⟨P, h, -⟩
  · trivial
  · cases h

/-- **`fireM` at `.Ms` is `.Ts`** (`fire-nomatch`). -/
theorem fireM_nil_eval_krw (E : D) (req rhs : T) :
    Eval c₀ 470 [embD E, emb req, emb rhs, embMs []] (some (embTs [])) :=
  clause_kht WalkR.fireMDef_lookup_krw (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))
    (ws_enum (vars := [45, 33, 33]) (.cons (embD_sorted_c₀ E) (.cons (emb_sorted_c₀ req)
      (.cons (emb_sorted_c₀ rhs) .nil))))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.ctor ctor_403 .nil) .nil))))
    (fun _ h => by cases h) (by decide) ⟨rfl, rfl, rfl, rfl⟩ (ev_ctor .nil)

/-- `fireM_inv_krw` at `fireM_nil_eval_krw`'s evaluation: the `.Ms` disjunct. -/
example (E : D) (req rhs : T) : True := by
  rcases fireM_inv_krw (R := Eval c₀) (fun _ _ _ h => h)
    (Eval.byClause_iff.mp (fireM_nil_eval_krw E req rhs)) with ⟨-, -⟩ | ⟨B, ms', h, -⟩
  · trivial
  · cases h

/-- `appF_eq_krw` at two lists of one term each. -/
example : Gen.appF [.iv 1] [.bv true] = some [.iv 1, .bv true] := appF_eq_krw _ _

/-- `rprio_encRl_krw`: an encoded rule's priority. -/
example (d : Semantics) : rprioF (encRl d ⟨[], .var 0, none, .var 0, none, 7, [], .top, .top⟩).prio
    false = 7 := rprio_encRl_krw d _

end Instances

/-! ## Checks -/

#check @rule_walk
#check @firedBy_step_krw
#check @firedAt_applies_krw
#check @firedAt_nil_krw
#check @FiredBy_krw
#check @RuleBelow_krw
#check @FiredAt_krw

open Lean in
#eval show CoreM Unit from do
  for n in [``WalkR.succsDef_lookup_krw, ``WalkR.stepAtDef_lookup_krw, ``WalkR.stepIfDef_lookup_krw,
      ``WalkR.fireAtDef_lookup_krw, ``WalkR.fireDef_lookup_krw, ``WalkR.fireMDef_lookup_krw,
      ``WalkR.walk_names_krw, ``appF_eq_krw, ``succs_inv_krw, ``stepAt_inv_krw, ``stepIf_inv_krw,
      ``rprioCmp_eval_krw, ``fireAt_inv_krw, ``fire_inv_krw, ``fireM_inv_krw, ``ruleShape_krw,
      ``ruleTerms_krw, ``ruleEnc_krw, ``ruleBinds_krw, ``ruleVarsNF_krw, ``ruleReqInst_krw,
      ``ruleRhsInst_krw, ``ruleReqEval_krw, ``ruleRhsEval_krw, ``FiredAt_krw.cons, ``FiredAt_krw.skip,
      ``firedAt_nil_krw, ``firedAt_applies_krw, ``firedBy_step_krw, ``ruleBelow_first_krw,
      ``ruleBelow_next_krw, ``encDef_rules_krw, ``fireM_spec_krw, ``fire_spec_krw, ``fireAt_spec_krw,
      ``rstep_stepAt_krw, ``rstep_stepIf_krw, ``rspec_of_steps_krw, ``rule_walk,
      ``stepAt_noP_eval_krw, ``fireM_nil_eval_krw] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
