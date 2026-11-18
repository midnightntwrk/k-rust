/-
  One clause of kore.k's `eval` inverted on the package `RefKk`, at the interpretation
  `HookParams.none`: a result of `eval(D, ap(F, As))` is a result of `ev-app`'s right side
  `apply(D, F, evalTs(D, As))` (`eval_app_inv`). Every other clause of `eval` has a pattern of
  another constructor, all are of priority 50, none has an `ensures`, and at `HookParams.none` the
  rest is `none`, which cannot be where `ev-app` applies.
-/
import User.Coherent

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-! ## `eval`'s equations -/

/-- The clause of `eval` from kore.k's rule `ev-app`. -/
def evApp : Clause :=
  { vars := [45, 3, 43],
    pats := [.var 0, .app 408 [.var 1, .var 2]],
    req := none,
    rhs := .app 448 [.var 0, .var 1, .app 467 [.var 0, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-col`. -/
def evCol : Clause :=
  { vars:= [45, 34, 3, 43],
    pats := [.var 0, .app 414 [.var 1, .var 2, .var 3]],
    req := none,
    rhs := .app 459 [.var 1, .var 2, .app 467 [.var 0, .var 3]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-el`. -/
def evEl : Clause :=
  { vars:= [45, 33],
    pats := [.var 0, .app 419 [.var 1]],
    req := none,
    rhs := .app 492 [.app 464 [.var 0, .var 1]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-en`. -/
def evEn : Clause :=
  { vars:= [45, 33, 33],
    pats := [.var 0, .app 420 [.var 1, .var 2]],
    req := none,
    rhs := .app 463 [.app 464 [.var 0, .var 2], .app 464 [.var 0, .var 1]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-hook`. -/
def evHook : Clause :=
  { vars:= [45, 3, 43],
    pats := [.var 0, .app 423 [.var 1, .var 2]],
    req := none,
    rhs := .app 508 [.var 1, .app 467 [.var 0, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-inj`. -/
def evInj : Clause :=
  { vars:= [45, 3, 3, 33],
    pats := [.var 0, .app 424 [.var 1, .var 2, .var 3]],
    req := none,
    rhs := .app 493 [.var 1, .var 2, .app 464 [.var 0, .var 3]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-kv`. -/
def evKv : Clause :=
  { vars:= [45, 33, 33],
    pats := [.var 0, .app 426 [.var 1, .var 2]],
    req := none,
    rhs := .app 494 [.app 464 [.var 0, .var 1], .app 464 [.var 0, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-bool`. -/
def evBool : Clause :=
  { vars:= [45, 2, 33],
    pats := [.var 0, .as (.app 413 [.var 1]) 2],
    req := none,
    rhs := .var 2,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-val`. -/
def evVal : Clause :=
  { vars:= [45, 34, 3, 43, 33],
    pats := [.var 0, .as (.app 416 [.var 1, .var 2, .var 3]) 4],
    req := none,
    rhs := .var 4,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-int`. -/
def evInt : Clause :=
  { vars:= [45, 3, 33],
    pats := [.var 0, .as (.app 425 [.var 1]) 2],
    req := none,
    rhs := .var 2,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `eval` from kore.k's rule `ev-tok`. -/
def evTok : Clause :=
  { vars:= [45, 3, 10, 33],
    pats := [.var 0, .as (.app 443 [.var 1, .var 2]) 3],
    req := none,
    rhs := .var 3,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `eval` (symbol 464) as the definition's semantics holds it. -/
def fnEval : Fn :=
  { label := 464, args := [45, 33], result := 33,
    clauses := [evApp, evCol, evEl, evEn, evHook, evInj, evKv, evBool, evVal, evInt, evTok], total := false }

theorem lookup_eval : c₀.lookupFn 464 = some fnEval := by kernel_rfl

theorem names_eval : c₀.symName 464 = "Lbleval'LParUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Term" ∧
    c₀.symName 408 = "Lblap'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts" ∧
    c₀.symName 448 = "Lblapply'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Term'Unds'Def'Unds'Int'Unds'Ts" ∧
    c₀.symName 467 = "LblevalTs'LParUndsCommUndsRParUnds'KORE'Unds'Ts'Unds'Def'Unds'Ts" := by decide +kernel

/-- A call of a function of the semantics: `apply` or `evalTs`. -/
theorem fn_flags (f : Sym) (hf : f = 448 ∨ f = 467) :
    c₀.isCtor f = false ∧ isHook f = false ∧ c₀.isParam f = false ∧ c₀.isOvl f = false := by
  rcases hf with rfl | rfl <;> decide +kernel

/-- A pattern of a constructor other than `ap` does not denote `ap(F, As)`. -/
theorem not_ap {σ : Subst} {g : Sym} {ps : List Term} {us : List GroundTerm}
    (h : PatVal c₀ σ (.app g ps) (.ctor 408 us)) (hg : g ≠ 408)
    (hc : c₀.isCtor g = true := by decide +kernel) (hp : patternHooks.contains g = false := by decide +kernel) :
    False := by
  obtain ⟨vs, he, -⟩ := pv_ctor h hc hp
  cases he
  exact hg rfl

theorem apply_args {d f : GroundTerm} {rs r : Option GroundTerm} {ws : List GroundTerm}
    (hws : allSome [some d, some f, rs] = some ws) (hA : Eval c₀ 448 ws r) :
    ∃ ys, rs = some ys ∧ Eval c₀ 448 [d, f, ys] r := by
  cases rs with
  | none => simp [allSome] at hws
  | some y =>
    simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hws
    subst hws
    exact ⟨y, rfl, hA⟩

theorem apply_none {d f : GroundTerm} {rs : Option GroundTerm} (hn : allSome [some d, some f, rs] = none) :
    rs = none := by
  cases rs with
  | none => rfl
  | some y => simp [allSome] at hn

/-- **`ev-app` inverted**: where the arguments are of `eval`'s sorts, a result of
`eval(D, ap(F, As))` is `apply(D, F, evalTs(D, As))`'s: `evalTs` has a result there, and the
result is `apply`'s at it, or none where `evalTs` has none. -/
theorem eval_app_inv {d f as : GroundTerm} {r : Option GroundTerm}
    (hsd : c₀.sortOf d = some 45) (hsf : c₀.sortOf f = some 3) (hsa : c₀.sortOf as = some 43)
    (h : Eval c₀ 464 [d, .ctor 408 [f, as]] r) :
    ∃ rs, Eval c₀ 467 [d, as] rs ∧ ((∃ ys, rs = some ys ∧ Eval c₀ 448 [d, f, ys] r) ∨ (rs = none ∧ r = none)) := by
  cases h with
  | clause hfn hmem _ hmatch _ _ _ _ hrhs _ _ =>
    rw [lookup_eval, Option.some.injEq] at hfn
    subst hfn
    simp only [fnEval, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hmatch with _ | ⟨h0, _ | ⟨h1, _ | _⟩⟩
    · -- ev-app: σ gives D, F, As; the right side is `apply(D, F, evalTs(D, As))`
      obtain ⟨xs, he, hxs⟩ := pv_ctor h1
      cases he
      rcases hxs with _ | ⟨hf, _ | ⟨ha, _ | _⟩⟩
      have hd := PatVal.var_inv h0
      have hf := PatVal.var_inv hf
      have ha := PatVal.var_inv ha
      obtain ⟨hc, hh, hp, ho⟩ := fn_flags 448 (.inl rfl)
      obtain ⟨rs, hts, hcase⟩ := EvalTerm.call_inv hc hh hp ho hrhs
      rcases hts with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩⟩
      rw [EvalTerm.var_inv e0, EvalTerm.var_inv e1, hd, hf] at hcase
      obtain ⟨hc', hh', hp', ho'⟩ := fn_flags 467 (.inr rfl)
      obtain ⟨rs', hts', hcase'⟩ := EvalTerm.call_inv hc' hh' hp' ho' e2
      rcases hts' with _ | ⟨e3, _ | ⟨e4, _ | _⟩⟩
      rw [EvalTerm.var_inv e3, EvalTerm.var_inv e4, hd, ha] at hcase'
      rcases hcase' with ⟨vs, hvs, hE⟩ | ⟨hn, -⟩
      · simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        subst hvs
        exact ⟨_, hE, hcase.imp (fun ⟨_, hws, hA⟩ => apply_args hws hA) fun ⟨hn, hr⟩ => ⟨apply_none hn, hr⟩⟩
      · simp [allSome] at hn
    all_goals first
      | exact (not_ap h1 (by decide)).elim
      | exact (not_ap (PatVal.as_inv h1).1 (by decide)).elim
  | rest hfn hnone =>
    rw [lookup_eval, Option.some.injEq] at hfn
    subst hfn
    have hw : c₀.WellSorted evApp.vars [(0, d), (1, f), (2, as)] := by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨d, rfl, hsd⟩
      | 1, hs => cases hs; exact ⟨f, rfl, hsf⟩
      | 2, hs => cases hs; exact ⟨as, rfl, hsa⟩
    have ha : evApp.AppliesAt c₀ [(0, d), (1, f), (2, as)] [d, .ctor 408 [f, as]] :=
      ⟨hw.at _, .cons (.var rfl) (.cons (.ctor (by decide +kernel) (.cons (.var rfl) (.cons (.var rfl) .nil))) .nil),
       ⟨fun _ h => absurd h (by simp [evApp]), Holds.top⟩⟩
    exact (not_fails rfl rfl ha (hnone evApp (List.mem_cons_self ..))).elim
  | ensFails hfn hmem _ _ _ _ _ _ ht =>
    rw [lookup_eval, Option.some.injEq] at hfn
    subst hfn
    simp only [fnEval, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    exact absurd ((Semantics.fnsNoExs_of_sortedOK hsorted).lookup hfn hmem) hne
  | exNone hfn hmem hne =>
    exact absurd ((Semantics.fnsNoExs_of_sortedOK hsorted).lookup hfn hmem) hne

end KK
