/-
  kore.k's functions at the interpretation `HookParams.none`: every function has at most one
  result (`KK.fnDet : FnDet c₀`, from `KK.coherent`), and evaluation does not solve the equations
  (`KK.not_fnSolves : ¬ FnSolves c₀`), so `consistent_of` does not apply to `c₀`.

  The point: `match(ij(2, 2, bot), ij(1, 1, bot), .Bind, sub(1, 1, .Subs))`.
  - `leq(1, 2, sub(1, 1, .Subs))` has no result (`leq_none`): `leq-up` applies (`1 =/=Int 2`) and
    gives `above(1, 2, S, S)`, where `above-hit` applies (the table's first entry starts at 1) and
    gives `leq(1, 2, S) orBool above(1, 2, .Subs, S)`, whose first operand is the call again; the
    other equations do not apply (`1 ==Int 2`, `1 =/=Int 1` and `.Subs` against `sub(…)` are false),
    and the rest needs `leq-up` (or `above-hit`) to fail. Each derivation of the call holds one of
    the same call, so there is none.
  - `match`'s equation `m-inj-sub` has the `requires` `2 =/=Int 1 andBool leq(1, 2, S)`, which
    therefore has no result there (`subReq_none`); `m-inj-same`'s `requires` `2 ==Int 1` is false
    and the nine other equations of priority 50 match another constructor.
  - So the `[owise]` equation `m-fail` decides there (`DecidesAt`: none of a smaller priority
    applies), and its right side `.Ms` has a value; but `match` has no result there
    (`match_none`): `m-fail` would need `m-inj-sub` to fail (`Fails`), which needs its `requires`
    to have a result.
-/
import User.Coherent

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK

open KCore KCore.Det RefKk

/-- **Every function of kore.k has at most one result at `HookParams.none`.** -/
theorem fnDet : FnDet c₀ := fnDet_of_coherent coherent

/-! ## The equations the argument reads -/

/-- The clause of `above` from kore.k's rule `above-hit`. -/
def aboveHit : Clause :=
  { vars := [3, 3, 3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 442 [.var 2, .var 3, .var 4], .var 5],
    req := some (.app 23 [.var 2, .var 0]),
    rhs := .app 6 [.app 482 [.var 3, .var 1, .var 5], .app 446 [.var 0, .var 1, .var 4, .var 5]],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `above` from kore.k's rule `above-miss`. -/
def aboveMiss : Clause :=
  { vars := [3, 3, 3, 3, 32, 32],
    pats := [.var 0, .var 1, .app 442 [.var 2, .var 3, .var 4], .var 5],
    req := some (.app 24 [.var 2, .var 0]),
    rhs := .app 446 [.var 0, .var 1, .var 4, .var 5],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `above` from kore.k's rule `above-nil`. -/
def aboveNil : Clause :=
  { vars := [3, 3, 32],
    pats := [.var 0, .var 1, .app 405 [], .var 2],
    req := none,
    rhs := .dv 2 (.bool false),
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- `above` (symbol 446) as the definition's semantics holds it. -/
def fnAbove : Fn :=
  { label := 446, args := [3, 3, 32, 32], result := 2,
    clauses := [aboveHit, aboveMiss, aboveNil], total := false }

/-- The clause of `leq` from kore.k's rule `leq-up`. -/
def leqUp : Clause :=
  { vars := [3, 3, 32],
    pats := [.var 0, .var 1, .var 2],
    req := some (.app 24 [.var 0, .var 1]),
    rhs := .app 446 [.var 0, .var 1, .var 2, .var 2],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `leq` from kore.k's rule `leq-refl`. -/
def leqRefl : Clause :=
  { vars := [3, 3, 32],
    pats := [.var 0, .var 1, .var 2],
    req := some (.app 23 [.var 0, .var 1]),
    rhs := .dv 2 (.bool true),
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- `leq` (symbol 482) as the definition's semantics holds it. -/
def fnLeq : Fn :=
  { label := 482, args := [3, 3, 32], result := 2, clauses := [leqUp, leqRefl], total := false }

/-- The clause of `match` from kore.k's rule `m-app`. -/
def mApp : Clause :=
  { vars := [3, 43, 3, 46, 32, 43],
    pats := [.app 408 [.var 0, .var 1], .app 408 [.var 2, .var 5], .var 3, .var 4],
    req := some (.app 23 [.var 0, .var 2]),
    rhs := .app 489 [.var 1, .var 5, .var 3, .var 4],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-as`. -/
def mAs : Clause :=
  { vars := [46, 32, 33, 3, 33],
    pats := [.app 409 [.var 2, .var 3], .var 4, .var 0, .var 1],
    req := none,
    rhs := .app 451 [.var 3, .var 4, .app 486 [.var 2, .var 4, .var 0, .var 1]],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-bool`. -/
def mBool : Clause :=
  { vars := [46, 32, 2, 2],
    pats := [.app 413 [.var 2], .app 413 [.var 3], .var 0, .var 1],
    req := some (.app 10 [.var 2, .var 3]),
    rhs := .app 428 [.var 0, .app 403 []],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-col`. -/
def mCol : Clause :=
  { vars := [3, 43, 46, 32, 34, 3, 43, 34],
    pats := [.app 414 [.var 4, .var 5, .var 6], .app 416 [.var 7, .var 0, .var 1], .var 2, .var 3],
    req := none,
    rhs := .app 487 [.var 4, .var 5, .var 6, .var 1, .var 2, .var 3],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-el`. -/
def mEl : Clause :=
  { vars := [46, 33, 33, 32],
    pats := [.app 419 [.var 1], .app 419 [.var 2], .var 0, .var 3],
    req := none,
    rhs := .app 486 [.var 1, .var 2, .var 0, .var 3],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-inj-same`. -/
def mInjSame : Clause :=
  { vars := [33, 46, 32, 3, 33, 3, 3, 3],
    pats := [.app 424 [.var 7, .var 3, .var 4], .app 424 [.var 5, .var 6, .var 0], .var 1, .var 2],
    req := some (.app 23 [.var 7, .var 5]),
    rhs := .app 486 [.var 4, .var 0, .var 1, .var 2],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- `A =/=Int C andBool leq(C, A, S)`, the `requires` of `m-inj-sub`. -/
abbrev subReq : Term := .app 4 [.app 24 [.var 4, .var 1], .app 482 [.var 1, .var 4, .var 7]]

/-- The clause of `match` from kore.k's rule `m-inj-sub`. -/
def mInjSub : Clause :=
  { vars := [33, 3, 3, 33, 3, 3, 46, 32],
    pats := [.app 424 [.var 4, .var 5, .var 0], .app 424 [.var 1, .var 2, .var 3], .var 6, .var 7],
    req := some subReq,
    rhs := .app 486 [.var 0, .app 424 [.var 1, .var 4, .var 3], .var 6, .var 7],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-int`. -/
def mInt : Clause :=
  { vars := [46, 32, 3, 3],
    pats := [.app 425 [.var 2], .app 425 [.var 3], .var 0, .var 1],
    req := some (.app 23 [.var 2, .var 3]),
    rhs := .app 428 [.var 0, .app 403 []],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-kv`. -/
def mKv : Clause :=
  { vars := [32, 33, 33, 33, 46, 33],
    pats := [.app 426 [.var 5, .var 1], .app 426 [.var 2, .var 3], .var 4, .var 0],
    req := none,
    rhs := .app 489 [.app 407 [.var 5, .app 407 [.var 1, .app 406 []]],
      .app 407 [.var 2, .app 407 [.var 3, .app 406 []]], .var 4, .var 0],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-tok`. -/
def mTok : Clause :=
  { vars := [3, 32, 10, 3, 10, 46],
    pats := [.app 443 [.var 0, .var 2], .app 443 [.var 3, .var 4], .var 5, .var 1],
    req := some (.app 4 [.app 23 [.var 0, .var 3], .app 285 [.var 2, .var 4]]),
    rhs := .app 428 [.var 5, .app 403 []],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-var`. -/
def mVar : Clause :=
  { vars := [3, 46, 32, 33],
    pats := [.app 445 [.var 0], .var 3, .var 1, .var 2],
    req := none,
    rhs := .app 452 [.var 0, .var 3, .var 1, .app 484 [.var 0, .var 1]],
    ens := none, prio := 50, aside := false, exs := [], pre := .top, post := .top }

/-- The clause of `match` from kore.k's rule `m-fail` (`[owise]`). -/
def mFail : Clause :=
  { vars := [33, 33, 46, 32],
    pats := [.var 0, .var 1, .var 2, .var 3],
    req := none,
    rhs := .app 403 [],
    ens := none, prio := 200, aside := false, exs := [], pre := .top, post := .top }

/-- `match` (symbol 486) as the definition's semantics holds it. -/
def fnMatch : Fn :=
  { label := 486, args := [33, 33, 46, 32], result := 37,
    clauses := [mApp, mAs, mBool, mCol, mEl, mInjSame, mInjSub, mInt, mKv, mTok, mVar, mFail],
    total := false }

theorem lookup_above : c₀.lookupFn 446 = some fnAbove := by kernel_rfl
theorem lookup_leq : c₀.lookupFn 482 = some fnLeq := by kernel_rfl
theorem lookup_match : c₀.lookupFn 486 = some fnMatch := by kernel_rfl
theorem get_match : c₀.fns[40]? = some fnMatch := by kernel_rfl
theorem mem_injSub : mInjSub ∈ fnMatch.clauses :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
theorem mem_fail : mFail ∈ fnMatch.clauses :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))
theorem mem_match : fnMatch ∈ c₀.fns := List.mem_of_getElem? get_match

/-! ## The point -/

/-- `.Subs`, `sub(1, 1, .Subs)`, `bot`, `.Bind`, and the two injections. -/
abbrev subsNil : GroundTerm := .ctor 405 []
abbrev S₁ : GroundTerm := .ctor 442 [int 1, int 1, subsNil]
abbrev botT : GroundTerm := .ctor 412 []
abbrev bindNil : GroundTerm := .ctor 400 []
abbrev ij₂ : GroundTerm := .ctor 424 [int 2, int 2, botT]
abbrev ij₁ : GroundTerm := .ctor 424 [int 1, int 1, botT]

/-- The arguments of `match` at which `FnSolves` fails. -/
abbrev vs₀ : List GroundTerm := [ij₂, ij₁, bindNil, S₁]

/-! ## Hooks on variables with values -/

/-- An Int comparison of two variables with Int values has the comparison's truth value. -/
theorem int2_val {σ : Subst} {f : Sym} {i j : Nat} {x y : Int} {P : Int → Int → Prop}
    [∀ x y, Decidable (P x y)] (hhk : isHook f = true)
    (hf : ∀ vs, hook f vs = some (int2 vs fun x y => some (bool (decide (P x y)))))
    (hi : σ.lookup i = some (int x)) (hj : σ.lookup j = some (int y)) {r : Option GroundTerm}
    (h : EvalTerm c₀ σ (.app f [.var i, .var j]) r) (hs : silentKey f = false := by decide +kernel)
    (hc : c₀.isCtor f = false := by decide +kernel) : r = some (bool (decide (P x y))) := by
  generalize ht : Term.app f [.var i, .var j] = e at h
  cases h with
  | ctor hk _ => cases ht; rw [hc] at hk; cases hk
  | @hook _ _ _ rs _ _ _ hts hh _ =>
    cases ht
    obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two hts
    rw [EvalTerm.var_inv h1, hi] at hh; rw [EvalTerm.var_inv h2, hj] at hh
    have hv := hh [int x, int y] rfl
    rw [Semantics.hookRes_of_notKey hs, hf, Option.some.injEq] at hv
    rw [← hv]; rfl
  | param _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | call _ hh _ _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | callUndef _ hh _ _ _ => cases ht; rw [hhk] at hh; cases hh
  | ovl _ ho _ => cases ht; have := (c₀.isOvl_parts ho).2.1; rw [hhk] at this; cases this
  | ovlFn _ ho => cases ht; have := (c₀.isOvl_parts ho).2.1; rw [hhk] at this; cases this
  | _ => cases ht

theorem isOvl_c₀ (f : Sym) : c₀.isOvl f = false := Semantics.isOvl_of_none (c := c₀) hovls

/-- Two variables with values: their list has those values. -/
theorem evalVars2 {σ : Subst} {i j : Nat} {v w : GroundTerm} (hi : σ.lookup i = some v)
    (hj : σ.lookup j = some w) {rs : List (Option GroundTerm)} (h : EvalTerms c₀ σ [.var i, .var j] rs) :
    rs = [some v, some w] := by
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := evalTerms_two h
  rw [EvalTerm.var_inv h1, hi, EvalTerm.var_inv h2, hj]

/-- Three variables with values: their list has those values. -/
theorem evalVars3 {σ : Subst} {i j k : Nat} {u v w : GroundTerm} (hi : σ.lookup i = some u)
    (hj : σ.lookup j = some v) (hk : σ.lookup k = some w) {rs : List (Option GroundTerm)}
    (h : EvalTerms c₀ σ [.var i, .var j, .var k] rs) : rs = [some u, some v, some w] := by
  cases h with
  | cons h1 hs =>
    rw [EvalTerm.var_inv h1, hi, evalVars2 hj hk hs]

/-- Four variables with values: their list has those values. -/
theorem evalVars4 {σ : Subst} {i j k l : Nat} {t u v w : GroundTerm} (hi : σ.lookup i = some t)
    (hj : σ.lookup j = some u) (hk : σ.lookup k = some v) (hl : σ.lookup l = some w)
    {rs : List (Option GroundTerm)} (h : EvalTerms c₀ σ [.var i, .var j, .var k, .var l] rs) :
    rs = [some t, some u, some v, some w] := by
  cases h with
  | cons h1 hs =>
    rw [EvalTerm.var_inv h1, hi, evalVars3 hj hk hl hs]

/-! ## `leq(1, 2, sub(1, 1, .Subs))` has no result -/

/-- What `leq-up` binds at `(1, 2, S₁)`. -/
def PUp (σ : Subst) : Prop :=
  σ.lookup 0 = some (int 1) ∧ σ.lookup 1 = some (int 2) ∧ σ.lookup 2 = some S₁

/-- What `above-hit` binds at `(1, 2, S₁, S₁)` (of what its right side reads). -/
def PHit (σ : Subst) : Prop :=
  σ.lookup 3 = some (int 1) ∧ σ.lookup 1 = some (int 2) ∧ σ.lookup 5 = some S₁

abbrev leqCall : Term := .app 482 [.var 3, .var 1, .var 5]
abbrev aboveRest : Term := .app 446 [.var 0, .var 1, .var 4, .var 5]

/-- What `leq-up` binds at `(1, 2, S₁)`. -/
theorem leq_args {σ : Subst} {vs : List GroundTerm} (hm : PatVals c₀ σ leqUp.pats vs)
    (hvs : vs = [int 1, int 2, S₁]) : PUp σ := by
  subst hvs
  rcases hm with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, -⟩⟩⟩
  exact ⟨PatVal.var_inv h0, PatVal.var_inv h1, PatVal.var_inv h2⟩

/-- What `above-hit` binds at `(1, 2, S₁, S₁)`. -/
theorem above_args {σ : Subst} {vs : List GroundTerm} (hm : PatVals c₀ σ aboveHit.pats vs)
    (hvs : vs = [int 1, int 2, S₁, S₁]) :
    σ.lookup 0 = some (int 1) ∧ σ.lookup 1 = some (int 2) ∧ σ.lookup 2 = some (int 1) ∧
      σ.lookup 3 = some (int 1) ∧ σ.lookup 4 = some subsNil ∧ σ.lookup 5 = some S₁ := by
  subst hvs
  rcases hm with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, -⟩⟩⟩⟩
  obtain ⟨es, he, hes⟩ := pv_ctor h2
  cases he
  rcases hes with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, -⟩⟩⟩
  exact ⟨PatVal.var_inv h0, PatVal.var_inv h1, PatVal.var_inv e0, PatVal.var_inv e1,
    PatVal.var_inv e2, PatVal.var_inv h3⟩

/-- `above-hit`'s `requires` at its match: `1 ==Int 1`. -/
theorem hit_req {σ : Subst} (h2 : σ.lookup 2 = some (int 1)) (h0 : σ.lookup 0 = some (int 1))
    {r : Option GroundTerm} (h : EvalTerm c₀ σ (.app 23 [.var 2, .var 0]) r) : r = some (bool true) :=
  (int2_val (f := intEq) rfl hook_intEq h2 h0 h).trans rfl

/-- `leq-up`'s `requires` at its match: `1 =/=Int 2`. -/
theorem up_req {σ : Subst} (h0 : σ.lookup 0 = some (int 1)) (h1 : σ.lookup 1 = some (int 2))
    {r : Option GroundTerm} (h : EvalTerm c₀ σ (.app 24 [.var 0, .var 1]) r) : r = some (bool true) :=
  (int2_val (f := intNe) rfl hook_intNe h0 h1 h).trans rfl

/-- `leq-up` does not fail at `(1, 2, S₁)`. -/
theorem up_not_fails (h : Fails c₀ [int 1, int 2, S₁] leqUp) : False := by
  cases h with
  | intro h =>
    let σ : Subst := [(0, int 1), (1, int 2), (2, S₁)]
    have hw : c₀.WellSortedAt leqUp.vars leqUp.leftVars σ := by
      intro i _ s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | _ + 3, hs => simp [leqUp] at hs
    cases h σ hw (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))) with
    | intro ht he hr => cases ht; exact hr (up_req rfl rfl he)
    | pre hf => exact absurd (Holds.top_eq hf) (by simp)

/-- `above-hit` does not fail at `(1, 2, S₁, S₁)`. -/
theorem hit_not_fails (h : Fails c₀ [int 1, int 2, S₁, S₁] aboveHit) : False := by
  cases h with
  | intro h =>
    let σ : Subst := [(0, int 1), (1, int 2), (2, int 1), (3, int 1), (4, subsNil), (5, S₁)]
    have hw : c₀.WellSortedAt aboveHit.vars aboveHit.leftVars σ := by
      intro i _ s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 3, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 4, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 5, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | _ + 6, hs => simp [aboveHit] at hs
    have hm : PatVals c₀ σ aboveHit.pats [int 1, int 2, S₁, S₁] :=
      .cons (.var rfl) (.cons (.var rfl)
        (.cons ((pv_ctor_iff).mpr ⟨_, rfl, .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))⟩)
          (.cons (.var rfl) .nil)))
    cases h σ hw hm with
    | intro ht he hr => cases ht; exact hr (hit_req rfl rfl he)
    | pre hf => exact absurd (Holds.top_eq hf) (by simp)
where
  pv_ctor_iff {σ : Subst} {ps : List Term} {v : GroundTerm} :
      PatVal c₀ σ (.app 442 ps) v ↔ ∃ vs, v = .ctor 442 vs ∧ PatVals c₀ σ ps vs :=
    PatVal.ctor_iff_of_not_hook (by decide +kernel) (by decide +kernel)

/-- **`leq(1, 2, sub(1, 1, .Subs))` has no result**: each derivation of it holds one of
`above(1, 2, S₁, S₁)`, and each of that one of the first. -/
theorem leq_none {r : Option GroundTerm} : ¬ Eval c₀ 482 [int 1, int 2, S₁] r := by
  intro hv
  exact Eval.rec (c := c₀)
    (motive_1 := fun f vs _ _ => (f = 482 ∧ vs = [int 1, int 2, S₁]) ∨
      (f = 446 ∧ vs = [int 1, int 2, S₁, S₁]) → False)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun σ t _ _ => (t = .app 446 [.var 0, .var 1, .var 2, .var 2] ∧ PUp σ) ∨
      (t = .app 6 [leqCall, aboveRest] ∧ PHit σ) ∨ (t = leqCall ∧ PHit σ) → False)
    (motive_5 := fun σ ts _ _ => ts = [leqCall, aboveRest] ∧ PHit σ → False)
    (motive_6 := fun _ _ _ _ _ => True)
    (fun {_ _ _ cl _ _} hfn hmem _ hmatch hreq _ _ _ _ _ _ _ ihrhs _ => fun hf => by
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [lookup_leq] at hfn; cases hfn
        simp only [fnLeq, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact ihrhs (.inl ⟨rfl, leq_args hmatch rfl⟩)
        · rcases hmatch with _ | ⟨h0, _ | ⟨h1, -⟩⟩
          have := int2_val (f := intEq) rfl hook_intEq (PatVal.var_inv h0) (PatVal.var_inv h1)
            (hreq _ rfl)
          exact absurd (bool_inj (Option.some.inj this)) (by decide)
      · rw [lookup_above] at hfn; cases hfn
        simp only [fnAbove, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · obtain ⟨-, h1, -, h3, -, h5⟩ := above_args hmatch rfl
          exact ihrhs (.inr (.inl ⟨rfl, h3, h1, h5⟩))
        · obtain ⟨h0, -, h2, -⟩ := above_args hmatch rfl
          have := int2_val (f := intNe) rfl hook_intNe h2 h0 (hreq _ rfl)
          exact absurd (bool_inj (Option.some.inj this)) (by decide)
        · rcases hmatch with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
          have := (PatVal.app_ctor_iff (f := 405) (by decide +kernel) (by decide +kernel)).mp h2
          exact absurd this.1 (by decide))
    (fun hfn hnone _ => fun hf => by
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [lookup_leq] at hfn; cases hfn
        exact up_not_fails (hnone leqUp (by simp [fnLeq]))
      · rw [lookup_above] at hfn; cases hfn
        exact hit_not_fails (hnone aboveHit (by simp [fnAbove])))
    (fun {_ _ _ cl _ _ _} hfn hmem _ _ _ _ _ ht _ _ _ _ _ _ => fun hf => by
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [lookup_leq] at hfn; cases hfn
        simp only [fnLeq, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> cases ht
      · rw [lookup_above] at hfn; cases hfn
        simp only [fnAbove, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl <;> cases ht)
    (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ => trivial)
    (fun h => by rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h)
    (fun h => by rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h)
    (fun _ _ => fun h => by rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h)
    (fun hk _ _ => fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h <;> exact absurd hk (by decide +kernel))
    (fun _ hhk _ _ _ ihts => fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, hp⟩ | ⟨h, -⟩ <;> cases h
      · exact absurd hhk (by decide +kernel)
      · exact ihts ⟨rfl, hp⟩
      · exact absurd hhk (by decide +kernel))
    (fun _ _ hp _ _ _ => fun h => by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h <;> exact absurd hp (by decide +kernel))
    (fun _ hh hts hvs _ _ _ ihf => fun h => by
      rcases h with ⟨h, ⟨h0, h1, h2⟩⟩ | ⟨h, -⟩ | ⟨h, ⟨h3, h1, h5⟩⟩ <;> cases h
      · rw [evalVars4 h0 h1 h2 h2 hts] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf (.inr ⟨rfl, hvs.symm⟩)
      · exact absurd hh (by decide +kernel)
      · rw [evalVars3 h3 h1 h5 hts] at hvs
        simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
        exact ihf (.inl ⟨rfl, hvs.symm⟩))
    (fun _ hh hts hvs _ _ => fun h => by
      rcases h with ⟨h, ⟨h0, h1, h2⟩⟩ | ⟨h, -⟩ | ⟨h, ⟨h3, h1, h5⟩⟩ <;> cases h
      · rw [evalVars4 h0 h1 h2 h2 hts] at hvs; simp [allSome] at hvs
      · exact absurd hh (by decide +kernel)
      · rw [evalVars3 h3 h1 h5 hts] at hvs; simp [allSome] at hvs)
    (fun _ ho _ _ _ => fun _ => absurd ho (by rw [isOvl_c₀]; decide))
    (fun _ ho _ _ _ _ _ _ _ => fun _ => absurd ho (by rw [isOvl_c₀]; decide))
    (fun h => by cases h.1)
    (fun _ _ ih1 _ => fun h => by
      obtain ⟨h, hp⟩ := h
      cases h
      exact ih1 (.inr (.inr ⟨rfl, hp⟩)))
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
    hv (.inl ⟨rfl, rfl⟩)

/-! ## `match` at the point -/

/-- What `m-inj-sub` binds at `vs₀` (of what its `requires` reads). -/
theorem sub_args {σ : Subst} (hm : PatVals c₀ σ mInjSub.pats vs₀) :
    σ.lookup 4 = some (int 2) ∧ σ.lookup 1 = some (int 1) ∧ σ.lookup 7 = some S₁ := by
  rcases hm with _ | ⟨h0, _ | ⟨h1, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩⟩
  obtain ⟨as, he, ha⟩ := pv_ctor h0
  cases he
  obtain ⟨bs, he, hb⟩ := pv_ctor h1
  cases he
  rcases ha with _ | ⟨a0, -⟩
  rcases hb with _ | ⟨b0, -⟩
  exact ⟨PatVal.var_inv a0, PatVal.var_inv b0, PatVal.var_inv h3⟩

/-- **`m-inj-sub`'s `requires` has no result at its match at `vs₀`**: its second operand is the
call `leq(1, 2, S₁)`. -/
theorem subReq_none {σ : Subst} (hm : PatVals c₀ σ mInjSub.pats vs₀) {r : Option GroundTerm} :
    ¬ EvalTerm c₀ σ subReq r := by
  intro h
  obtain ⟨h4, h1, h7⟩ := sub_args hm
  generalize ht : subReq = e at h
  cases h with
  | ctor hk _ => cases ht; exact absurd hk (by decide +kernel)
  | hook _ _ hts _ _ =>
    cases ht
    obtain ⟨r₁, r₂, rfl, -, h2⟩ := evalTerms_two hts
    obtain ⟨rs, hts', hcase⟩ := EvalTerm.call_inv (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (isOvl_c₀ _) h2
    rw [evalVars3 h1 h4 h7 hts'] at hcase
    rcases hcase with ⟨vs, hvs, hE⟩ | ⟨hn, -⟩
    · simp only [allSome, Option.bind_some, Option.map_some, Option.some.injEq] at hvs
      subst hvs
      exact leq_none hE
    · simp [allSome] at hn
  | param _ hh _ _ _ => cases ht; exact absurd hh (by decide +kernel)
  | call _ hh _ _ _ _ => cases ht; exact absurd hh (by decide +kernel)
  | callUndef _ hh _ _ _ => cases ht; exact absurd hh (by decide +kernel)
  | ovl _ ho _ => cases ht; exact absurd ho (by rw [isOvl_c₀]; decide)
  | ovlFn _ ho => cases ht; exact absurd ho (by rw [isOvl_c₀]; decide)
  | _ => cases ht

/-- `m-inj-same`'s `requires` at its match at `vs₀`: `2 ==Int 1`, false. -/
theorem same_req {σ : Subst} (hm : PatVals c₀ σ mInjSame.pats vs₀)
    (h : EvalTerm c₀ σ (.app 23 [.var 7, .var 5]) (some (bool true))) : False := by
  rcases hm with _ | ⟨h0, _ | ⟨h1, -⟩⟩
  obtain ⟨as, he, ha⟩ := pv_ctor h0
  cases he
  obtain ⟨bs, he, hb⟩ := pv_ctor h1
  cases he
  rcases ha with _ | ⟨a0, -⟩
  rcases hb with _ | ⟨b0, -⟩
  have := int2_val (f := intEq) rfl hook_intEq (PatVal.var_inv a0) (PatVal.var_inv b0) h
  exact absurd (bool_inj (Option.some.inj this)) (by decide)

/-- A clause whose first pattern is a constructor other than `ij` does not match `vs₀`. -/
theorem head_apart {σ : Subst} {k : Sym} {ps qs : List Term} (hm : PatVals c₀ σ (.app k ps :: qs) vs₀)
    (hk : c₀.isCtor k = true := by decide +kernel) (hp : patternHooks.contains k = false := by decide +kernel)
    (hne : k ≠ 424 := by decide) : False := by
  rcases hm with _ | ⟨h0, -⟩
  exact hne ((PatVal.app_ctor_iff hk hp).mp h0).1

/-- `m-fail` matches `vs₀` under σ₀. -/
abbrev σ₀ : Subst := [(0, ij₂), (1, ij₁), (2, bindNil), (3, S₁)]

/-- **`m-fail` decides at `vs₀`**: it applies there, and none of the equations of priority 50
applies. -/
theorem fail_decides : mFail.DecidesAt c₀ fnMatch σ₀ vs₀ := by
  refine ⟨⟨fun i s hs => ?_, .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))),
    (fun t ht => by cases ht), Holds.top⟩, fun cl' hcl' _ hlt σ' _ hm hq => ?_⟩
  · match i, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | _ + 4, hs => simp [mFail] at hs
  · simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hcl'
    rcases hcl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact same_req hm (hq.1 _ rfl)
    · exact subReq_none hm (hq.1 _ rfl)
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact absurd hlt (by decide)

/-- `m-inj-sub` does not fail at `vs₀`: its `requires` has no result there. -/
theorem sub_not_fails (h : Fails c₀ vs₀ mInjSub) : False := by
  cases h with
  | intro h =>
    let σ : Subst := [(0, botT), (1, int 1), (2, int 1), (3, botT), (4, int 2), (5, int 2),
      (6, bindNil), (7, S₁)]
    have hw : c₀.WellSortedAt mInjSub.vars mInjSub.leftVars σ := by
      intro i _ s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 3, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 4, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 5, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 6, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | 7, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
      | _ + 8, hs => simp [mInjSub] at hs
    have hm : PatVals c₀ σ mInjSub.pats vs₀ :=
      .cons (ij_iff.mpr ⟨_, rfl, .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))⟩)
        (.cons (ij_iff.mpr ⟨_, rfl, .cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))⟩)
          (.cons (.var rfl) (.cons (.var rfl) .nil)))
    cases h σ hw hm with
    | intro ht he _ => cases ht; exact subReq_none hm he
    | pre hf => exact absurd (Holds.top_eq hf) (by simp)
where
  ij_iff {σ : Subst} {ps : List Term} {v : GroundTerm} :
      PatVal c₀ σ (.app 424 ps) v ↔ ∃ vs, v = .ctor 424 vs ∧ PatVals c₀ σ ps vs :=
    PatVal.ctor_iff_of_not_hook (by decide +kernel) (by decide +kernel)

/-- **`match` has no result at `vs₀`.** -/
theorem match_none {r : Option GroundTerm} : ¬ Eval c₀ 486 vs₀ r := by
  intro h
  cases h with
  | clause hfn hmem _ hm hreq _ hprio _ _ =>
    rw [lookup_match, Option.some.injEq] at hfn
    subst hfn
    simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact same_req hm (hreq _ rfl)
    · exact subReq_none hm (hreq _ rfl)
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact head_apart hm
    · exact sub_not_fails (hprio mInjSub mem_injSub rfl (by decide))
  | rest hfn hnone =>
    rw [lookup_match, Option.some.injEq] at hfn
    subst hfn
    exact sub_not_fails (hnone mInjSub mem_injSub)
  | ensFails hfn hmem _ _ _ _ _ ht _ _ =>
    rw [lookup_match, Option.some.injEq] at hfn
    subst hfn
    simp only [fnMatch, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases ht

/-- **Evaluation does not solve kore.k's equations at `HookParams.none`**: at `vs₀`, of
`match`'s sorts, the `[owise]` equation `m-fail` decides and its right side has the value `.Ms`,
but `match` has no result there. -/
theorem not_fnSolves : ¬ FnSolves c₀ := by
  intro hs
  have hE := (hs fnMatch mem_match vs₀ (by decide +kernel) mFail mem_fail σ₀ fail_decides
    (.ctor 403 [])).mpr ⟨.ctor (by decide +kernel) .nil, fun t ht => by cases ht⟩
  exact match_none hE

end KK
