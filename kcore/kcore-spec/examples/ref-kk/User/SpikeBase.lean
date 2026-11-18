/-
  Helper-lemma spike on kore.k's own semantics, shared part: the equations of `app`, `lookup`,
  `mkInj` and `match` as literals (each function tied to the definition's semantics by
  `kernel_rfl`). The values the statements are over, and the sorts of those values, are User.KkKit's.

  The statements of User.SpikeHand and User.SpikeCascade are `F.eval` (the function's result at
  the values of a Lean function's arguments is the value of the Lean function's result) and
  `F.eval_iff` (it is the only result, by `Eval.functional KK.coherent`), at the interpretation
  `HookParams.none`. A list of terms is kore.k's `Ts` (`tsOf`), a list of numbered clause lists its
  `Fns` (`fnsOf`), a found clause list or nothing its `Look` (`lookOf`); terms, bindings and
  subsort lists are values of their sorts.
-/
import User.KkKit

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KK.Spike

open KCore KCore.Det RefKk KK KK.Kit

/-! ## The equations -/

/-- The clause of `app` from kore.k's rule `app-nil`. -/
def appNil : Clause :=
  { vars := [43],
    pats := [.app 406 [], .var 0],
    req := none,
    rhs := .var 0,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `app` from kore.k's rule `app-cons`. -/
def appCons : Clause :=
  { vars := [33, 43, 43],
    pats := [.app 407 [.var 0, .var 1], .var 2],
    req := none,
    rhs := .app 407 [.var 0, .app 447 [.var 1, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `app` (symbol 447) as the definition's semantics holds it. -/
def fnApp : Fn :=
  { label := 447, args := [43, 43], result := 43,
    clauses := [appNil, appCons], total := false }

theorem lookup_app : c₀.lookupFn 447 = some fnApp := by kernel_rfl

/-- The clause of `lookup` from kore.k's rule `lookup-hit`. -/
def lkHit : Clause :=
  { vars := [3, 3, 35, 39],
    pats := [.var 0, .app 421 [.var 1, .var 2, .var 3]],
    req := some (.app 23 [.var 0, .var 1]),
    rhs := .app 422 [.var 2],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `lookup` from kore.k's rule `lookup-miss`. -/
def lkMiss : Clause :=
  { vars := [3, 3, 35, 39],
    pats := [.var 0, .app 421 [.var 1, .var 2, .var 3]],
    req := some (.app 24 [.var 0, .var 1]),
    rhs := .app 485 [.var 0, .var 3],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `lookup` from kore.k's rule `lookup-nil`. -/
def lkNil : Clause :=
  { vars := [3],
    pats := [.var 0, .app 402 []],
    req := none,
    rhs := .app 432 [],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `lookup` (symbol 485) as the definition's semantics holds it. -/
def fnLookup : Fn :=
  { label := 485, args := [3, 39], result := 40,
    clauses := [lkHit, lkMiss, lkNil], total := false }

theorem lookup_lookup : c₀.lookupFn 485 = some fnLookup := by kernel_rfl

/-- The clause of `match` from kore.k's rule `m-app`. -/
def mApp : Clause :=
  { vars := [3, 32, 43, 3, 43, 46],
    pats := [.app 408 [.var 0, .var 2], .app 408 [.var 3, .var 4], .var 5, .var 1],
    req := some (.app 23 [.var 0, .var 3]),
    rhs := .app 489 [.var 2, .var 4, .var 5, .var 1],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-as`. -/
def mAs : Clause :=
  { vars := [33, 46, 32, 33, 3],
    pats := [.app 409 [.var 3, .var 4], .var 0, .var 1, .var 2],
    req := none,
    rhs := .app 451 [.var 4, .var 0, .app 486 [.var 3, .var 0, .var 1, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-bool`. -/
def mBool : Clause :=
  { vars := [46, 2, 2, 32],
    pats := [.app 413 [.var 1], .app 413 [.var 2], .var 0, .var 3],
    req := some (.app 10 [.var 1, .var 2]),
    rhs := .app 428 [.var 0, .app 403 []],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-col`. -/
def mCol : Clause :=
  { vars := [34, 3, 43, 34, 32, 46, 3, 43],
    pats := [.app 414 [.var 0, .var 1, .var 2], .app 416 [.var 3, .var 6, .var 7], .var 5, .var 4],
    req := none,
    rhs := .app 487 [.var 0, .var 1, .var 2, .var 7, .var 5, .var 4],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-el`. -/
def mEl : Clause :=
  { vars := [32, 33, 33, 46],
    pats := [.app 419 [.var 1], .app 419 [.var 2], .var 3, .var 0],
    req := none,
    rhs := .app 486 [.var 1, .var 2, .var 3, .var 0],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-inj-same`. -/
def mInjSame : Clause :=
  { vars := [3, 46, 32, 33, 3, 3, 33, 3],
    pats := [.app 424 [.var 0, .var 7, .var 3], .app 424 [.var 4, .var 5, .var 6], .var 1, .var 2],
    req := some (.app 23 [.var 0, .var 4]),
    rhs := .app 486 [.var 3, .var 6, .var 1, .var 2],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-inj-sub`. -/
def mInjSub : Clause :=
  { vars := [3, 3, 33, 46, 32, 3, 33, 3],
    pats := [.app 424 [.var 0, .var 1, .var 2], .app 424 [.var 7, .var 5, .var 6], .var 3, .var 4],
    req := some (.app 4 [.app 24 [.var 0, .var 7], .app 482 [.var 7, .var 0, .var 4]]),
    rhs := .app 486 [.var 2, .app 424 [.var 7, .var 0, .var 6], .var 3, .var 4],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-int`. -/
def mInt : Clause :=
  { vars := [3, 3, 46, 32],
    pats := [.app 425 [.var 0], .app 425 [.var 1], .var 2, .var 3],
    req := some (.app 23 [.var 0, .var 1]),
    rhs := .app 428 [.var 2, .app 403 []],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-kv`. -/
def mKv : Clause :=
  { vars := [32, 33, 33, 33, 46, 33],
    pats := [.app 426 [.var 5, .var 1], .app 426 [.var 2, .var 3], .var 4, .var 0],
    req := none,
    rhs := .app 489 [.app 407 [.var 5, .app 407 [.var 1, .app 406 []]], .app 407 [.var 2, .app 407 [.var 3, .app 406 []]], .var 4, .var 0],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-tok`. -/
def mTok : Clause :=
  { vars := [46, 32, 3, 10, 3, 10],
    pats := [.app 443 [.var 2, .var 3], .app 443 [.var 4, .var 5], .var 0, .var 1],
    req := some (.app 4 [.app 23 [.var 2, .var 4], .app 285 [.var 3, .var 5]]),
    rhs := .app 428 [.var 0, .app 403 []],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-var`. -/
def mVar : Clause :=
  { vars := [3, 33, 46, 32],
    pats := [.app 445 [.var 0], .var 1, .var 2, .var 3],
    req := none,
    rhs := .app 452 [.var 0, .var 1, .var 2, .app 484 [.var 0, .var 2]],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `match` from kore.k's rule `m-fail`. -/
def mFail : Clause :=
  { vars := [33, 33, 46, 32],
    pats := [.var 0, .var 1, .var 2, .var 3],
    req := none,
    rhs := .app 403 [],
    ens := none,
    prio := 200,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `match` (symbol 486) as the definition's semantics holds it. -/
def fnMatch : Fn :=
  { label := 486, args := [33, 33, 46, 32], result := 37,
    clauses := [mApp, mAs, mBool, mCol, mEl, mInjSame, mInjSub, mInt, mKv, mTok, mVar, mFail], total := false }

theorem lookup_match : c₀.lookupFn 486 = some fnMatch := by kernel_rfl

/-- The clause of `mkInj` from kore.k's rule `inj-compose`. -/
def injCompose : Clause :=
  { vars := [3, 3, 33, 3, 3],
    pats := [.var 3, .var 4, .app 424 [.var 0, .var 1, .var 2]],
    req := none,
    rhs := .app 424 [.var 0, .var 4, .var 2],
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `mkInj` from kore.k's rule `inj-bot`. -/
def injBot : Clause :=
  { vars := [3, 33, 3],
    pats := [.var 2, .var 0, .as (.app 412 []) 1],
    req := none,
    rhs := .var 1,
    ens := none,
    prio := 50,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- The clause of `mkInj` from kore.k's rule `inj-new`. -/
def injNew : Clause :=
  { vars := [3, 3, 33],
    pats := [.var 0, .var 1, .var 2],
    req := none,
    rhs := .app 424 [.var 0, .var 1, .var 2],
    ens := none,
    prio := 200,
    aside := false,
    exs := [],
    pre := .top,
    post := .top }

/-- `mkInj` (symbol 493) as the definition's semantics holds it. -/
def fnMkInj : Fn :=
  { label := 493, args := [3, 3, 33], result := 33,
    clauses := [injCompose, injBot, injNew], total := false }

theorem lookup_mkInj : c₀.lookupFn 493 = some fnMkInj := by kernel_rfl

end KK.Spike
