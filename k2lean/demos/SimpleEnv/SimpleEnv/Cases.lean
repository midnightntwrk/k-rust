import SimpleEnv.Invariant
import KSimple.Preserves
import KPrelude.InvTactic
import KPrelude.InvColl

/-!
# Every rule of `KSimple` keeps `Invariant` (kind 2 layout: `Cases.lean`)

HAND-WRITTEN. `preserved` applies the generated `KSimple.Step.preserves_of` (169 rules) through
`k2l_preserve … hand SimpleEnv.hand`: the case of rule `r` is the theorem `SimpleEnv.hand.r` below when it
exists, and the tactic's closers prove it otherwise. A build logs
`k2l_preserve: N of M rules closed; hand: [...]; open: [...]`; each rule in `open` is an
`unsolved goals` error tagged by the rule, showing its goal `P lhs → P rhs` with the rule's
variables and side conditions in context. Give the closers more lemmas
(`k2l_preserve [l₁, …] split [f, …] hand …`), or prove the case by hand below:
`k2lean new-invariant --lib … --out … --from-log BUILD.log` adds a stub per open rule.

A hand case is stated as the generated `KSimple.Step.Case.r Invariant`, by reference, so an edit of
rule `r` changes what its hand case must prove and nothing else here; `k2lean diff OLD NEW --hand
THIS_PROJECT` lists the hand cases to revisit after a regeneration.

For SIMPLE, 164 of the 169 rules are closed by the tactic with the unfolding set of `preserved`
below, through the cell map of threads: the closers read the invariant of the thread a rule
matches off the match `k |-> T REST` and prove the thread it rebuilds. The 5 hand cases are the
rules that add or overwrite a store binding; each is one line of store reasoning followed by the
closers (`grow_close`).
-/

namespace SimpleEnv

open KPrelude KSimple

namespace hand

/-- The end of a case whose rule grows the store along `hg : ∀ v, InStore S v → InStore S' v`
(`S` the store before, `S'` after) and rebuilds one thread by `hr`, matched by `hm`: every
environment of the configuration that was in `S` is in `S'` (`threadsOk_mono`, `envIn_mono`),
and the collections closer proves the rebuilt thread from the matched one's facts. -/
local macro "grow_close" hm:ident hg:ident h:ident : tactic => `(tactic| (
  simp only [Invariant, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf] at $h:ident ⊢
  obtain ⟨h1, h2⟩ := $h:ident
  have ht := threadOk_mono $hg (MapHook.entry_of_concat_element $hm h1)
  have hrest := threadsOk_mono $hg (MapHook.entriesOn_of_concat_right $hm h1)
  have hgenv := envIn_mono $hg h2
  simp only [ThreadOk, EnvIn, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf, thK, thCtl,
    thEnv, kOf, envOf, ctlF, ctlX, fsOf, xsOf, envsI, envsK, envsC_eq, envsFO, envsXO,
    envsL_unit, envsL_element, envsL_concat, allIn_nil, allIn_cons, allIn_append,
    envsI_inj_Exp, envsI_inj_Exps, envsI_inj_Ids, envsI_inj_Stmt, envsI_inj_Val, envsI_inj_Vals,
    envsI_inj_IOInt, List.nil_append, List.append_nil, KSimple.K.initControlCell,
    KSimple.K.initFstackCell, KSimple.K.initXstackCell] at ht hgenv
  clear h1 h2
  k2l_coll_close [ThreadOk, EnvIn, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf, thK, thCtl,
    thEnv, kOf, envOf, ctlF, ctlX, fsOf, xsOf, envsI, envsK, envsC_eq, envsFO, envsXO,
    envsL_unit, envsL_element, envsL_concat, allIn_nil, allIn_cons, allIn_append,
    envsI_inj_Exp, envsI_inj_Exps, envsI_inj_Ids, envsI_inj_Stmt, envsI_inj_Val, envsI_inj_Vals,
    envsI_inj_IOInt, List.nil_append, List.append_nil, KSimple.K.initControlCell,
    KSimple.K.initFstackCell, KSimple.K.initXstackCell]))

/-! ## HAND CASE `var X;` (simple-untyped.md:444:3)

The rule allocates the location `L` (`<nextLoc>`) in the store and binds `X` to it in the
thread's `<env>`. `k2l_preserve` does not close it: the invariant before the step speaks of the
store `S`, after it of the larger store `S'`, and the closers have no lemma that carries a
predicate from `S` to `S'`. The proof gives that step (`grow_right`, `threadsOk_mono`) and the
new location (`inStore_left_element`); the closers do the rest. -/

theorem «var X;» : KSimple.Step.Case.«var X;» (Invariant) := by
  intro m Gen7 DotVar2 Gen6 Gen10 Gen8 Gen9 L DotVar0 k DotVar3 X DotVar5 Gen11 Env Gen12 r r_2 hm hr hr_3 hpri
  intro h
  have hg := grow_right hr_3
  have hL := inStore_left_element hr_3
  grow_close hm hg h

/-! ## HAND CASE `var X[N];` (simple-untyped.md:471:3)

The rule allocates `N + 1` locations (the array and its elements, through the function
`_..._|->_`) and binds `X` to the first. Not closed for the reason of `var X;`: the store grows. The
proof uses only that the old store is the right operand of the new one and that `L` is a key of
the left one, so it needs nothing about `_..._|->_`. -/

theorem «var X[N];» : KSimple.Step.Case.«var X[N];» (Invariant) := by
  intro m Gen7 DotVar2 Gen6 Gen10 Gen8 Gen9 L DotVar0 k DotVar3 X N DotVar5 Gen11 Env Gen12 r r_2 r_4 r_6 hm hreq hr hr_3 hr_5 hr_7 hpri
  intro h
  have hg := grow_right hr_7
  have hL : InStore r_6 (SortKItem.inj_Int L) := (inStore_concat hr_7 _).2 (.inl (inStore_left_element hr_5))
  grow_close hm hg h

/-! ## HAND CASE `function F(Xs) S` (simple-untyped.md:532:3)

The rule stores the function's `lambda` at a new location and binds `F` to it. Not closed
for the reason of `var X;`: the store grows. -/

theorem «function F(Xs) S» : KSimple.Step.Case.«function F(Xs) S» (Invariant) := by
  intro m Gen7 DotVar2 Gen6 Gen10 Gen8 Gen9 L DotVar0 k DotVar3 F Xs S DotVar5 Gen11 Env Gen12 r r_2 hm hr hr_3 hpri
  intro h
  have hg := grow_right hr_3
  have hL := inStore_left_element hr_3
  grow_close hm hg h

/-! ## HAND CASE `++ loc(L)` (simple-untyped.md:593:3)

The rule overwrites the value at the location `L`. Not closed because the store after the
step is a different term from the store before it (`L |-> I +Int 1` in place of `L |-> I`), so
the invariant before and after speak of two stores; they have the same locations
(`grow_overwrite`). -/

theorem «++ loc(L)» : KSimple.Step.Case.«++ loc(L)» (Invariant) := by
  intro m Gen7 m_2 Gen6 Gen11 Gen8 Gen10 Gen9 DotVar0 k DotVar3 L DotVar5 Gen12 Gen13 Gen14 DotVar2 I r r_7 hm hm_5 hr hr_8 hpri
  intro h
  have hg := grow_overwrite hm_5 hr_8
  grow_close hm hg h

/-! ## HAND CASE `loc(L) = V` (simple-untyped.md:759:3)

The rule overwrites the value at the location `L`. Not closed for the reason of `++ loc(L)`:
the store is rebuilt with another value at `L`, with the same locations (`grow_overwrite`). -/

theorem «loc(L) = V» : KSimple.Step.Case.«loc(L) = V» (Invariant) := by
  intro m Gen7 m_2 Gen6 Gen11 Gen8 Gen10 Gen9 DotVar0 k DotVar3 L y_3 DotVar5 Gen12 Gen13 Gen14 V v_4 DotVar2 r r_7 hm hp hm_6 hr hr_8 hpri
  intro h
  have hg := grow_overwrite hm_6 hr_8
  grow_close hm hg h

-- k2lean new-invariant --from-log: new hand cases go above this line
end hand

/-- Every rule of `KSimple` keeps `Invariant`. -/
theorem preserved : Preserved KSimple.Step Invariant := by
  k2l_preserve [ThreadOk, EnvIn, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf, thK, thCtl,
    thEnv, kOf, envOf, ctlF, ctlX, fsOf, xsOf, envsI, envsK, envsC_eq, envsFO, envsXO,
    envsL_unit, envsL_element, envsL_concat, allIn_nil, allIn_cons, allIn_append,
    envsI_inj_Exp, envsI_inj_Exps, envsI_inj_Ids, envsI_inj_Stmt, envsI_inj_Val, envsI_inj_Vals,
    envsI_inj_IOInt, List.nil_append, List.append_nil, KSimple.K.initControlCell,
    KSimple.K.initFstackCell, KSimple.K.initXstackCell] hand SimpleEnv.hand

end SimpleEnv
