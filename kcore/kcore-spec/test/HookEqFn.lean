/-
  A hooked symbol of the text whose hook no registry interprets, read as a function when the text
  gives it an equation. Of such a symbol the theory states the text's sentences alone (the hook
  attribute is no sentence, and the registry holds no prose for the hook): its equations where they
  apply, the interpretation's value where none does. That is the meaning `Eval` gives a function:
  a clause that decides gives its value (`Eval.clause`); where every clause fails the value is the
  rest, `Semantics.fnRest`, the interpretation's (`Eval.rest`). The same symbol without the
  equation is a parameter symbol with `impl = none`, whose value is the interpretation's at every
  point (`Semantics.paramVal`). Run from the package root: `lake env lean -j1 test/HookEqFn.lean`.

  `F(Int) : Int`, an own symbol (`nRegSyms + 100`), with the one equation `F(0) => 1` (the shape of
  the fixture `c3-hook-eq-param`, `lg(1) => 0` on `hook(INT.rand)`). `cF` reads it as a function
  with that clause; `cP` reads the symbol without the equation, as a parameter; `H7` gives `F` the
  value 7 at every argument list.
  - Under every interpretation `F(0)` is 1 (`fn_at_0`) and has no other result (`fn_at_0_only`):
    where the equation decides the interpretation is not read.
  - At 5 the equation does not apply and the value is the function's rest (`fn_at_5`): 7 under
    `H7` (`rest_H7`), none under `HookParams.none` (`rest_none`); `fn_H7` states both points under
    `H7`.
  - Read as a parameter, the symbol's value under `H7` is 7 at both points (`param_H7`). So the
    equation changes the value at the point where it decides and nowhere else.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.HookEqFnTest

open KCore

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def F : Sym := nRegSyms + 100

def base (fns : List Fn) (params : List ParamSig) : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := fns
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []
  params := params

/-- The interpretation that gives `F` the value 7 at every argument list. -/
def H7 : HookParams := ⟨fun f _ => if f = F then some (int 7) else none⟩

theorem patVal_dv {c : Semantics} {σ : Subst} {s : Srt} {l : Lit} {v : GroundTerm}
    (h : PatVal c σ (.dv s l) v) : v = .dv s l := by
  cases h; rfl

/-- `F(0) => 1` -/
def clF : Clause := ⟨[], [.dv Srt.int (.int 0)], none, .dv Srt.int (.int 1), none, 50, false, [], .top, .top⟩
def fnF : Fn := ⟨F, [Srt.int], Srt.int, [clF], false⟩

/-- read as a function: the equation is its clause -/
def cF : Semantics := base [fnF] []
/-- the same symbol without the equation: a parameter symbol with `impl = none` -/
def cP : Semantics := base [] [{ sig := ⟨F, [Srt.int], Srt.int⟩ }]

theorem cF_lookup (H : HookParams) : (cF.withHooks H).lookupFn F = some fnF := by
  rw [Semantics.lookupFn_withHooks]; rfl

/-- Where the equation decides, the value is the equation's, under every interpretation. -/
theorem fn_at_0 (H : HookParams) : Eval (cF.withHooks H) F [int 0] (some (int 1)) :=
  .clause (cl := clF) (σ := []) (cF_lookup H) (List.mem_singleton_self _)
    (fun i s hi => by simp [clF] at hi) (.cons .dv .nil) (fun t ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun t ht => by cases ht) .top

/-- And it has no other result there: the interpretation is not read. -/
theorem fn_at_0_only (H : HookParams) (r : Option GroundTerm)
    (h : Eval (cF.withHooks H) F [int 0] r) : r = some (int 1) := by
  cases h with
  | clause hfn hmem _ _ _ _ _ _ hrhs _ _ =>
    rw [cF_lookup] at hfn; cases hfn
    rw [List.mem_singleton.mp hmem] at hrhs
    generalize hr : clF.rhs = t at hrhs
    cases hrhs <;> cases hr
    rfl
  | rest hfn hnone =>
    rw [cF_lookup] at hfn; cases hfn
    cases hnone clF (List.mem_singleton_self _) with
    | intro hf =>
      cases hf [] (fun i _ s hi => by simp [clF] at hi) (.cons .dv .nil) with
      | intro ht _ _ => cases ht
      | pre h => exact absurd (Holds.top_eq h) (by simp)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [cF_lookup] at hfn; cases hfn
    rw [List.mem_singleton.mp hmem] at ht; cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [cF_lookup] at hfn; cases hfn
    rw [List.mem_singleton.mp hmem] at hne; exact absurd rfl hne
  | exNone hfn hmem hne =>
    rw [cF_lookup] at hfn; cases hfn
    rw [List.mem_singleton.mp hmem] at hne; exact absurd rfl hne

/-- Where the equation does not apply, the value is the interpretation's (the function's rest). -/
theorem fn_at_5 (H : HookParams) :
    Eval (cF.withHooks H) F [int 5] ((cF.withHooks H).fnRest fnF [int 5]) :=
  .rest (cF_lookup H) fun cl hcl => by
    rw [List.mem_singleton.mp hcl]
    refine .intro fun σ _ hp => ?_
    cases hp with
    | cons h _ => exact absurd (patVal_dv h) (by decide)

theorem rest_H7 : (cF.withHooks H7).fnRest fnF [int 5] = some (int 7) := by decide +kernel
theorem rest_none : (cF.withHooks HookParams.none).fnRest fnF [int 5] = none := by decide +kernel

/-- Under `H7`: `F(0)` is 1 by the equation, `F(5)` is 7 by the interpretation. -/
theorem fn_H7 : Eval (cF.withHooks H7) F [int 0] (some (int 1)) ∧ Eval (cF.withHooks H7) F [int 5] (some (int 7)) :=
  ⟨fn_at_0 H7, rest_H7 ▸ fn_at_5 H7⟩

/-- The symbol without the equation, a parameter: the interpretation's value at both points. -/
theorem param_H7 : (cP.withHooks H7).paramVal F [int 0] = some (int 7) ∧
    (cP.withHooks H7).paramVal F [int 5] = some (int 7) := by decide +kernel

end KCore.HookEqFnTest

/--
info: 'KCore.HookEqFnTest.fn_at_0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.HookEqFnTest.fn_at_0
/--
info: 'KCore.HookEqFnTest.fn_at_0_only' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.HookEqFnTest.fn_at_0_only
/--
info: 'KCore.HookEqFnTest.fn_H7' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.HookEqFnTest.fn_H7
/--
info: 'KCore.HookEqFnTest.rest_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.HookEqFnTest.rest_none
/--
info: 'KCore.HookEqFnTest.param_H7' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.HookEqFnTest.param_H7
