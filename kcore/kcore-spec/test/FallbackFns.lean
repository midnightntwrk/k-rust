/-
  Rests of functions: where every clause of a function fails at values of its argument sorts, the
  equations say nothing of its value, and KCore gives it the interpretation's (`Semantics.fnRest`,
  `Eval.rest`), the graph of which `Γ` states there (`Faithful.ΓFallback`). Where a clause decides,
  the rest is not read, also where that clause's `ensures` is not `true`: the text then gives the
  function no value there. Run from the package root: `lake env lean test/FallbackFns.lean`.

  - `Ens`: `f2-examples/ens.kompile.kore`, `half(N) => N /Int 2 ensures N >=Int 0` (the clause with
    the `ensures` `N >=Int 0`, `Clause.ens`), not declared total, and the rule
    `<k> run(N) => done(half(N)) </k>`. The text: `half(N) = N /Int 2 ∧ (N >=Int 0 = true)`.
    - `half(4)` is 2 under every interpretation (`half_4`).
    - At `-4` the clause decides (it has no `requires`, `half_not_fails`) and its `ensures` is false,
      so `half(-4)` has no value under every interpretation (`half_neg4_none`, `half_neg4_noValue`),
      among them `H7`, which gives `half(-4)` the value 7 as its rest (`fnRest_H7`): the rest is
      not read there (`half_neg4_H7`). `run(-4)` has no successor under every interpretation
      (`run_stuck`), and the executable step lists none (`run_stuck_none`).
  - `nc`: one function `F(Int) : Int` declared `[total]` with no equation (the case `clauses = []`):
    every argument is a point where every clause fails. Under `HookParams.none` it has no value
    anywhere and `FnHyp` fails (`AtNone.nc_noValue`, `AtNone.nc_not_fnHyp`); under `Hc`, which gives it `0`
    everywhere, `RestTotal` holds (`nc_restTotal`), so it is total (`total_of_restTotal_nil`) and
    `FnHyp` holds (`nc_fnHyp`).
  - `EnsReq`: `f2-examples/ensreq.kompile.kore`, `f(X) => 1 ensures X >Int 0` and
    `<k> a => b </k> requires f(0) ==Int 7`, the failing call in a rule's `requires`: `f(0)` has no
    value under every interpretation (`f0_none`), among them `H7`, which gives `f(0)` the rest 7
    (`rest_H7`), and `a` has no successor under every interpretation (`a_stuck`).
  - `et`: `G(Int) : Int` declared `[total]`, its one equation `G(X) = 1 ensures false`. The clause
    decides at every argument and its `ensures` is false, so under every interpretation `G` has no
    value (`et_noValue`) and `FnHyp` fails (`et_not_fnHyp`): the rest cannot make it total.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FallbackFnsTest

open KCore ML Faithful

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)

kernel_rfl clausesFixed_withHooks : ∀ (c : Semantics) (H : HookParams),
  (c.withHooks H).clausesFixed = c.clausesFixed
/-- `evalFC` reads no interpretation where no parameter is raw. -/
theorem evalFC_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (n : Nat) (f : Sym)
    (vs : List GroundTerm) : Cert.evalFC (c.withHooks H) n f vs = Cert.evalFC c n f vs :=
  Cert.evalFC_withHooks c H hr n f vs

/-! ## `half`, whose one clause has an `ensures` -/

namespace Ens

definition_of defn from "f2-examples/ens.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def half : Sym := 387
def run : Sym := 386
def done : Sym := 385
def kCell : Sym := 383
def cmd : Srt := 32

theorem names : c.symName half = "Lblhalf" ∧ c.symName run = "Lblrun" ∧ c.symName done = "Lbldone" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.sortName cmd = "Cmd" := by decide +kernel

/-- `half`, the definition's one function. -/
noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem fn_label : fn.label = half := by decide +kernel
/-- `half` is not declared total. -/
theorem fn_not_total : fn.total = false := by decide +kernel

/-- The interpretation that gives `half(-4)` the value 7 and nothing else. -/
def H7 : HookParams := ⟨fun f vs => if f = half ∧ vs = [int (-4)] then some (int 7) else none⟩

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn half = some fn := rfl

theorem hokH (H : HookParams) : (c.withHooks H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hsrH (H : HookParams) : (c.withHooks H).srReady = true := (Semantics.srReady_withHooks c H).trans hsr
theorem hmrH (H : HookParams) : (c.withHooks H).matchReady = true := (Semantics.matchReady_withHooks c H).trans hmr
theorem hfnH (H : HookParams) : (c.withHooks H).lookupFn half = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl

/-- A result `evalFC` computes on the data, which reads no interpretation, is `half`'s under every
interpretation. -/
theorem eval_of_evalFC {vs : List GroundTerm} (hvs : c.sortsOf vs = some fn.args) {n : Nat} {r : Option GroundTerm}
    (h : Cert.evalFC c n half vs = some r) (H : HookParams) : Eval (c.withHooks H) half vs r :=
  Exec.evalF_sound (sortCtx_of (hokH H) (hsrH H) (Exec.ovlCase_of (hmrH H))) (Exec.clauseCtx_of (hokH H))
    (Exec.matchCtx_of (hmrH H)) n (Cert.evalFC_sound n (by rw [evalFC_withHooks _ _ noRaw]; exact h)) (hfnH H)
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact hvs)

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil (hokH H) (hsrH H) (hmrH H) ((clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

/-- Where the `ensures` holds, the right-hand side's value, under every interpretation. -/
theorem half_4 (H : HookParams) : Eval (c.withHooks H) half [int 4] (some (int 2)) :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel) H

/-- At `-4` the clause does not fail under any interpretation: it has no `requires`. -/
theorem half_not_fails (H : HookParams) : ∀ cl ∈ fn.clauses, ¬ Fails (c.withHooks H) [int (-4)] cl := by
  intro cl hcl hf
  have hcl' : cl = ⟨[Srt.int], [.var 0], none, .app intTDiv [.var 0, .dv Srt.int (.int 2)],
      some (.app intGe [.var 0, .dv Srt.int (.int 0)]), 50, false, [], .top, .top⟩ := by
    have : fn.clauses = [_] := rfl
    rw [this] at hcl
    exact List.mem_singleton.mp hcl
  subst hcl'
  cases hf with
  | intro h =>
    have hσ : (c.withHooks H).WellSorted [Srt.int] [(0, int (-4))] := by
      intro i s hi
      cases i with
      | zero => cases hi; exact ⟨int (-4), rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
      | succ i => cases hi
    cases h [(0, int (-4))] (hσ.at _) (.cons (.var rfl) .nil) with
    | intro ht _ _ => cases ht
    | pre h => exact absurd (Holds.top_eq h) (by simp)

/-- So `half(-4)` has no value under every interpretation: the clause decides and its `ensures`
`-4 >=Int 0` is false. -/
theorem half_neg4_none (H : HookParams) : Eval (c.withHooks H) half [int (-4)] none :=
  eval_of_evalFC (by decide +kernel) (n := 10) (by decide +kernel) H

theorem half_neg4_noValue (H : HookParams) : ¬ ∃ v, Eval (c.withHooks H) half [int (-4)] (some v) :=
  fun ⟨_, h⟩ => nomatch Eval.functional (coherent H) h (half_neg4_none H)

/-- `H7` gives `half(-4)` the rest 7; it is not read there. -/
theorem fnRest_H7 : (c.withHooks H7).fnRest fn [int (-4)] = some (int 7) := by decide +kernel

theorem half_neg4_H7 : Eval (c.withHooks H7) half [int (-4)] none := half_neg4_none H7

/-- The configuration with `it` in the k cell and the counter at 0. -/
def cfg (it : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmd Srt.kitem it, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def X : Config c := ⟨cfg (.ctor run [int (-4)]), by decide +kernel⟩
def XH (H : HookParams) : Config (c.withHooks H) := ⟨X.val, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact X.property⟩

/-- Under the interpretation that gives nothing, the executable step lists no successor of
`run(-4)`. -/
theorem run_stuck_none : Exec.successorsN c 100 X.val = [] := by decide +kernel

/-- Under every interpretation, `run(-4)` has no successor: `done(half(-4))` denotes nothing. -/
theorem run_stuck (H : HookParams) : ∀ y, ¬ Step (c.withHooks H) (XH H) y :=
  Cert.stuckCheck_sound hok hsr hmr H (coherent H) (n := 100) (x := XH H)
    (show Cert.stuckCheck c 100 X.val = true by decide +kernel)

end Ens

/-! ## A function declared total with no equation -/

namespace NoClause

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def F : Sym := nRegSyms + 100

def fnF : Fn := ⟨F, [Srt.int], Srt.int, [], true⟩

def nc : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnF]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

theorem nc_lookup : nc.lookupFn F = some fnF := rfl

/-- The interpretation that gives `F` the value 0 at every argument list. -/
def Hc : HookParams := ⟨fun f _ => if f = F then some (int 0) else none⟩

-- At the interpretation that gives nothing (`HookParams.none`): no statement for every interpretation.
namespace AtNone

/-- Under the interpretation that gives nothing, `F` has no value at 0. -/
theorem nc_noValue : ¬ ∃ v, Eval nc F [int 0] (some v) := by
  rintro ⟨v, h⟩
  generalize hr : some v = r at h
  cases h with
  | clause hfn hmem _ _ _ _ _ _ _ =>
    rw [nc_lookup] at hfn; cases hfn
    simp [fnF] at hmem
  | ensFails hfn hmem _ _ _ _ _ _ _ _ =>
    rw [nc_lookup] at hfn; cases hfn
    simp [fnF] at hmem
  | clauseEx hfn hmem =>
    rw [nc_lookup] at hfn; cases hfn
    simp [fnF] at hmem
  | exNone hfn hmem =>
    rw [nc_lookup] at hfn; cases hfn
    simp [fnF] at hmem
  | rest hfn _ =>
    rw [nc_lookup] at hfn; cases hfn
    have : nc.fnRest fnF [int 0] = none := rfl
    rw [this] at hr; cases hr

/-- So `FnHyp` fails there: `F` is declared total. -/
theorem nc_not_fnHyp : ¬ FnHyp nc := fun h =>
  nc_noValue (h.2.1 fnF (List.mem_singleton_self _) rfl [int 0] (by decide +kernel))

end AtNone

theorem nc_restTotal : RestTotal nc Hc := by
  intro fn hfn _ vs _
  rw [List.mem_singleton.mp hfn]
  exact ⟨int 0, by show (if F = F then some (int 0) else none) = some (int 0); simp, by decide +kernel⟩

/-- Under `Hc`, `FnHyp` holds: `F`'s value everywhere is its rest. -/
theorem nc_fnHyp : FnHyp (nc.withHooks Hc) := by
  have hlook : (nc.withHooks Hc).lookupFn fnF.label = some fnF := by
    rw [Semantics.lookupFn_withHooks]; exact nc_lookup
  have hp : (nc.withHooks Hc).plain = true := (Semantics.plain_withHooks nc Hc).trans (by decide +kernel)
  refine ⟨fun fn hfn vs _ => ?_, fun fn hfn _ vs hvs => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    openDecided_of_plain (fun r hr => needsWitness_of_binds ((Semantics.plain_parts hp).1 r hr))
      (fun fn hfn cl hcl => Clause.needsWitness_of_binds ((Semantics.plain_parts hp).2.1 fn hfn cl hcl)),
    openLaws_of_plain (Semantics.plain_parts hp).2.2⟩
  · rw [List.mem_singleton.mp hfn]
    exact ⟨_, .rest hlook fun cl hcl => by simp [fnF] at hcl⟩
  · rw [List.mem_singleton.mp hfn] at hvs ⊢
    exact total_of_restTotal_nil nc_restTotal (List.mem_singleton_self _) rfl nc_lookup rfl
      (by decide +kernel) fnF hlook vs hvs
  · rw [List.mem_singleton.mp hfn]
    intro cl cl' h
    simp [fnF, pairs] at h
  · rw [List.mem_singleton.mp hfn] at hcl
    simp [fnF] at hcl

end NoClause

/-! ## A function declared total whose `ensures` fails -/

namespace EnsTotal

open NoClause (cellSorts cellCtors cellSubsorts)

def G : Sym := nRegSyms + 100

/-- `G(X) = 1 ensures false`: the text states `G(X) = 1 ∧ (false = true)`, no value anywhere,
beside the `[total]` declaration's `∃y. G(X) = y`. -/
def clG : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1), some (.dv Srt.bool (.bool false)), 50, false, [], .top, .top⟩

def fnG : Fn := ⟨G, [Srt.int], Srt.int, [clG], true⟩

def et : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := [fnG]
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

/-- No parameter of `et` is an open generator. -/
theorem noRaw : ∀ k ∈ et.params, k.raw = false := by decide +kernel

/-- Under every interpretation, `G` has no value at 0: its clause decides there and its `ensures`
is false. The rest, the interpretation's, is not read. -/
theorem et_noValue (H : HookParams) : ¬ ∃ v, Eval (et.withHooks H) G [int 0] (some v) := by
  rintro ⟨v, h⟩
  have hl : (et.withHooks H).lookupFn G = some fnG := by rw [Semantics.lookupFn_withHooks]; rfl
  generalize hr : some v = r at h
  cases h with
  | clause hfn hmem _ _ _ _ _ _ _ hens _ =>
    rw [hl] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem
    subst hmem
    cases hens _ rfl
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [hl] at hfn; cases hfn
    simp only [fnG, List.mem_singleton] at hmem
    subst hmem; exact absurd rfl hne
  | exNone => cases hr
  | rest hfn hnone =>
    rw [hl] at hfn; cases hfn
    have hσ : (et.withHooks H).WellSorted [Srt.int] [(0, int 0)] := by
      intro i s hi
      cases i with
      | zero => cases hi; exact ⟨int 0, rfl, by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel⟩
      | succ i => cases hi
    cases hnone clG (List.mem_singleton_self _) with
    | intro hf =>
      cases hf [(0, int 0)] (hσ.at _) (.cons (.var rfl) .nil) with
      | intro ht _ _ => cases ht
      | pre h => exact absurd (Holds.top_eq h) (by simp)
  | ensFails => cases hr

/-- So `FnHyp` fails under every interpretation: `G` is declared total, and no interpretation of
the rest gives it a value where its clause decides. -/
theorem et_not_fnHyp (H : HookParams) : ¬ FnHyp (et.withHooks H) := fun h =>
  et_noValue H (h.2.1 fnG (List.mem_singleton_self _) rfl [int 0] (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel))

end EnsTotal

/-! ## `f`, whose `ensures` fails at a call in a rule's `requires` -/

-- `f2-examples/ensreq.kompile.kore` (`ensreq.k`): `f(X) => 1 ensures X >Int 0` and
-- `<k> a => b </k> requires f(0) ==Int 7`. The text's equation is `\equals{SortInt{},R}(Lblf{}(X0),
-- \and{SortInt{}}(\dv{SortInt{}}("1"), \equals{SortBool{},SortInt{}}(Lbl'Unds-GT-'Int'Unds'{}(VarX,
-- \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))))` under `X0 ∈ VarX`: at 0 its right side is
-- `1 ∧ ⊥`, empty, so `f(0)` has no value; the rule's `requires` `f(0) ==Int 7 = true` is then
-- empty too, and the rule's axiom says nothing of `a`.
namespace EnsReq

definition_of defn from "f2-examples/ensreq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def f : Sym := 387
def a : Sym := 385
def kCell : Sym := 383
def cmd : Srt := 32

theorem names : c.symName f = "Lblf" ∧ c.symName a = "Lbla" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.sortName cmd = "Cmd" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem fn_label : fn.label = f := by decide +kernel

/-- `f`'s one clause: the pattern `X`, no `requires`, the right side 1, the `ensures` `X >Int 0`. -/
theorem fn_clauses : fn.clauses = [⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1),
    some (.app intGt [.var 0, .dv Srt.int (.int 0)]), 50, false, [], .top, .top⟩] := rfl

/-- The interpretation that gives `f(0)` the value 7 and nothing else. -/
def H7 : HookParams := ⟨fun g vs => if g = f ∧ vs = [int 0] then some (int 7) else none⟩

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hfn : c.lookupFn f = some fn := rfl

theorem hokH (H : HookParams) : (c.withHooks H).ok = true := (Semantics.ok_withHooks c H).trans hok
theorem hsrH (H : HookParams) : (c.withHooks H).srReady = true := (Semantics.srReady_withHooks c H).trans hsr
theorem hmrH (H : HookParams) : (c.withHooks H).matchReady = true := (Semantics.matchReady_withHooks c H).trans hmr
theorem hfnH (H : HookParams) : (c.withHooks H).lookupFn f = some fn := by
  rw [Semantics.lookupFn_withHooks]; rfl

theorem coherent (H : HookParams) : CoherentAll (c.withHooks H) :=
  Det.coherentAll_of_nil (hokH H) (hsrH H) (hmrH H) ((clausesFixed_withHooks c H).trans (by decide +kernel))
    ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))

/-- **`f(0)` has no value under every interpretation**: the clause decides at 0 (it has no
`requires`) and its `ensures` `0 >Int 0` is false. -/
theorem f0_none (H : HookParams) : Eval (c.withHooks H) f [int 0] none :=
  Exec.evalF_sound (sortCtx_of (hokH H) (hsrH H) (Exec.ovlCase_of (hmrH H))) (Exec.clauseCtx_of (hokH H))
    (Exec.matchCtx_of (hmrH H)) 10 (Cert.evalFC_sound 10 (by rw [evalFC_withHooks _ _ noRaw]; decide +kernel)) (hfnH H)
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)

/-- The point is reached: `H7` gives `f(0)` the rest 7, which is not read there. -/
theorem rest_H7 : (c.withHooks H7).fnRest fn [int 0] = some (int 7) := by decide +kernel

theorem f0_H7 : Eval (c.withHooks H7) f [int 0] none := f0_none H7

/-- The configuration with `a` in the k cell and the counter at 0. -/
def cfgA : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj cmd Srt.kitem (.ctor a []), .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def A : Config c := ⟨cfgA, by decide +kernel⟩
def AH (H : HookParams) : Config (c.withHooks H) := ⟨A.val, by rw [Semantics.sortOf_withHooks _ _ noRaw]; exact A.property⟩

/-- **`a` has no successor under every interpretation**: the rule's `requires` `f(0) ==Int 7` has no
value, so the rule does not apply, `H7` among them. -/
theorem a_stuck (H : HookParams) : ∀ y, ¬ Step (c.withHooks H) (AH H) y :=
  Cert.stuckCheck_sound hok hsr hmr H (coherent H) (n := 100) (x := AH H)
    (show Cert.stuckCheck c 100 A.val = true by decide +kernel)

end EnsReq

end KCore.FallbackFnsTest

#print axioms KCore.FallbackFnsTest.Ens.half_4
#print axioms KCore.FallbackFnsTest.Ens.half_not_fails
#print axioms KCore.FallbackFnsTest.Ens.half_neg4_noValue
#print axioms KCore.FallbackFnsTest.Ens.half_neg4_H7
#print axioms KCore.FallbackFnsTest.Ens.run_stuck
#print axioms KCore.FallbackFnsTest.Ens.run_stuck_none
#print axioms KCore.FallbackFnsTest.NoClause.AtNone.nc_not_fnHyp
#print axioms KCore.FallbackFnsTest.NoClause.nc_fnHyp
#print axioms KCore.FallbackFnsTest.EnsTotal.et_not_fnHyp
#print axioms KCore.FallbackFnsTest.EnsReq.f0_none
#print axioms KCore.FallbackFnsTest.EnsReq.rest_H7
#print axioms KCore.FallbackFnsTest.EnsReq.a_stuck
