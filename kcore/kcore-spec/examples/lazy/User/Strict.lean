/-
  Strict evaluation on the generated package `Lazy` (`f2-examples/lazy.k`), by the kernel.
  `t1`'s right-hand side calls `inv(0)`, an `ite{Int}` whose guard `0 =/=Int 0` is false and whose
  skipped then-branch `100 /Int 0` is undefined, so `inv(0)` is undefined and `t1` has no step; `p` has
  no clause at 0, so `p(0)` is its rest, which the interpretation that gives nothing (`HookParams.none`)
  leaves undefined: there `t3`'s `false andBool p(0)` is undefined, and `t3` has no step. A short-circuiting
  reading would step `t1` to `res(0)` and `t3` to `resB(false)`. These are the two occurrences the
  package lists (`lazy_obligations`), and the first of them, `inv`'s, is shown not to hold
  (`inv_obligation_fails`). `t2`, `t4` and `t5` step as both readings say: `t4`'s and `t5`'s skipped
  arguments are literals and calls of the `[total]` function `dbl`, which `definedArg` confirms.
-/
import Lazy
import KcoreSpec.Cert
import KcoreSpec.LazySound
import KcoreSpec.CollExecFinal

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Lazy.Strict

open KCore KCore.Cert Lazy

def ctr0 : GroundTerm := .ctor counterLabel [.dv KCore.Srt.int (.int 0)]
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<k>» [.ctor kseq [st, .ctor dotk []]], ctr0]
def cmd (f : Sym) : GroundTerm := .inj Srt.«Cmd» KCore.Srt.kitem (.ctor f [])
def resI (i : Int) : GroundTerm := .ctor Sym.«res» [.dv KCore.Srt.int (.int i)]

theorem t2_run : checkRun c 100 (cfg (cmd Sym.«t2»)) [(1, cfg (resI 25))] (cfg (resI 25)) = true := by
  decide +kernel
theorem t4_run : checkRun c 100 (cfg (cmd Sym.«t4»)) [(3, cfg (resI 5))] (cfg (resI 5)) = true := by
  decide +kernel
theorem t5_run : checkRun c 100 (cfg (cmd Sym.«t5»)) [(4, cfg (resI 4))] (cfg (resI 4)) = true := by
  decide +kernel

theorem t1_stuck : stuckCheck c 100 (cfg (cmd Sym.«t1»)) = true := by decide +kernel

/-- `t1` has no successor: `inv(0)` is undefined. -/
theorem t1_ends (hf : c.sortOf (cfg (cmd Sym.«t1»)) = some topCellSort) : ∀ y, ¬ Step c ⟨_, hf⟩ y :=
  stuckCheck_sound ok srReady matchReady c.hooks (coherent_withHooks c.hooks) (x := ⟨_, hf⟩) t1_stuck

theorem t3_fuel : CExec.outOfFuel (c.withHooks HookParams.none) 100 (cfg (cmd Sym.«t3»)) = false := by
  decide +kernel
theorem t3_none : CExec.successorsN (c.withHooks HookParams.none) 100 (cfg (cmd Sym.«t3»)) = [] := by
  decide +kernel

/-- Under the interpretation that gives nothing, `t3` has no successor: `p(0)` is its rest, undefined
there, so `false andBool p(0)` is. -/
theorem t3_ends (hf : (c.withHooks HookParams.none).sortOf (cfg (cmd Sym.«t3»)) = some topCellSort) :
    ∀ y, ¬ Step (c.withHooks HookParams.none) ⟨_, hf⟩ y :=
  CExec.noStep_at (by decide +kernel) (fnDet_of_coherent (coherent_withHooks HookParams.none)) t3_fuel t3_none

theorem t1_config : c.sortOf (cfg (cmd Sym.«t1»)) = some topCellSort := by decide +kernel

/-- **The listed obligation of `inv` does not hold**: at `inv(0)`, which its clause reaches, the
guard `0 =/=Int 0` is false and the skipped then-branch `100 /Int 0` has no value. -/
theorem inv_obligation_fails : ∃ o ∈ defn.sem.lazyObligations, ¬ o.Holds defn.sem := by
  rw [lazy_obligations]
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun h => ?_⟩
  have hsig := fn_inv_sig
  have hcl := fn_inv_0
  cases hfn : c.lookupFn Sym.«inv» with
  | none => rw [hfn] at hsig; cases hsig
  | some fn =>
    rw [hfn] at hsig hcl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsig
    simp only [Option.bind_some] at hcl
    let σ : Subst := [(0, int 0)]
    have hσ : c.WellSorted [KCore.Srt.int] σ := fun i s hi => by
      cases i with
      | zero => cases hi; exact ⟨_, rfl, sortOf_int 0⟩
      | succ i => simp at hi
    have hR : c.Reached (.clauseRhs Sym.«inv» 0) σ :=
      ⟨fn, _, hfn, hcl, hσ, ⟨[int 0], by rw [hsig.1]; exact sortsOf_cons.mpr ⟨_, _, sortOf_int 0, sortsOf_nil, rfl⟩,
        .cons (.var rfl) .nil, fun cl' hcl' hlt => by
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsig.2.2
          rw [hx] at hcl' hcl
          rw [List.mem_singleton.mp hcl'] at hlt
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
          subst hcl
          exact absurd hlt (by decide)⟩, fun t ht => by cases ht⟩
    have hguard : EvalTerm c σ (.app KCore.intNe [.var 0, .dv KCore.Srt.int (.int 0)]) (some (bool false)) :=
      EvalTerm.hook (by decide +kernel) rfl (.cons .var (.cons .dv .nil))
        (fun vs hv => by simp only [σ, allSome, List.lookup] at hv; cases hv; rfl) (fun hv => by cases hv)
    obtain ⟨v, hv⟩ := h σ hR hguard
    have hundef : EvalTerm c σ (.app KCore.intTDiv [.dv KCore.Srt.int (.int 100), .var 0]) none :=
      EvalTerm.hook (by decide +kernel) rfl (.cons .dv (.cons .var .nil))
        (fun vs hv => by simp only [σ, allSome, List.lookup] at hv; cases hv; rfl) (fun hv => by cases hv)
    cases EvalTerm.functional coherent hv hundef

/-- info: 'Lazy.Strict.inv_obligation_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inv_obligation_fails

/-- info: 'Lazy.Strict.t1_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_ends

end Lazy.Strict
