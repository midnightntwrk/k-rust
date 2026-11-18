/-
  Function priorities on the generated package `Fprio` (`f2-examples/fprio.k`), by the kernel.
  Each value is an `Eval` fact, computed by the executable evaluation and read through its
  soundness (`evalF_sound`); the clauses of one priority being coherent (`coherent`, from `ag`'s
  agreement `ag_agree`, the package's one named obligation), it is the function's only result
  (`Eval.functional`). The arguments are chosen so that the order of the priorities decides:
  - `pr(0)` is 1: `pr-low` (40) decides, though `pr-def` (50, `0 <=Int 5`) and `pr-mid` (100) match;
  - `pr(3)` is 2: `pr-def` (50) decides, though `pr-mid` (100) matches; `pr(9)` is 3;
  - `ow(5)` is 5: `ow-pos` (50) decides, though the `[owise]` `ow-else` (200, `5 >=Int -100`) applies;
  - `ow(-3)` is 3, by the `[owise]`; `ow(-200)` is undefined: `ow-pos`'s and the `[owise]`'s
    `requires` are both false;
  - `op(0, 0)` is 100 (`op-zz`, 30, over `op-z`, 50); `op(0, 4)` is 4; `op(1, 4)` is 7 by the
    `[owise]` over the pattern `op(1, _)`; `op(2, 4)` is undefined: no clause matches;
  - `ag(0)` is 0, where `ag-z` and `ag-sq`, both of priority 50, apply and agree; `ag(3)` is 9.
  The four rules step as these values say (`t1`, `t2`, `t3`), and `t4`, whose right-hand side calls
  `ow(-200)`, has no step. With the agreement, the package's obligations hold and it is sound
  (`sound_defn`).
-/
import Fprio
import Fprio.Sound
import KcoreSpec.Cert
import KcoreSpec.EvalComplete
import KcoreSpec.CollExecFinal

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Fprio.Values

open KCore KCore.Exec KCore.Cert Fprio

/-! ## `ag`'s two clauses of priority 50 agree -/

/-- `ag`'s clauses: `ag(0 #as X) => X` and `ag(N) => N *Int N`. -/
theorem ag_clauses {fn : Fn} (hfn : c.lookupFn Sym.«ag» = some fn) :
    fn.clauses = [{ vars := [KCore.Srt.int], pats := [.as (.dv KCore.Srt.int (.int 0)) 0], req := none,
                    rhs := .var 0, ens := none, prio := 50 },
                  { vars := [KCore.Srt.int], pats := [.var 0], req := none,
                    rhs := .app KCore.intMul [.var 0, .var 0], ens := none, prio := 50 }] := by
  have hsig := fn_ag_sig
  have h0 := fn_ag_0
  have h1 := fn_ag_1
  rw [hfn] at hsig h0 h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Option.bind_some] at hsig h0 h1
  have hl := hsig.2.2
  generalize fn.clauses = l at hl h0 h1 ⊢
  match l, hl with
  | [a, b], _ =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
    rw [h0, h1]

/-- Where `ag-z` applies, its argument is 0 and its right-hand side's result is 0. -/
theorem agZ_val {σ : Subst} {vs : List GroundTerm} {r : Option GroundTerm}
    (hm : PatVals c σ [.as (.dv KCore.Srt.int (.int 0)) 0] vs) (he : EvalTerm c σ (.var 0) r) :
    vs = [int 0] ∧ r = some (int 0) := by
  cases hm with
  | cons hp hs =>
    cases hs
    cases hp with
    | as hp hi =>
      cases hp
      cases he
      exact ⟨rfl, hi⟩

/-- Where `ag-sq` applies at `[int 0]`, its right-hand side's result is 0. -/
theorem agSq_val {σ : Subst} {r : Option GroundTerm}
    (hm : PatVals c σ [.var 0] [int 0]) (he : EvalTerm c σ (.app KCore.intMul [.var 0, .var 0]) r) :
    r = some (int 0) := by
  cases hm with
  | cons hp hs =>
    cases hp with
    | var hi =>
      cases he with
      | ctor h _ => exact absurd h (by decide +kernel)
      | hook _ _ hts hh _ =>
        cases hts with
        | cons h1 hs1 =>
          cases hs1 with
          | cons h2 hs2 =>
            cases hs2
            cases h1
            cases h2
            have := hh [int 0, int 0] (by simp only [allSome, hi]; rfl)
            rw [Semantics.hookRes_of_notKey (by decide +kernel)] at this
            simp only [hook] at this
            exact (Option.some.inj this).symm.trans rfl
      | param _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
      | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
      | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
      | ovl _ ho _ => exact absurd ho (by decide +kernel)
      | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- **`ag`'s agreement**, the package's one named agreement (`agree_obligations`): its two clauses,
of one priority, give one result where both apply, at `ag(0)`, in both orders. -/
theorem ag_agree : ∀ f ∈ c.agreeObligations, ∀ fn, c.lookupFn f = some fn → ClausesAgree c fn := by
  intro f hf fn hfn
  rw [agree_obligations] at hf
  rw [List.mem_singleton.mp hf] at hfn
  intro cl cl' hp _
  rw [ag_clauses hfn] at hp
  simp [pairs] at hp
  obtain ⟨rfl, rfl⟩ := hp
  refine ⟨Coherent.of_rhs rfl rfl fun vs σ σ' ha ha' _ _ _ => .inr fun r r' he he' => ?_,
          Coherent.of_rhs rfl rfl fun vs σ σ' ha ha' _ _ _ => .inr fun r r' he he' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := agZ_val ha.2.1 he
    exact (agSq_val ha'.2.1 he').symm
  · obtain ⟨rfl, rfl⟩ := agZ_val ha'.2.1 he'
    exact agSq_val ha.2.1 he

/-- The clauses of one priority are coherent. -/
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_fixed ok srReady matchReady clausesFixed ag_agree

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_defn : c.readsConfined = false := by decide +kernel

/-- **The package's named obligations hold**, and it is sound. -/
theorem obligations_hold : Obligations defn :=
  ⟨fun f hf => by rw [named_terminates] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [named_totals] at hf; exact absurd hf List.not_mem_nil,
   ag_agree,
   fun p hp => by rw [match_obligations] at hp; exact absurd hp List.not_mem_nil,
   fun o ho => by rw [lazy_obligations] at ho; exact absurd ho List.not_mem_nil,
   openDecided_of_readsConfined readsConfined_defn, openLaws_of_plain (by decide +kernel)⟩

theorem sound_defn : Sound defn := Fprio.sound obligations_hold

/-! ## Values by the executable evaluation -/

/-- The executable evaluation of f at vs, with fuel n, gives r (`none`: undefined), at arguments of
f's sorts. -/
noncomputable def evalAt (n : Nat) (f : Sym) (vs : List GroundTerm) (r : Option GroundTerm) : Bool :=
  match c.lookupFn f with
  | some fn => c.sortsOf vs == some fn.args &&
      (match evalF c n f vs, r with
       | some (some v), some w => same v w
       | some none, none => true
       | _, _ => false)
  | none => false

theorem eval_of_evalAt {f : Sym} {vs : List GroundTerm} {r : Option GroundTerm} (n : Nat)
    (h : evalAt n f vs r = true) : Eval c f vs r := by
  unfold evalAt at h
  split at h
  · rename_i fn hfn
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hvs, hev⟩ := h
    have snd := fun {r'} (he : evalF c n f vs = some r') =>
      evalF_sound (sortCtx_of ok srReady (ovlCase_of matchReady)) (clauseCtx_of ok) (matchCtx_of matchReady) n he hfn hvs
    revert hev
    cases hE : evalF c n f vs with
    | none => cases r <;> simp
    | some o =>
      cases o with
      | none => cases r <;> simp; exact snd hE
      | some v =>
        cases r with
        | none => simp
        | some w => intro hs; rw [same_iff.mp hs] at hE; exact snd hE
  · cases h

/-- The value the executable evaluation gives is f's only result. -/
theorem only_of_evalAt {f : Sym} {vs : List GroundTerm} {r r' : Option GroundTerm} (n : Nat)
    (h : evalAt n f vs r = true) (h' : Eval c f vs r') : r' = r :=
  Eval.functional coherent h' (eval_of_evalAt n h)

/-- `pr-low` (40) decides at 0, where `pr-def` (50) and `pr-mid` (100) also match. -/
theorem pr_0 : Eval c Sym.«pr» [int 0] (some (int 1)) := eval_of_evalAt 20 (by decide +kernel)
theorem pr_0_only {r : Option GroundTerm} (h : Eval c Sym.«pr» [int 0] r) : r = some (int 1) :=
  only_of_evalAt 20 (by decide +kernel) h
/-- `pr-def` (50) decides at 3, where `pr-mid` (100) also matches. -/
theorem pr_3 : Eval c Sym.«pr» [int 3] (some (int 2)) := eval_of_evalAt 20 (by decide +kernel)
theorem pr_3_only {r : Option GroundTerm} (h : Eval c Sym.«pr» [int 3] r) : r = some (int 2) :=
  only_of_evalAt 20 (by decide +kernel) h
/-- Only `pr-mid` (100) applies at 9. -/
theorem pr_9 : Eval c Sym.«pr» [int 9] (some (int 3)) := eval_of_evalAt 20 (by decide +kernel)

/-- `ow-pos` (50) decides at 5, where the `[owise]` (200) also applies (`5 >=Int -100`). -/
theorem ow_5 : Eval c Sym.«ow» [int 5] (some (int 5)) := eval_of_evalAt 20 (by decide +kernel)
theorem ow_5_only {r : Option GroundTerm} (h : Eval c Sym.«ow» [int 5] r) : r = some (int 5) :=
  only_of_evalAt 20 (by decide +kernel) h
/-- The `[owise]` decides at -3, where `ow-pos`'s `requires` is false. -/
theorem ow_m3 : Eval c Sym.«ow» [int (-3)] (some (int 3)) := eval_of_evalAt 20 (by decide +kernel)
/-- `ow` is undefined at -200: the `[owise]`'s `requires` is false there, as `ow-pos`'s is. -/
theorem ow_m200 : Eval c Sym.«ow» [int (-200)] none := eval_of_evalAt 20 (by decide +kernel)
theorem ow_m200_only {r : Option GroundTerm} (h : Eval c Sym.«ow» [int (-200)] r) : r = none :=
  only_of_evalAt 20 (by decide +kernel) h

/-- `op-zz` (30) decides at (0, 0), where `op-z` (50) also matches. -/
theorem op_00 : Eval c Sym.«op» [int 0, int 0] (some (int 100)) := eval_of_evalAt 20 (by decide +kernel)
theorem op_00_only {r : Option GroundTerm} (h : Eval c Sym.«op» [int 0, int 0] r) : r = some (int 100) :=
  only_of_evalAt 20 (by decide +kernel) h
theorem op_04 : Eval c Sym.«op» [int 0, int 4] (some (int 4)) := eval_of_evalAt 20 (by decide +kernel)
/-- The `[owise]` over `op(1, _)` decides at (1, 4). -/
theorem op_14 : Eval c Sym.«op» [int 1, int 4] (some (int 7)) := eval_of_evalAt 20 (by decide +kernel)
/-- No clause matches (2, 4), the `[owise]` included: `op` is undefined there. -/
theorem op_24 : Eval c Sym.«op» [int 2, int 4] none := eval_of_evalAt 20 (by decide +kernel)

/-- At 0 both clauses of priority 50 apply and give 0. -/
theorem ag_0 : Eval c Sym.«ag» [int 0] (some (int 0)) := eval_of_evalAt 20 (by decide +kernel)
theorem ag_0_only {r : Option GroundTerm} (h : Eval c Sym.«ag» [int 0] r) : r = some (int 0) :=
  only_of_evalAt 20 (by decide +kernel) h
theorem ag_3 : Eval c Sym.«ag» [int 3] (some (int 9)) := eval_of_evalAt 20 (by decide +kernel)

/-! ## Steps -/

def ctr0 : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor Sym.«<k>» [.ctor kseq [st, .ctor dotk []]], ctr0]
def cmd (f : Sym) : GroundTerm := .inj Srt.«Cmd» KCore.Srt.kitem (.ctor f [])
def resI (i : Int) : GroundTerm := .ctor Sym.«res» [int i]

/-- `t1` steps to `res(pr(0) +Int pr(3))`, `res(3)`. -/
theorem t1_run : checkRun c 100 (cfg (cmd Sym.«t1»)) [(0, cfg (resI 3))] (cfg (resI 3)) = true := by
  decide +kernel
/-- `t2` steps to `res(ow(-3))`, `res(3)`. -/
theorem t2_run : checkRun c 100 (cfg (cmd Sym.«t2»)) [(1, cfg (resI 3))] (cfg (resI 3)) = true := by
  decide +kernel
/-- `t3` steps to `res(op(1, 4) +Int ag(0))`, `res(7)`. -/
theorem t3_run : checkRun c 100 (cfg (cmd Sym.«t3»)) [(2, cfg (resI 7))] (cfg (resI 7)) = true := by
  decide +kernel

theorem t4_fuel : CExec.outOfFuel (c.withHooks HookParams.none) 100 (cfg (cmd Sym.«t4»)) = false := by
  decide +kernel
theorem t4_none : CExec.successorsN (c.withHooks HookParams.none) 100 (cfg (cmd Sym.«t4»)) = [] := by
  decide +kernel

/-- Under the interpretation that gives nothing, `t4` has no successor: every clause of `ow` fails
at -200, and its rest is undefined there. -/
theorem t4_ends (hf : (c.withHooks HookParams.none).sortOf (cfg (cmd Sym.«t4»)) = some topCellSort) :
    ∀ y, ¬ Step (c.withHooks HookParams.none) ⟨_, hf⟩ y :=
  CExec.noStep_at (by decide +kernel) (fnDet_of_coherent (coherent_withHooks HookParams.none ag_agree)) t4_fuel t4_none

/-- info: 'Fprio.Values.sound_defn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sound_defn

/-- info: 'Fprio.Values.pr_0_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pr_0_only

end Fprio.Values
