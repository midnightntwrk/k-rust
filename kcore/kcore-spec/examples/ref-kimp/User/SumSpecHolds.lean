/-
  K's claim `sum-spec` (imp-semantics, `examples/specs/imp-sum-spec.k`) proved as the consumer's
  statement `Claims.Expected.«sum-spec»` states it (User/SumSpecStmt.lean): for every interpretation
  `H` of the hooks, every complete path of `Step (defn.sem.withHooks H)` from the claim's left side
  passes through its right side, for `N ≥ 0`.

  The run is that of User/SumSpec.lean, each step `fire i` at `defn.sem.withHooks H` with `H` a
  variable: the kernel evaluates the rule's match, `requires` and right-hand side under `H`
  without reading it, since kimp's text declares no symbol that `H` interprets. `loop_runs_withHooks`
  is the induction on `$n`, the claim's circularity, the rest of the k cell growing by the block's
  `{}` each pass. The package's determinism for every `H` (`RefKimp.deterministic`) makes the run
  the only complete path (`Reachability.allPath_of_star`). `sum_spec_kore` is the claim's KORE
  sentence, `Claims.ExpectedKore.«sum-spec»`, from it: the target's counter taken to be the left
  side's. No hypothesis on the functions is used: the check below finds none of `FnHyp`,
  `fnHyp_defn`, `fnHyp_withHooks_defn` among the constants the proofs reach.
-/
import User.SumSpec
import User.SumSpecStmt

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp.Claims

open KCore RefKimp.Syntax
open RefKimp.SumSpec (init cfg tri_step tri_tdiv)

/-- The facts `fire` reads of the definition under an interpretation `H`: those of the data, which
do not read `H`, and the rules' priorities, the same rules under every `H`. -/
instance fireFacts_withHooks_sumHolds (H : HookParams) : FireFacts (defn.sem.withHooks H) :=
  ⟨(Semantics.ok_withHooks _ H).trans ok, (Semantics.srReady_withHooks _ H).trans srReady,
    (Semantics.matchReady_withHooks _ H).trans matchReady, 50, prio_floor⟩

/-- From the loop with `$n ↦ n` and `$s ↦ b` before any rest K of the k cell, under every
interpretation `H`, a run reaches K alone, with `$n ↦ 0` and `$s ↦ b + n(n+1)/2`. The induction
hypothesis is used with the rest `{} ~> K` the iteration leaves. -/
theorem loop_runs_withHooks (H : HookParams) : ∀ (n : Nat) (b : Int) (K C : GroundTerm),
    (defn.sem.withHooks H).sortOf K = some KCore.Srt.k →
    (defn.sem.withHooks H).sortOf C = some KCore.Srt.counter →
    Runs (defn.sem.withHooks H) (init n b K C) (cfg ⟨K⟩ 0 (b + ((n * (n + 1) / 2 : Nat) : Int)) C)
  | 0, b, K, C, hK, hC => by
    fire 69 73 74 26 49 68 13 51 0 27 25  -- the condition, false
    fire 75 78  -- the exit
    rw [show b + ((0 * (0 + 1) / 2 : Nat) : Int) = b by simp]
    run_end
  | n + 1, b, K, C, hK, hC => by
    fire 69 73 74 26 49 68 13 51 0 27 25  -- the condition
    rw [show (!decide (((n + 1 : Nat) : Int) ≤ 0)) = true by simp]
    fire 76 77 72 77 72 70 40 68 7 41 68 8 42 19 71 70 40 68 7 42 19 71 78  -- one iteration
    rw [show ((n + 1 : Nat) : Int) + -1 = n by omega]
    run_by loop_runs_withHooks H n (b + (n + 1 : Nat)) (Tm.kseq «{}» ⟨K⟩).val C (by ksort) hC
    fire 78  -- the outer block's `{}`
    rw [tri_step]
    run_end

/-- **K's claim `sum-spec`, as the consumer's statement states it**: for every interpretation `H`,
`N ≥ 0`, `S`, rest `K` of the k cell and counter `C`, every complete path of the package's step
from the left side passes through the right side. -/
theorem sum_spec_holds : Expected.«sum-spec» := by
  intro H N S ⟨K⟩ C hN
  refine Reachability.allPath_of_star (r := Step (defn.sem.withHooks H))
    (fun _ _ _ h h' => deterministic H h h') fun x hx => ?_
  have hx' : x.val = init N S K («<generatedCounter>» (Tm.int C)).val := hx
  config_sorts hx'
  have hC : (defn.sem.withHooks H).sortOf («<generatedCounter>» (Tm.int C)).val
      = some KCore.Srt.counter := by ksort
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hN
  obtain ⟨y, hy, hs⟩ := loop_runs_withHooks H n S K _ hK hC x hx'
  refine ⟨y, ?_, hs⟩
  rw [hy, tri_tdiv]
  rfl

/-- **K's claim `sum-spec`, as its KORE sentence states it** (`ExpectedKore.«sum-spec»`, the
target's counter existential), from `sum_spec_holds`: the target's counter is the left side's. -/
theorem sum_spec_kore : ExpectedKore.«sum-spec» := fun H N S K C hN =>
  (sum_spec_holds H N S K C hN).mono (fun _ h => h) fun _ h => ⟨C, h⟩

/- The axioms of the theorems are Lean's own, and no constant they reach, through every definition
and proof below them, is a hypothesis on the functions. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let banned := [``KCore.FnHyp, ``RefKimp.fnHyp_defn, ``RefKimp.fnHyp_withHooks_defn]
  for n in [``sum_spec_holds, ``sum_spec_kore, ``loop_runs_withHooks] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"
    let mut seen : NameSet := {}
    let mut todo := [n]
    while !todo.isEmpty do
      let m := todo.head!
      todo := todo.tail!
      if seen.contains m then continue
      seen := seen.insert m
      if banned.contains m then throwError "{n} reaches {m}"
      if let some ci := env.find? m then
        let body : Option Expr := match ci with
          | .thmInfo t => some t.value
          | .defnInfo d => some d.value
          | .opaqueInfo o => some o.value
          | _ => none
        let cs := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
        todo := cs.toList ++ todo
  for n in banned do
    unless env.contains n do throwError "no constant {n}: the check would be vacuous"

end RefKimp.Claims
