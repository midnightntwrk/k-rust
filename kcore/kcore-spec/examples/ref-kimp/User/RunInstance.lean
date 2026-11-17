/-
  One point where the hypothesis of the package's `run_exact` holds, and what the theorem gives
  there, stated without the executor.

  The configuration is `Claims.inst`: the loop of K's claim `sum-spec` before `.K`, with `$n ↦ 3`
  and `$s ↦ 0`, the counter 0. At the fuel 100, for every interpretation `H` of the hooks, the
  executor runs out of nothing (`fuel`) and lists one successor (`succs`), `next`: the loop
  unfolded by the rule `while`, `if (C) { S while (C) S }`. Both are equalities the kernel checks
  by evaluating the executor with `H` a variable: kimp's text declares no symbol that `H`
  interprets, so no evaluation reads it.

  `run_instance` is `RefKimp.run_exact` there, with the list written out. It names `Consistent`,
  `Γ`, `Γstep`, `den`, `allNext`, `sNext` and the two configurations, and nothing of `CExec`:
  under every `H` the theory with the step's closure has a model; with the step's closure every
  successor of `inst` is `next`; and `next` is a successor of `inst` in every model of `Γ`.
-/
import User.SumSpecStmt
import RefKimp.FnHyp

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp.RunInstance

open KCore RefKimp.Syntax
open KCore.Faithful (Γ Γstep)

def body : Tm Srt.«Stmt» :=
  «{_}» («__»
    («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
    («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))

def cond : Tm Srt.«Expr» := «!_» («_<=_» (Tm.ident "$n") (Tm.int 0))

def next : Tm Srt.top :=
  «<generatedTop>»
    («<k>» (Tm.kseq
      («if(_)_» cond («{_}» («__» body («while(_)_» cond body))))
      Tm.dotk))
    («<env>» (Tm.map [(Tm.ident "$n", Tm.int 3), (Tm.ident "$s", Tm.int 0)]))
    («<generatedCounter>» (Tm.int 0))

kernel_rfl fuel : ∀ H : HookParams,
    CExec.outOfFuel (defn.sem.withHooks H) 100 Claims.inst.val = false

kernel_rfl succs : ∀ H : HookParams,
    CExec.successorsN (defn.sem.withHooks H) 100 Claims.inst.val = [next.val]

/-- `Claims.inst` as a configuration under an interpretation. -/
def x (H : HookParams) : Config (defn.sem.withHooks H) := ⟨Claims.inst.val, Claims.instSorted H⟩

theorem run_instance (H : HookParams) :
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) Claims.inst.val ⇒
          KoreAML.allNext (den (defn.sem.withHooks H) next.val))) ∧
      (Γ (defn.sem.withHooks H) ⊧
        (den (defn.sem.withHooks H) Claims.inst.val ⇒
          KoreAML.sNext (den (defn.sem.withHooks H) next.val))) := by
  have h := RefKimp.run_exact H (n := 100) (x := x H) (fuel H)
  rw [show (x H).val = Claims.inst.val from rfl, succs H] at h
  exact ⟨h.1, h.2.1, h.2.2 _ (List.mem_singleton.mpr rfl)⟩

open Lean in
#eval show CoreM Unit from do
  for n in [``run_instance, ``fuel, ``succs] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"
  let some v := (← getEnv).find? ``run_instance | throwError "no statement"
  let cs := v.type.getUsedConstants.toList.map (·.toString)
  if cs.any (·.startsWith "KCore.CExec") then throwError "the statement names the executor: {cs}"

end RefKimp.RunInstance
