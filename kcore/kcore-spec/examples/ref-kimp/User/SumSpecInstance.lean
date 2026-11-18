/-
  K's claim `sum-spec` at one instance of its variables: `N = 3`, `S = 0`, the rest `.K` of the k
  cell and the counter `0`. There the claim's hypothesis `N ≥ 0` holds, and `Claims.inst` (the
  loop before `.K`, `$n ↦ 3`, `$s ↦ 0`), a configuration under every interpretation `H` by
  `Claims.instSorted`, is the statement's left side. From `sum_spec_holds` there, every complete
  path of `Step (defn.sem.withHooks H)` from it passes through the configuration with `.K` alone,
  `$n ↦ 0` and `$s ↦ 6` (`0 + (3 + 1) * 3 / 2`).
-/
import User.SumSpecHolds

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp.Claims

open KCore KCore.Reachability RefKimp.Syntax

/-- The right side at the instance: `.K` alone, `$n ↦ 0`, `$s ↦ 6`, the counter `0`. -/
def instFinal : Tm Srt.top :=
  «<generatedTop>»
    («<k>» Tm.dotk)
    («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0), (Tm.ident "$s", Tm.int 6)]))
    («<generatedCounter>» (Tm.int 0))

/-- `Claims.inst` as a configuration under the interpretation `H`. -/
def instCfg (H : HookParams) : Config (defn.sem.withHooks H) := ⟨inst.val, instSorted H⟩

/-- **The claim at `N = 3`, `S = 0`, `K = .K`, `C = 0`**, under every interpretation `H`: the
hypothesis holds, `Claims.inst` is the statement's left side there, and every complete path from it
passes through `instFinal`. -/
theorem sum_spec_instance (H : HookParams) :
    (3 : Int) ≥ 0 ∧
      (instCfg H).val =
        («<generatedTop>»
          («<k>» (Tm.kseq
            («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
              («{_}» («__»
                («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
            Tm.dotk))
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 3), (Tm.ident "$s", Tm.int 0)]))
          («<generatedCounter>» (Tm.int 0))).val ∧
      ∀ l, CPath (Step (defn.sem.withHooks H)) (instCfg H) l → ∃ z ∈ l, z.val = instFinal.val := by
  refine ⟨by decide, rfl, fun l hl => ?_⟩
  obtain ⟨z, hz, hq⟩ := sum_spec_holds H 3 0 Tm.dotk 0 (by decide) (instCfg H) rfl l hl
  exact ⟨z, hz, hq.trans rfl⟩

open Lean in
#eval show CoreM Unit from do
  let axs ← collectAxioms ``sum_spec_instance
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "sum_spec_instance: axioms {axs}"

end RefKimp.Claims
