import ImpWrites.Cases
import KImp.Init
import KPrelude.InvSteps
import KPrelude.Tactic

/-! A run of a program that does not assign `x`, from a store with no value that does, never
assigns `x`. -/

namespace ImpWrites

open KPrelude

/-- The initial configuration satisfies `Invariant x` when the program does not assign `x` and no
value of the initial store does. -/
theorem init_holds (x : KImp.SortId) (pgm : KImp.SortStmt) (env : KImp.SortMap)
    (h_pgm : writesS x pgm = false) (h_env : MapHook.EntriesOn (fun p => writesI x p.2 = false) env) :
    Invariant x (KImp.init pgm env) := by
  simp [Invariant, KImp.init, kOf, kContent, envOf, envContent, writesK, writesI, h_pgm, h_env]

/-- Every configuration reachable from the initial configuration satisfies `Invariant x`. -/
theorem star {x : KImp.SortId} {pgm : KImp.SortStmt} {env : KImp.SortMap}
    (h_pgm : writesS x pgm = false) (h_env : MapHook.EntriesOn (fun p => writesI x p.2 = false) env)
    {c : KImp.SortGeneratedTopCell} (h : Star KImp.Step (KImp.init pgm env) c) : Invariant x c :=
  (preserved x).star h (init_holds x pgm env h_pgm h_env)

#k2l_assert_axioms preserved init_holds star

end ImpWrites
