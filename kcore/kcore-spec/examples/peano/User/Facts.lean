/-
  The decisions peano's witnesses and its guard invariant need (the user's: they are about the
  configurations and the position its statements name). Each is one kernel decision; sorts are read
  from the package's tables (`sortOfT`, `T_eq`).
-/
import User.Statements

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Peano

open KCore

theorem sorted_runSZ : c.sortOf (cfg (run (s z)) ctr0) = some topCellSort :=
  sortOf_of_T T_eq (by decide +kernel)
theorem sorted_runZ : c.sortOf (cfg (run z) ctr0) = some topCellSort :=
  sortOf_of_T T_eq (by decide +kernel)
theorem sorted_doneZ : c.sortOf (cfg (done (natVal z)) ctr0) = some topCellSort :=
  sortOf_of_T T_eq (by decide +kernel)
theorem sorted_doneSZ : c.sortOf (cfg (done (natVal (s z))) ctr0) = some topCellSort :=
  sortOf_of_T T_eq (by decide +kernel)
theorem succ_runSZ : (Exec.successorsN c 100 (cfg (run (s z)) ctr0)).any (Exec.same · (cfg (run z) ctr0)) = true := by
  decide +kernel
theorem succ_runZ :
    (Exec.successorsN c 100 (cfg (run z) ctr0)).any (Exec.same · (cfg (done (natVal z)) ctr0)) = true := by
  decide +kernel
theorem nomatch_doneZ : c.rules.all (fun r =>
    ((Exec.matchP c (Exec.patFuel [r.lhs]) [] r.lhs (cfg (done (natVal z)) ctr0)).filter
      (Exec.wellSorted c r.vars)).isEmpty) = true := by decide +kernel

/-- The first item of the k cell. -/
def kItemPath : Path := kPath ++ [.arg kseq 2 0, .inj KCore.Srt.kitem]
/-- After a step, a `done(_)` at the head of the k cell holds `z` (as a `Val`). -/
def doneGuard : Guard := { path := kItemPath, head := Sym.«done», sub := [.arg Sym.«done» 1 0], val := natVal z }

theorem guardDone : allExcept (guardOK c doneGuard) [] 0 c.rules = true := by decide +kernel

end Peano
