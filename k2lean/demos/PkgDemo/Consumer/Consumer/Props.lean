import Consumer.Hooks
import Params.Adequacy
import Params.Init

/-! Statements about the semantics at `hooks`: a generated theorem instantiated, a run, and a
fact about two runs closed by `decide`. -/

namespace Consumer
open Params

attribute [local instance] hooks

/-- A generated theorem, stated for every `Params.Hooks`, at this implementation. -/
theorem step_sound_hex {c c' : SortGeneratedTopCell} (h : step c = .next c') : Step c c' :=
  step_sound h

/-- `hash 0xdead` writes `lengthString(Bytes2Hex(0xdead)) +Int oracle(2) = 4 + 7` into `<out>`. -/
def hashRun : String :=
  toK_SortGeneratedTopCell (run 10 (init (SortStmt.hash_ [0xde, 0xad]))).config

/-- info: "<generatedTop>(<T>(<k>(.K), <out>(11)), <generatedCounter>(0))" -/
#guard_msgs (info, whitespace := lax) in
#eval hashRun

theorem same_out : (run 10 (init (SortStmt.hash_ [0xde, 0xad]))).config =
    (run 10 (init (SortStmt.hash_ [0xbe, 0xef]))).config := by decide

end Consumer
