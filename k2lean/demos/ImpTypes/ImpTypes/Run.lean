import ImpTypes.Cases
import KImp.Init
import KPrelude.InvSteps
import KPrelude.Tactic

/-!
# Every run of a well-typed kimp program keeps the runtime typing (kind 2 layout: `Run.lean`)

HAND-WRITTEN, stable under edits of kimp's rules (it depends on the configuration declaration
only, through the generated `KImp.init`). `init_holds` is the invariant at the initial
configuration of program `pgm` and store `env`, under the hypotheses that the program is
well typed and that the store holds a value of the declared type for every typed identifier;
`star` and `stepsN` extend it to every configuration reachable from there.
-/

namespace ImpTypes

open KPrelude

/-- The initial configuration of a well-typed program with a typed store is well typed. -/
theorem init_holds {G : TEnv} (pgm : KImp.SortStmt) (env : KImp.SortMap)
    (h_pgm : wtS G pgm = true) (h_env : envTy G env) : WTc G (KImp.init pgm env) := by
  refine ⟨?_, h_env⟩
  simp [KImp.init, kOf, kty_kseq, item_none, h_pgm, kty_dotk]

/-- Every configuration reachable from the initial configuration is well typed. -/
theorem star {G : TEnv} {pgm : KImp.SortStmt} {env : KImp.SortMap} (h_pgm : wtS G pgm = true)
    (h_env : envTy G env) {c : KImp.SortGeneratedTopCell} (h : Star KImp.Step (KImp.init pgm env) c) :
    WTc G c :=
  (preserved G).star h (init_holds pgm env h_pgm h_env)

/-- Every configuration reached in `n` steps from the initial configuration is well typed. -/
theorem stepsN {G : TEnv} {pgm : KImp.SortStmt} {env : KImp.SortMap} (h_pgm : wtS G pgm = true)
    (h_env : envTy G env) {n : Nat} {c : KImp.SortGeneratedTopCell}
    (h : StepsN KImp.Step n (KImp.init pgm env) c) : WTc G c :=
  (preserved G).stepsN h (init_holds pgm env h_pgm h_env)

#k2l_assert_axioms preserved hand.«CALC.var» hand.«CALC.assign» init_holds star stepsN

end ImpTypes
