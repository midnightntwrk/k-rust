import SimpleEnv.Cases
import KSimple.Init
import KPrelude.InvSteps
import KPrelude.Tactic

/-!
# Every run keeps `Invariant` (kind 2 layout: `Run.lean`)

HAND-WRITTEN, stable under edits of the K rules (it depends on the configuration declaration
only, through the generated `KSimple.init`). `init_holds` is `Invariant` at the initial configuration
for the configuration variables `pgm`, `stdin`, `io`; add the hypotheses on them that it needs (krust accepts any
value of their sorts). `star` and `stepsN` extend it to every configuration reachable from there.
-/

namespace SimpleEnv

open KPrelude

/-- The initial configuration satisfies `Invariant`, for every program and input: its one thread,
`<genv>` and `<store>` are empty, and its computation `$PGM ~> execute` holds no environment. -/
theorem init_holds (pgm : KSimple.SortStmt) (stdin : KSimple.SortString) (io : KSimple.SortString) : Invariant (KSimple.init pgm stdin io) := by
  simp only [Invariant, KSimple.init, ThreadOk, EnvIn, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf, thK, thCtl,
    thEnv, kOf, envOf, ctlF, ctlX, fsOf, xsOf, envsI, envsK, envsC_eq, envsFO, envsXO,
    envsL_unit, envsL_element, envsL_concat, allIn_nil, allIn_cons, allIn_append,
    envsI_inj_Exp, envsI_inj_Exps, envsI_inj_Ids, envsI_inj_Stmt, envsI_inj_Val, envsI_inj_Vals,
    envsI_inj_IOInt, List.nil_append, List.append_nil]
  k2l_coll_close [ThreadOk, EnvIn, topT, tThreads, tGenv, tStore, threadsOf, genvOf, storeOf, thK, thCtl,
    thEnv, kOf, envOf, ctlF, ctlX, fsOf, xsOf, envsI, envsK, envsC_eq, envsFO, envsXO,
    envsL_unit, envsL_element, envsL_concat, allIn_nil, allIn_cons, allIn_append,
    envsI_inj_Exp, envsI_inj_Exps, envsI_inj_Ids, envsI_inj_Stmt, envsI_inj_Val, envsI_inj_Vals,
    envsI_inj_IOInt, List.nil_append, List.append_nil]

/-- Every configuration reachable from the initial configuration satisfies `Invariant`. -/
theorem star {pgm : KSimple.SortStmt} {stdin : KSimple.SortString} {io : KSimple.SortString} {c : KSimple.SortGeneratedTopCell} (h : Star KSimple.Step (KSimple.init pgm stdin io) c) : Invariant c :=
  preserved.star h (init_holds pgm stdin io)

/-- Every configuration reached in `n` steps from the initial configuration satisfies `Invariant`. -/
theorem stepsN {pgm : KSimple.SortStmt} {stdin : KSimple.SortString} {io : KSimple.SortString} {n : Nat} {c : KSimple.SortGeneratedTopCell} (h : StepsN KSimple.Step n (KSimple.init pgm stdin io) c) : Invariant c :=
  preserved.stepsN h (init_holds pgm stdin io)

#k2l_assert_axioms preserved init_holds star stepsN

end SimpleEnv
