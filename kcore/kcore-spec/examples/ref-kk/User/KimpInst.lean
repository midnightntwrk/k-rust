/-
  **C10 is not vacuous at kimp**: the hypotheses of the three statements at `KK.sig` hold of kimp's
  semantics and of one of its configurations, and soundness there gives a step that is named.

  - `encDef_kimp`: `encDef RefKimp.defn.sem = some E₀`, with `E₀` written out (29 subsort pairs,
    20 functions, 79 rules). The kernel evaluates `encDef` on kimp's semantics.
  - `succs_at`: `Eval KK.c₀ 510 [embD E₀, t₀] (some r₀)`: kore.k's `succs` (symbol 510), at its
    member `KK.c₀` (`K₀ sig`, by `rfl`), has the result `r₀` at the definition `E₀` and the term
    `t₀`. The kernel evaluates the checked executor on kore.k's semantics (`succs_run`), and
    `CExec.evalF_sound` makes the result an `Eval`; kore.k's semantics is ready for the executor
    (`c₀_ready`).
  - `step_named`: `Step (RefKimp.defn.sem.withHooks HookParams.none) ⟨x₀, _⟩ ⟨y₀, _⟩`, from
    `succs_sound` at `succs_at`: `t₀` is the encoding of `x₀` as a kore.k value (`t₀_tie`), `r₀` is
    `next` of the list holding the encoding of `y₀` (`r₀_tie`), and a configuration with the
    encoding of `y₀` is `y₀` (`enc_injective`).

  `x₀` is the loop of K's claim `sum-spec` at `N = 3`, `S = 0`, and `y₀` the loop unfolded by the
  rule `while`. The five literals are values written out; the statements of `encDef_kimp`,
  `succs_at` and `step_named` name no encoding of a configuration and no embedding of a term or of
  a result; gen/kimp-inst-lits.sh prints them from kimp's text, and a literal that is not the value
  fails a kernel check here. The module is built over both packages (`gen/build.sh --only --with examples/ref-kimp
  examples/ref-kk User.KimpInst`); of kimp's it imports the generated modules only.
-/
import User.KkThree
import RefKimp.FnHyp

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK.KimpInst

open KCore KCore.KK

/-! ## The definition -/

/-- kimp's semantics in kore.k's form: its subsort pairs, its functions with their clauses and its
rules, each rule a priority, whether it is `owise`, a left side, a `requires` and a right side. -/
def E₀ : D :=
  { subs := [(30, 31),
           (32, 33),
           (37, 34),
           (3, 37),
           (2, 37),
           (9, 34),
           (37, 35),
           (3, 35),
           (3, 34),
           (2, 35),
           (2, 34),
           (4, 1),
           (6, 1),
           (7, 1),
           (5, 1),
           (2, 1),
           (3, 1),
           (9, 1),
           (17, 1),
           (18, 1),
           (30, 1),
           (31, 1),
           (32, 1),
           (33, 1),
           (19, 1),
           (34, 1),
           (35, 1),
           (36, 1),
           (37, 1)],
    fns := [(51,
             [{ prio := 50,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv true }]),
            (52,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.vr 0, T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (55,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 4 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (57,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 6 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (58,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 7 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (56,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 5 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (53,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 2 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (54,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 3 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (59,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 9 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (67,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 17 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (68,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 18 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (380,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 30 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (381,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 31 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (382,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 32 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (383,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 33 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (69,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 19 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (384,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (385,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 35 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (386,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 36 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }]),
            (387,
             [{ prio := 50,
                owise := false,
                pats := [T.ap 0 [T.ij 37 1 (T.vr 0), T.ap 1 []]],
                req := T.bv true,
                rhs := T.bv true },
              { prio := 200,
                owise := false,
                pats := [T.vr 0],
                req := T.bv true,
                rhs := T.bv false }])],
    rules := [{ prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap 0 [T.ap 393 [], T.vr 2]]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.ap 392 [T.vr 0]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap 0 [T.ap 394 [], T.vr 2]]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.ap 419 [T.vr 0]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     395
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 420 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     396
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 420 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     397
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 421 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     398
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 422 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     399
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 422 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     400
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 423 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     401
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 423 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     402
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 424 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     403
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 424 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     404
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 425 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     405
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 425 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     406
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 426 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     407
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 426 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     408
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 427 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     409
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 427 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     410
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 428 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     411
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 428 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     412
                                     [T.ap
                                        0
                                        [T.ij 9 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap 429 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     413
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 430 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     414
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 430 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     415
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 431 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     416
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 431 [T.vr 2, T.vr 0]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     417
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 433 [T.vr 0, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.as (T.ij 34 1 (T.vr 0)) 1,
                                T.ap
                                  0
                                  [T.ap
                                     418
                                     [T.ap
                                        0
                                        [T.ij 36 1 (T.vr 2), T.ap 1 []],
                                      T.ap
                                        0
                                        [T.ij 36 1 (T.vr 3), T.ap 1 []]],
                                   T.vr 4]]],
                          T.vr 5,
                          T.vr 6],
                req := T.hk
                         20
                         [T.bv true,
                          T.ap 385 [T.ap 0 [T.vr 1, T.ap 1 []]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    435
                                    [T.vr 0, T.vr 2, T.vr 3]),
                                T.vr 4]],
                          T.vr 5,
                          T.vr 6] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.ap 392 [T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap 0 [T.ap 393 [], T.vr 1]]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 392 [T.ij 2 34 (T.vr 0)]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 2 1 (T.hk 22 [T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.ap 419 [T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap 0 [T.ap 394 [], T.vr 1]]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 419 [T.ij 3 34 (T.vr 0)]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  3
                                  1
                                  (T.hk 2 [T.iv 0, T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 420 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     395
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 420 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     396
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    420
                                    [T.ij 2 34 (T.vr 0),
                                     T.ij 2 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk
                                    22
                                    [T.hk 23 [T.vr 0, T.vr 1]]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    420
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 15 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 421 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     397
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    421
                                    [T.ij 2 34 (T.as (T.bv false) 0),
                                     T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 2 1 (T.vr 0), T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    421
                                    [T.ij 2 34 (T.bv true), T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 34 1 (T.vr 0), T.vr 1]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 422 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     398
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 422 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     399
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    422
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  3
                                  1
                                  (T.hk 3 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 423 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     400
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 423 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     401
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    423
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  3
                                  1
                                  (T.hk 1 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 424 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     402
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 424 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     403
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    424
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  3
                                  1
                                  (T.hk 2 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 425 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     404
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 425 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     405
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    425
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  3
                                  1
                                  (T.hk 4 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 426 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     406
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 426 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     407
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    426
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 11 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 427 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     408
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 427 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     409
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    427
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 10 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 428 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     410
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 428 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     411
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    428
                                    [T.ij 2 34 (T.vr 0),
                                     T.ij 2 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 23 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    428
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 14 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 430 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     413
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 430 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     414
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    430
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 13 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 431 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     415
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 431 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.hk
                            20
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                             T.bv true],
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     416
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    431
                                    [T.ij 3 34 (T.vr 0),
                                     T.ij 3 34 (T.vr 1)]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  2
                                  1
                                  (T.hk 12 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap 433 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     417
                                     [T.ap
                                        0
                                        [T.ij 34 1 (T.vr 1), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    433
                                    [T.ij 2 34 (T.bv false), T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 34 1 (T.vr 0), T.vr 1]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  34
                                  1
                                  (T.ap
                                    433
                                    [T.ij 2 34 (T.bv true), T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 2 1 (T.bv true), T.vr 1]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 9 1 (T.vr 0), T.vr 1]],
                          T.as
                            (T.ap
                              390
                              [T.cb
                                 (Kind.map)
                                 6
                                 [T.kv
                                    (T.ij 9 1 (T.vr 0))
                                    (T.vr 2),
                                  T.vr 3]])
                            4,
                          T.vr 5],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap 388 [T.ap 0 [T.vr 2, T.vr 1]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.as
                                    (T.ap 436 [T.vr 0, T.vr 1])
                                    2),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    434
                                    [T.vr 0,
                                     T.ap
                                       437
                                       [T.ap 432 [T.vr 1, T.vr 2]]]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap 429 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 1), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 1),
                                T.ap
                                  0
                                  [T.ap
                                     412
                                     [T.ap
                                        0
                                        [T.ij 9 1 (T.vr 0), T.ap 1 []]],
                                   T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    429
                                    [T.vr 0, T.ij 37 34 (T.vr 1)]),
                                T.vr 2]],
                          T.ap 390 [T.vr 3],
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap 388 [T.vr 2],
                          T.ap
                            390
                            [T.hk
                               42
                               [T.vr 3,
                                T.ij 9 1 (T.vr 0),
                                T.ij 37 1 (T.vr 1)]],
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap 432 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 36 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ij 36 1 (T.vr 1), T.vr 2]]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap 434 [T.vr 0, T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    435
                                    [T.vr 0, T.vr 1, T.ap 438 []]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    435
                                    [T.vr 0, T.vr 1, T.vr 2]),
                                T.vr 3]],
                          T.vr 4,
                          T.vr 5],
                req := T.hk
                         20
                         [T.bv true,
                          T.hk
                            22
                            [T.ap
                               385
                               [T.ap
                                  0
                                  [T.ij 34 1 (T.vr 0), T.ap 1 []]]]],
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 34 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ap
                                     418
                                     [T.ap
                                        0
                                        [T.ij 36 1 (T.vr 1), T.ap 1 []],
                                      T.ap
                                        0
                                        [T.ij 36 1 (T.vr 2), T.ap 1 []]],
                                   T.vr 3]]],
                          T.vr 4,
                          T.vr 5] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    435
                                    [T.ij 2 34 (T.bv false),
                                     T.vr 0,
                                     T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 36 1 (T.vr 1), T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij
                                  36
                                  1
                                  (T.ap
                                    435
                                    [T.ij 2 34 (T.bv true),
                                     T.vr 0,
                                     T.vr 1]),
                                T.vr 2]],
                          T.vr 3,
                          T.vr 4],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap 0 [T.ij 36 1 (T.vr 0), T.vr 2]],
                          T.vr 3,
                          T.vr 4] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 36 1 (T.ap 437 [T.vr 0]),
                                T.vr 1]],
                          T.vr 2,
                          T.vr 3],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 36 1 (T.vr 0),
                                T.ap
                                  0
                                  [T.ij 36 1 (T.ap 438 []), T.vr 1]]],
                          T.vr 2,
                          T.vr 3] },
              { prio := 50,
                owise := false,
                lhs := T.ap
                         71
                         [T.ap
                            388
                            [T.ap
                               0
                               [T.ij 36 1 (T.ap 438 []), T.vr 0]],
                          T.vr 1,
                          T.vr 2],
                req := T.bv true,
                rhs := T.ap
                         71
                         [T.ap 388 [T.vr 0], T.vr 1, T.vr 2] }] }

/- **`encDef` has a value at kimp's semantics**, and the value is `E₀`. -/
kernel_rfl encDef_kimp : encDef RefKimp.defn.sem = some E₀

/-! ## The configuration, its successor, and kore.k's argument and result -/

/-- The configuration: `while (!($n <= 0)) { $s = $s + $n; $n = $n + -1; }` before `.K`, with
`$n ↦ 3` and `$s ↦ 0`, the counter 0. -/
def x₀ : GroundTerm :=
  GroundTerm.ctor
  71
  [GroundTerm.ctor
     388
     [GroundTerm.ctor
        0
        [GroundTerm.inj
           36
           1
           (GroundTerm.ctor
             436
             [GroundTerm.ctor
                392
                [GroundTerm.ctor
                   426
                   [GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$n")),
                    GroundTerm.inj 3 34 (GroundTerm.dv 3 (Lit.int 0))]],
              GroundTerm.ctor
                437
                [GroundTerm.ctor
                   432
                   [GroundTerm.ctor
                      429
                      [GroundTerm.dv 9 (Lit.tok "$s"),
                       GroundTerm.ctor
                         423
                         [GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$s")),
                          GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$n"))]],
                    GroundTerm.ctor
                      429
                      [GroundTerm.dv 9 (Lit.tok "$n"),
                       GroundTerm.ctor
                         423
                         [GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$n")),
                          GroundTerm.inj
                            3
                            34
                            (GroundTerm.dv 3 (Lit.int (-1)))]]]]]),
         GroundTerm.ctor 1 []]],
   GroundTerm.ctor
     390
     [GroundTerm.map
        6
        [(GroundTerm.inj 9 1 (GroundTerm.dv 9 (Lit.tok "$n")),
          GroundTerm.inj 3 1 (GroundTerm.dv 3 (Lit.int 3))),
         (GroundTerm.inj 9 1 (GroundTerm.dv 9 (Lit.tok "$s")),
          GroundTerm.inj 3 1 (GroundTerm.dv 3 (Lit.int 0)))]],
   GroundTerm.ctor 73 [GroundTerm.dv 3 (Lit.int 0)]]

/-- The successor: the loop unfolded by the rule `while`, `if (C) { S while (C) S }`, the store and
the counter unchanged. -/
def y₀ : GroundTerm :=
  GroundTerm.ctor
  71
  [GroundTerm.ctor
     388
     [GroundTerm.ctor
        0
        [GroundTerm.inj
           36
           1
           (GroundTerm.ctor
             434
             [GroundTerm.ctor
                392
                [GroundTerm.ctor
                   426
                   [GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$n")),
                    GroundTerm.inj 3 34 (GroundTerm.dv 3 (Lit.int 0))]],
              GroundTerm.ctor
                437
                [GroundTerm.ctor
                   432
                   [GroundTerm.ctor
                      437
                      [GroundTerm.ctor
                         432
                         [GroundTerm.ctor
                            429
                            [GroundTerm.dv 9 (Lit.tok "$s"),
                             GroundTerm.ctor
                               423
                               [GroundTerm.inj
                                  9
                                  34
                                  (GroundTerm.dv 9 (Lit.tok "$s")),
                                GroundTerm.inj
                                  9
                                  34
                                  (GroundTerm.dv 9 (Lit.tok "$n"))]],
                          GroundTerm.ctor
                            429
                            [GroundTerm.dv 9 (Lit.tok "$n"),
                             GroundTerm.ctor
                               423
                               [GroundTerm.inj
                                  9
                                  34
                                  (GroundTerm.dv 9 (Lit.tok "$n")),
                                GroundTerm.inj
                                  3
                                  34
                                  (GroundTerm.dv 3 (Lit.int (-1)))]]]],
                    GroundTerm.ctor
                      436
                      [GroundTerm.ctor
                         392
                         [GroundTerm.ctor
                            426
                            [GroundTerm.inj 9 34 (GroundTerm.dv 9 (Lit.tok "$n")),
                             GroundTerm.inj 3 34 (GroundTerm.dv 3 (Lit.int 0))]],
                       GroundTerm.ctor
                         437
                         [GroundTerm.ctor
                            432
                            [GroundTerm.ctor
                               429
                               [GroundTerm.dv 9 (Lit.tok "$s"),
                                GroundTerm.ctor
                                  423
                                  [GroundTerm.inj
                                     9
                                     34
                                     (GroundTerm.dv 9 (Lit.tok "$s")),
                                   GroundTerm.inj
                                     9
                                     34
                                     (GroundTerm.dv 9 (Lit.tok "$n"))]],
                             GroundTerm.ctor
                               429
                               [GroundTerm.dv 9 (Lit.tok "$n"),
                                GroundTerm.ctor
                                  423
                                  [GroundTerm.inj
                                     9
                                     34
                                     (GroundTerm.dv 9 (Lit.tok "$n")),
                                   GroundTerm.inj
                                     3
                                     34
                                     (GroundTerm.dv 3 (Lit.int (-1)))]]]]]]]]),
         GroundTerm.ctor 1 []]],
   GroundTerm.ctor
     390
     [GroundTerm.map
        6
        [(GroundTerm.inj 9 1 (GroundTerm.dv 9 (Lit.tok "$n")),
          GroundTerm.inj 3 1 (GroundTerm.dv 3 (Lit.int 3))),
         (GroundTerm.inj 9 1 (GroundTerm.dv 9 (Lit.tok "$s")),
          GroundTerm.inj 3 1 (GroundTerm.dv 3 (Lit.int 0)))]],
   GroundTerm.ctor 73 [GroundTerm.dv 3 (Lit.int 0)]]

/-- The configuration as a value of kore.k's sort `Term`. -/
def t₀ : GroundTerm :=
  GroundTerm.ctor
  408
  [GroundTerm.dv 3 (Lit.int 71),
   GroundTerm.ctor
     407
     [GroundTerm.ctor
        408
        [GroundTerm.dv 3 (Lit.int 388),
         GroundTerm.ctor
           407
           [GroundTerm.ctor
              408
              [GroundTerm.dv 3 (Lit.int 0),
               GroundTerm.ctor
                 407
                 [GroundTerm.ctor
                    424
                    [GroundTerm.dv 3 (Lit.int 36),
                     GroundTerm.dv 3 (Lit.int 1),
                     GroundTerm.ctor
                       408
                       [GroundTerm.dv 3 (Lit.int 436),
                        GroundTerm.ctor
                          407
                          [GroundTerm.ctor
                             408
                             [GroundTerm.dv 3 (Lit.int 392),
                              GroundTerm.ctor
                                407
                                [GroundTerm.ctor
                                   408
                                   [GroundTerm.dv 3 (Lit.int 426),
                                    GroundTerm.ctor
                                      407
                                      [GroundTerm.ctor
                                         424
                                         [GroundTerm.dv 3 (Lit.int 9),
                                          GroundTerm.dv 3 (Lit.int 34),
                                          GroundTerm.ctor
                                            443
                                            [GroundTerm.dv 3 (Lit.int 9),
                                             GroundTerm.dv 10 (Lit.tok "$n")]],
                                       GroundTerm.ctor
                                         407
                                         [GroundTerm.ctor
                                            424
                                            [GroundTerm.dv 3 (Lit.int 3),
                                             GroundTerm.dv 3 (Lit.int 34),
                                             GroundTerm.ctor
                                               425
                                               [GroundTerm.dv 3 (Lit.int 0)]],
                                          GroundTerm.ctor 406 []]]],
                                 GroundTerm.ctor 406 []]],
                           GroundTerm.ctor
                             407
                             [GroundTerm.ctor
                                408
                                [GroundTerm.dv 3 (Lit.int 437),
                                 GroundTerm.ctor
                                   407
                                   [GroundTerm.ctor
                                      408
                                      [GroundTerm.dv 3 (Lit.int 432),
                                       GroundTerm.ctor
                                         407
                                         [GroundTerm.ctor
                                            408
                                            [GroundTerm.dv 3 (Lit.int 429),
                                             GroundTerm.ctor
                                               407
                                               [GroundTerm.ctor
                                                  443
                                                  [GroundTerm.dv 3 (Lit.int 9),
                                                   GroundTerm.dv 10 (Lit.tok "$s")],
                                                GroundTerm.ctor
                                                  407
                                                  [GroundTerm.ctor
                                                     408
                                                     [GroundTerm.dv 3 (Lit.int 423),
                                                      GroundTerm.ctor
                                                        407
                                                        [GroundTerm.ctor
                                                           424
                                                           [GroundTerm.dv 3 (Lit.int 9),
                                                            GroundTerm.dv
                                                              3
                                                              (Lit.int 34),
                                                            GroundTerm.ctor
                                                              443
                                                              [GroundTerm.dv
                                                                 3
                                                                 (Lit.int 9),
                                                               GroundTerm.dv
                                                                 10
                                                                 (Lit.tok "$s")]],
                                                         GroundTerm.ctor
                                                           407
                                                           [GroundTerm.ctor
                                                              424
                                                              [GroundTerm.dv
                                                                 3
                                                                 (Lit.int 9),
                                                               GroundTerm.dv
                                                                 3
                                                                 (Lit.int 34),
                                                               GroundTerm.ctor
                                                                 443
                                                                 [GroundTerm.dv
                                                                    3
                                                                    (Lit.int 9),
                                                                  GroundTerm.dv
                                                                    10
                                                                    (Lit.tok "$n")]],
                                                            GroundTerm.ctor 406 []]]],
                                                   GroundTerm.ctor 406 []]]],
                                          GroundTerm.ctor
                                            407
                                            [GroundTerm.ctor
                                               408
                                               [GroundTerm.dv 3 (Lit.int 429),
                                                GroundTerm.ctor
                                                  407
                                                  [GroundTerm.ctor
                                                     443
                                                     [GroundTerm.dv 3 (Lit.int 9),
                                                      GroundTerm.dv 10 (Lit.tok "$n")],
                                                   GroundTerm.ctor
                                                     407
                                                     [GroundTerm.ctor
                                                        408
                                                        [GroundTerm.dv 3 (Lit.int 423),
                                                         GroundTerm.ctor
                                                           407
                                                           [GroundTerm.ctor
                                                              424
                                                              [GroundTerm.dv
                                                                 3
                                                                 (Lit.int 9),
                                                               GroundTerm.dv
                                                                 3
                                                                 (Lit.int 34),
                                                               GroundTerm.ctor
                                                                 443
                                                                 [GroundTerm.dv
                                                                    3
                                                                    (Lit.int 9),
                                                                  GroundTerm.dv
                                                                    10
                                                                    (Lit.tok "$n")]],
                                                            GroundTerm.ctor
                                                              407
                                                              [GroundTerm.ctor
                                                                 424
                                                                 [GroundTerm.dv
                                                                    3
                                                                    (Lit.int 3),
                                                                  GroundTerm.dv
                                                                    3
                                                                    (Lit.int 34),
                                                                  GroundTerm.ctor
                                                                    425
                                                                    [GroundTerm.dv
                                                                       3
                                                                       (Lit.int (-1))]],
                                                               GroundTerm.ctor 406 []]]],
                                                      GroundTerm.ctor 406 []]]],
                                             GroundTerm.ctor 406 []]]],
                                    GroundTerm.ctor 406 []]],
                              GroundTerm.ctor 406 []]]]],
                  GroundTerm.ctor
                    407
                    [GroundTerm.ctor
                       408
                       [GroundTerm.dv 3 (Lit.int 1), GroundTerm.ctor 406 []],
                     GroundTerm.ctor 406 []]]],
            GroundTerm.ctor 406 []]],
      GroundTerm.ctor
        407
        [GroundTerm.ctor
           408
           [GroundTerm.dv 3 (Lit.int 390),
            GroundTerm.ctor
              407
              [GroundTerm.ctor
                 416
                 [GroundTerm.ctor 429 [],
                  GroundTerm.dv 3 (Lit.int 6),
                  GroundTerm.ctor
                    407
                    [GroundTerm.ctor
                       426
                       [GroundTerm.ctor
                          424
                          [GroundTerm.dv 3 (Lit.int 9),
                           GroundTerm.dv 3 (Lit.int 1),
                           GroundTerm.ctor
                             443
                             [GroundTerm.dv 3 (Lit.int 9),
                              GroundTerm.dv 10 (Lit.tok "$n")]],
                        GroundTerm.ctor
                          424
                          [GroundTerm.dv 3 (Lit.int 3),
                           GroundTerm.dv 3 (Lit.int 1),
                           GroundTerm.ctor 425 [GroundTerm.dv 3 (Lit.int 3)]]],
                     GroundTerm.ctor
                       407
                       [GroundTerm.ctor
                          426
                          [GroundTerm.ctor
                             424
                             [GroundTerm.dv 3 (Lit.int 9),
                              GroundTerm.dv 3 (Lit.int 1),
                              GroundTerm.ctor
                                443
                                [GroundTerm.dv 3 (Lit.int 9),
                                 GroundTerm.dv 10 (Lit.tok "$s")]],
                           GroundTerm.ctor
                             424
                             [GroundTerm.dv 3 (Lit.int 3),
                              GroundTerm.dv 3 (Lit.int 1),
                              GroundTerm.ctor 425 [GroundTerm.dv 3 (Lit.int 0)]]],
                        GroundTerm.ctor 406 []]]],
               GroundTerm.ctor 406 []]],
         GroundTerm.ctor
           407
           [GroundTerm.ctor
              408
              [GroundTerm.dv 3 (Lit.int 73),
               GroundTerm.ctor
                 407
                 [GroundTerm.ctor 425 [GroundTerm.dv 3 (Lit.int 0)],
                  GroundTerm.ctor 406 []]],
            GroundTerm.ctor 406 []]]]]

/-- kore.k's result: `next` of the one-element list holding the successor as a `Term`. -/
def r₀ : GroundTerm :=
  GroundTerm.ctor
  430
  [GroundTerm.ctor
     407
     [GroundTerm.ctor
        408
        [GroundTerm.dv 3 (Lit.int 71),
         GroundTerm.ctor
           407
           [GroundTerm.ctor
              408
              [GroundTerm.dv 3 (Lit.int 388),
               GroundTerm.ctor
                 407
                 [GroundTerm.ctor
                    408
                    [GroundTerm.dv 3 (Lit.int 0),
                     GroundTerm.ctor
                       407
                       [GroundTerm.ctor
                          424
                          [GroundTerm.dv 3 (Lit.int 36),
                           GroundTerm.dv 3 (Lit.int 1),
                           GroundTerm.ctor
                             408
                             [GroundTerm.dv 3 (Lit.int 434),
                              GroundTerm.ctor
                                407
                                [GroundTerm.ctor
                                   408
                                   [GroundTerm.dv 3 (Lit.int 392),
                                    GroundTerm.ctor
                                      407
                                      [GroundTerm.ctor
                                         408
                                         [GroundTerm.dv 3 (Lit.int 426),
                                          GroundTerm.ctor
                                            407
                                            [GroundTerm.ctor
                                               424
                                               [GroundTerm.dv 3 (Lit.int 9),
                                                GroundTerm.dv 3 (Lit.int 34),
                                                GroundTerm.ctor
                                                  443
                                                  [GroundTerm.dv 3 (Lit.int 9),
                                                   GroundTerm.dv 10 (Lit.tok "$n")]],
                                             GroundTerm.ctor
                                               407
                                               [GroundTerm.ctor
                                                  424
                                                  [GroundTerm.dv 3 (Lit.int 3),
                                                   GroundTerm.dv 3 (Lit.int 34),
                                                   GroundTerm.ctor
                                                     425
                                                     [GroundTerm.dv 3 (Lit.int 0)]],
                                                GroundTerm.ctor 406 []]]],
                                       GroundTerm.ctor 406 []]],
                                 GroundTerm.ctor
                                   407
                                   [GroundTerm.ctor
                                      408
                                      [GroundTerm.dv 3 (Lit.int 437),
                                       GroundTerm.ctor
                                         407
                                         [GroundTerm.ctor
                                            408
                                            [GroundTerm.dv 3 (Lit.int 432),
                                             GroundTerm.ctor
                                               407
                                               [GroundTerm.ctor
                                                  408
                                                  [GroundTerm.dv 3 (Lit.int 437),
                                                   GroundTerm.ctor
                                                     407
                                                     [GroundTerm.ctor
                                                        408
                                                        [GroundTerm.dv 3 (Lit.int 432),
                                                         GroundTerm.ctor
                                                           407
                                                           [GroundTerm.ctor
                                                              408
                                                              [GroundTerm.dv
                                                                 3
                                                                 (Lit.int 429),
                                                               GroundTerm.ctor
                                                                 407
                                                                 [GroundTerm.ctor
                                                                    443
                                                                    [GroundTerm.dv
                                                                       3
                                                                       (Lit.int 9),
                                                                     GroundTerm.dv
                                                                       10
                                                                       (Lit.tok "$s")],
                                                                  GroundTerm.ctor
                                                                    407
                                                                    [GroundTerm.ctor
                                                                       408
                                                                       [GroundTerm.dv
                                                                          3
                                                                          (Lit.int 423),
                                                                        GroundTerm.ctor
                                                                          407
                                                                          [GroundTerm.ctor
                                                                             424
                                                                             [GroundTerm.dv
                                                                                3
                                                                                (Lit.int 9),
                                                                              GroundTerm.dv
                                                                                3
                                                                                (Lit.int 34),
                                                                              GroundTerm.ctor
                                                                                443
                                                                                [GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     9),
                                                                                 GroundTerm.dv
                                                                                   10
                                                                                   (Lit.tok
                                                                                     "$s")]],
                                                                           GroundTerm.ctor
                                                                             407
                                                                             [GroundTerm.ctor
                                                                                424
                                                                                [GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     9),
                                                                                 GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     34),
                                                                                 GroundTerm.ctor
                                                                                   443
                                                                                   [GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        9),
                                                                                    GroundTerm.dv
                                                                                      10
                                                                                      (Lit.tok
                                                                                        "$n")]],
                                                                              GroundTerm.ctor
                                                                                406
                                                                                []]]],
                                                                     GroundTerm.ctor
                                                                       406
                                                                       []]]],
                                                            GroundTerm.ctor
                                                              407
                                                              [GroundTerm.ctor
                                                                 408
                                                                 [GroundTerm.dv
                                                                    3
                                                                    (Lit.int 429),
                                                                  GroundTerm.ctor
                                                                    407
                                                                    [GroundTerm.ctor
                                                                       443
                                                                       [GroundTerm.dv
                                                                          3
                                                                          (Lit.int 9),
                                                                        GroundTerm.dv
                                                                          10
                                                                          (Lit.tok "$n")],
                                                                     GroundTerm.ctor
                                                                       407
                                                                       [GroundTerm.ctor
                                                                          408
                                                                          [GroundTerm.dv
                                                                             3
                                                                             (Lit.int 423),
                                                                           GroundTerm.ctor
                                                                             407
                                                                             [GroundTerm.ctor
                                                                                424
                                                                                [GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     9),
                                                                                 GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     34),
                                                                                 GroundTerm.ctor
                                                                                   443
                                                                                   [GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        9),
                                                                                    GroundTerm.dv
                                                                                      10
                                                                                      (Lit.tok
                                                                                        "$n")]],
                                                                              GroundTerm.ctor
                                                                                407
                                                                                [GroundTerm.ctor
                                                                                   424
                                                                                   [GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        3),
                                                                                    GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        34),
                                                                                    GroundTerm.ctor
                                                                                      425
                                                                                      [GroundTerm.dv
                                                                                         3
                                                                                         (Lit.int
                                                                                           (-1))]],
                                                                                 GroundTerm.ctor
                                                                                   406
                                                                                   []]]],
                                                                        GroundTerm.ctor
                                                                          406
                                                                          []]]],
                                                               GroundTerm.ctor 406 []]]],
                                                      GroundTerm.ctor 406 []]],
                                                GroundTerm.ctor
                                                  407
                                                  [GroundTerm.ctor
                                                     408
                                                     [GroundTerm.dv 3 (Lit.int 436),
                                                      GroundTerm.ctor
                                                        407
                                                        [GroundTerm.ctor
                                                           408
                                                           [GroundTerm.dv
                                                              3
                                                              (Lit.int 392),
                                                            GroundTerm.ctor
                                                              407
                                                              [GroundTerm.ctor
                                                                 408
                                                                 [GroundTerm.dv
                                                                    3
                                                                    (Lit.int 426),
                                                                  GroundTerm.ctor
                                                                    407
                                                                    [GroundTerm.ctor
                                                                       424
                                                                       [GroundTerm.dv
                                                                          3
                                                                          (Lit.int 9),
                                                                        GroundTerm.dv
                                                                          3
                                                                          (Lit.int 34),
                                                                        GroundTerm.ctor
                                                                          443
                                                                          [GroundTerm.dv
                                                                             3
                                                                             (Lit.int 9),
                                                                           GroundTerm.dv
                                                                             10
                                                                             (Lit.tok "$n")]],
                                                                     GroundTerm.ctor
                                                                       407
                                                                       [GroundTerm.ctor
                                                                          424
                                                                          [GroundTerm.dv
                                                                             3
                                                                             (Lit.int 3),
                                                                           GroundTerm.dv
                                                                             3
                                                                             (Lit.int 34),
                                                                           GroundTerm.ctor
                                                                             425
                                                                             [GroundTerm.dv
                                                                                3
                                                                                (Lit.int 0)]],
                                                                        GroundTerm.ctor
                                                                          406
                                                                          []]]],
                                                               GroundTerm.ctor 406 []]],
                                                         GroundTerm.ctor
                                                           407
                                                           [GroundTerm.ctor
                                                              408
                                                              [GroundTerm.dv
                                                                 3
                                                                 (Lit.int 437),
                                                               GroundTerm.ctor
                                                                 407
                                                                 [GroundTerm.ctor
                                                                    408
                                                                    [GroundTerm.dv
                                                                       3
                                                                       (Lit.int 432),
                                                                     GroundTerm.ctor
                                                                       407
                                                                       [GroundTerm.ctor
                                                                          408
                                                                          [GroundTerm.dv
                                                                             3
                                                                             (Lit.int 429),
                                                                           GroundTerm.ctor
                                                                             407
                                                                             [GroundTerm.ctor
                                                                                443
                                                                                [GroundTerm.dv
                                                                                   3
                                                                                   (Lit.int
                                                                                     9),
                                                                                 GroundTerm.dv
                                                                                   10
                                                                                   (Lit.tok
                                                                                     "$s")],
                                                                              GroundTerm.ctor
                                                                                407
                                                                                [GroundTerm.ctor
                                                                                   408
                                                                                   [GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        423),
                                                                                    GroundTerm.ctor
                                                                                      407
                                                                                      [GroundTerm.ctor
                                                                                         424
                                                                                         [GroundTerm.dv
                                                                                            3
                                                                                            (Lit.int
                                                                                              9),
                                                                                          GroundTerm.dv
                                                                                            3
                                                                                            (Lit.int
                                                                                              34),
                                                                                          GroundTerm.ctor
                                                                                            443
                                                                                            [GroundTerm.dv
                                                                                               3
                                                                                               (Lit.int
                                                                                                 9),
                                                                                             GroundTerm.dv
                                                                                               10
                                                                                               (Lit.tok
                                                                                                 "$s")]],
                                                                                       GroundTerm.ctor
                                                                                         407
                                                                                         [GroundTerm.ctor
                                                                                            424
                                                                                            [GroundTerm.dv
                                                                                               3
                                                                                               (Lit.int
                                                                                                 9),
                                                                                             GroundTerm.dv
                                                                                               3
                                                                                               (Lit.int
                                                                                                 34),
                                                                                             GroundTerm.ctor
                                                                                               443
                                                                                               [GroundTerm.dv
                                                                                                  3
                                                                                                  (Lit.int
                                                                                                    9),
                                                                                                GroundTerm.dv
                                                                                                  10
                                                                                                  (Lit.tok
                                                                                                    "$n")]],
                                                                                          GroundTerm.ctor
                                                                                            406
                                                                                            []]]],
                                                                                 GroundTerm.ctor
                                                                                   406
                                                                                   []]]],
                                                                        GroundTerm.ctor
                                                                          407
                                                                          [GroundTerm.ctor
                                                                             408
                                                                             [GroundTerm.dv
                                                                                3
                                                                                (Lit.int 429),
                                                                              GroundTerm.ctor
                                                                                407
                                                                                [GroundTerm.ctor
                                                                                   443
                                                                                   [GroundTerm.dv
                                                                                      3
                                                                                      (Lit.int
                                                                                        9),
                                                                                    GroundTerm.dv
                                                                                      10
                                                                                      (Lit.tok
                                                                                        "$n")],
                                                                                 GroundTerm.ctor
                                                                                   407
                                                                                   [GroundTerm.ctor
                                                                                      408
                                                                                      [GroundTerm.dv
                                                                                         3
                                                                                         (Lit.int
                                                                                           423),
                                                                                       GroundTerm.ctor
                                                                                         407
                                                                                         [GroundTerm.ctor
                                                                                            424
                                                                                            [GroundTerm.dv
                                                                                               3
                                                                                               (Lit.int
                                                                                                 9),
                                                                                             GroundTerm.dv
                                                                                               3
                                                                                               (Lit.int
                                                                                                 34),
                                                                                             GroundTerm.ctor
                                                                                               443
                                                                                               [GroundTerm.dv
                                                                                                  3
                                                                                                  (Lit.int
                                                                                                    9),
                                                                                                GroundTerm.dv
                                                                                                  10
                                                                                                  (Lit.tok
                                                                                                    "$n")]],
                                                                                          GroundTerm.ctor
                                                                                            407
                                                                                            [GroundTerm.ctor
                                                                                               424
                                                                                               [GroundTerm.dv
                                                                                                  3
                                                                                                  (Lit.int
                                                                                                    3),
                                                                                                GroundTerm.dv
                                                                                                  3
                                                                                                  (Lit.int
                                                                                                    34),
                                                                                                GroundTerm.ctor
                                                                                                  425
                                                                                                  [GroundTerm.dv
                                                                                                     3
                                                                                                     (Lit.int
                                                                                                       (-1))]],
                                                                                             GroundTerm.ctor
                                                                                               406
                                                                                               []]]],
                                                                                    GroundTerm.ctor
                                                                                      406
                                                                                      []]]],
                                                                           GroundTerm.ctor
                                                                             406
                                                                             []]]],
                                                                  GroundTerm.ctor 406 []]],
                                                            GroundTerm.ctor 406 []]]],
                                                   GroundTerm.ctor 406 []]]],
                                          GroundTerm.ctor 406 []]],
                                    GroundTerm.ctor 406 []]]]],
                        GroundTerm.ctor
                          407
                          [GroundTerm.ctor
                             408
                             [GroundTerm.dv 3 (Lit.int 1),
                              GroundTerm.ctor 406 []],
                           GroundTerm.ctor 406 []]]],
                  GroundTerm.ctor 406 []]],
            GroundTerm.ctor
              407
              [GroundTerm.ctor
                 408
                 [GroundTerm.dv 3 (Lit.int 390),
                  GroundTerm.ctor
                    407
                    [GroundTerm.ctor
                       416
                       [GroundTerm.ctor 429 [],
                        GroundTerm.dv 3 (Lit.int 6),
                        GroundTerm.ctor
                          407
                          [GroundTerm.ctor
                             426
                             [GroundTerm.ctor
                                424
                                [GroundTerm.dv 3 (Lit.int 9),
                                 GroundTerm.dv 3 (Lit.int 1),
                                 GroundTerm.ctor
                                   443
                                   [GroundTerm.dv 3 (Lit.int 9),
                                    GroundTerm.dv 10 (Lit.tok "$n")]],
                              GroundTerm.ctor
                                424
                                [GroundTerm.dv 3 (Lit.int 3),
                                 GroundTerm.dv 3 (Lit.int 1),
                                 GroundTerm.ctor
                                   425
                                   [GroundTerm.dv 3 (Lit.int 3)]]],
                           GroundTerm.ctor
                             407
                             [GroundTerm.ctor
                                426
                                [GroundTerm.ctor
                                   424
                                   [GroundTerm.dv 3 (Lit.int 9),
                                    GroundTerm.dv 3 (Lit.int 1),
                                    GroundTerm.ctor
                                      443
                                      [GroundTerm.dv 3 (Lit.int 9),
                                       GroundTerm.dv 10 (Lit.tok "$s")]],
                                 GroundTerm.ctor
                                   424
                                   [GroundTerm.dv 3 (Lit.int 3),
                                    GroundTerm.dv 3 (Lit.int 1),
                                    GroundTerm.ctor
                                      425
                                      [GroundTerm.dv 3 (Lit.int 0)]]],
                              GroundTerm.ctor 406 []]]],
                     GroundTerm.ctor 406 []]],
               GroundTerm.ctor
                 407
                 [GroundTerm.ctor
                    408
                    [GroundTerm.dv 3 (Lit.int 73),
                     GroundTerm.ctor
                       407
                       [GroundTerm.ctor 425 [GroundTerm.dv 3 (Lit.int 0)],
                        GroundTerm.ctor 406 []]],
                  GroundTerm.ctor 406 []]]]],
      GroundTerm.ctor 406 []]]

/- `x₀` and `y₀` are configurations of kimp at the interpretation that gives nothing. -/
kernel_rfl x₀_sorted : (RefKimp.defn.sem.withHooks HookParams.none).sortOf x₀ = some topCellSort
kernel_rfl y₀_sorted : (RefKimp.defn.sem.withHooks HookParams.none).sortOf y₀ = some topCellSort

/- `t₀` is the encoding of `x₀`, as a kore.k value. -/
kernel_rfl t₀_tie : emb (enc x₀) = t₀

/- `r₀` is `next` of the list whose one element is the encoding of `y₀`, as a kore.k value. -/
kernel_rfl r₀_tie : embSt (.next [enc y₀]) = r₀

/-! ## kore.k's `succs`, evaluated -/

/-- kore.k's semantics is ready for the checked executor. -/
theorem c₀_ready : CExec.execReady _root_.KK.c₀ = true := by decide +kernel

/- The executor's result at `succs`, `E₀` and `t₀`. -/
kernel_rfl succs_run : CExec.evalF _root_.KK.c₀ 100000 510 [embD E₀, t₀] = some (some r₀)

/-- The arguments have the sorts `succs` takes, `Def` and `Term`. -/
theorem succs_args : _root_.KK.c₀.sortsOf [embD E₀, t₀] = some WalkR.succsDef_krw.args := by
  have h1 := embD_sorted_c₀ E₀
  have h2 := emb_sorted_c₀ (enc x₀)
  rw [t₀_tie] at h2
  simp only [Semantics.sortsOf, h1, h2]
  rfl

/-- **kore.k's `succs` at `E₀` and `t₀` has the result `r₀`.** -/
theorem succs_at : Eval _root_.KK.c₀ 510 [embD E₀, t₀] (some r₀) :=
  have h := CExec.execReady_parts c₀_ready
  CExec.evalF_sound h.2.1 h.2.2.1 h.2.2.2.1 _ succs_run WalkR.succsDef_lookup_krw succs_args

/-! ## The step -/

/-- **`y₀` is a successor of `x₀`**: `succs_sound` at `succs_at`. -/
theorem step_named :
    Step (RefKimp.defn.sem.withHooks HookParams.none) ⟨x₀, x₀_sorted⟩ ⟨y₀, y₀_sorted⟩ := by
  have h : SuccsAt sig E₀ x₀ (some (embSt (.next [enc y₀]))) := by
    show Eval _root_.KK.c₀ 510 [embD E₀, emb (enc x₀)] (some (embSt (.next [enc y₀])))
    rw [t₀_tie, r₀_tie]
    exact succs_at
  obtain ⟨y, hy, hst⟩ := succs_sound RefKimp.exec_ready encDef_kimp
    (⟨x₀, x₀_sorted⟩ : Config (d₀ RefKimp.defn.sem)) h (List.mem_cons_self ..)
  have e : y = ⟨y₀, y₀_sorted⟩ := enc_injective encDef_kimp hy
  rw [e] at hst
  exact hst

/-! ## Checks -/

example : K₀ sig = _root_.KK.c₀ := rfl
example : sig.succs = 510 := rfl
example : d₀ RefKimp.defn.sem = RefKimp.defn.sem.withHooks HookParams.none := rfl

#check @encDef_kimp
#check @succs_at
#check @step_named

open Lean in
#eval show CoreM Unit from do
  for n in [``encDef_kimp, ``succs_at, ``step_named, ``x₀_sorted, ``y₀_sorted, ``t₀_tie, ``r₀_tie] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"
  -- the three statements name no encoding and no embedding of a term or a result
  let env ← getEnv
  for n in [``encDef_kimp, ``succs_at, ``step_named] do
    let some ci := env.find? n | throwError "no {n}"
    let cs := ci.type.getUsedConstants
    for b in [``KCore.KK.enc, ``KCore.KK.emb, ``KCore.KK.embSt] do
      if cs.contains b then throwError "{n} names {b}"
  IO.println "kimp instance: encDef_kimp, succs_at, step_named within propext, Classical.choice, Quot.sound"

end KCore.KK.KimpInst
