/-
  The statements of row imp, pinned on the package `kcore gen --wf` writes for kimp read from
  kompile's own KORE (examples/ref-kimp/RefKimp/definition.kore): the types of `consistent`,
  `sound_at`, `complete_at` and `run_exact`, each checked by its proof term at the type written
  out. Each is stated for every interpretation `H` of the hooks, concludes `Consistent` of the
  semantics under `H` (alone, or beside its entailments), and has no hypothesis on the functions:
  `sound_at` takes a step, `complete_at` `StepDecided` at the configuration and a list holding its
  successors, `run_exact` a fuel at which nothing ran out. `sound_hyp` and `complete_hyp` stay
  stated with `FnHyp` as their hypothesis. Their axioms are exactly `propext`, `Classical.choice`,
  `Quot.sound`. The consumer's statement (DONE-0 C9 part 5), `Claims.Expected.«sum-spec»`, written
  from K's claim `sum-spec` before any generator ran (examples/ref-kimp/User/SumSpecStmt.lean,
  which pins-kimp.sh builds over the generated package), is pinned by its body, and so is
  `Claims.ExpectedKore.«sum-spec»`, the statement of the claim's KORE sentence (the same with the
  target's counter existential). The statement `k2lean kcore-claims` writes from that sentence,
  `Claims.Generated.«sum-spec»` (examples/ref-kimp/User/SumSpecGen.lean), is `ExpectedKore.«sum-spec»`
  by `rfl`, and `Expected.«sum-spec»` implies `ExpectedKore.«sum-spec»` (`AllPath.mono`, the target's
  counter taken to be the left side's). `Expected.«sum-spec»` is proved (`Claims.sum_spec_holds`,
  User/SumSpecHolds.lean), and its matching-logic corollaries are pinned by their types
  (User/SumSpecML.lean): `stepDecided_all`, `complete_at`'s hypothesis at every configuration;
  `sum_spec_ml` (reach); `sum_spec_ml_closure` and `sum_spec_ml_stuck` (closure). The claim at one
  concrete initial configuration (User/SumSpecInstance.lean), `sum_spec_instance`, is pinned by its
  type with the configurations written out: at `N = 3`, `S = 0`, `K = .K`, `C = 0` the hypothesis
  `N ≥ 0` holds, the configuration `instCfg H` is the statement's left side there, and every
  complete path from it passes through the right side there; its axioms are exactly Lean's three.
  test/pins-kimp.sh generates the package under the namespace `RefKimp` into .lake/pins/kimp,
  builds it and checks this file against it:

      gen/gen.sh examples/ref-kimp/RefKimp/definition.kore .lake/pins/kimp RefKimp --wf
      gen/build.sh .lake/pins/kimp User.SumSpecStmt User.SumSpecGen User.SumSpec User.SumSpecHolds User.SumSpecML User.SumSpecInstance
      LEAN_PATH=.lake/pins/kimp/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/PinsKimp.lean
-/
import RefKimp.Sound
import RefKimp.FnHyp
import User.SumSpecStmt
import User.SumSpecGen
import User.SumSpecML
import User.SumSpecInstance

set_option autoImplicit false

namespace RefKimp.Pins

open KCore RefKimp
open KCore.Faithful (Γ Γstep)

example : ∀ H : HookParams, Consistent (defn.sem.withHooks H) := consistent

example : ∀ (H : HookParams) (x y : Config (defn.sem.withHooks H))
    (_hs : Step (defn.sem.withHooks H) x y),
    Consistent (defn.sem.withHooks H) ∧
      (Γ (defn.sem.withHooks H) ⊧
        (den (defn.sem.withHooks H) x.val ⇒ KoreAML.sNext (den (defn.sem.withHooks H) y.val))) :=
  sound_at

example : ∀ (H : HookParams) (x : Config (defn.sem.withHooks H))
    (_hd : StepDecided (defn.sem.withHooks H) x.val) (ys : List GroundTerm)
    (_hys : ∀ y : Config (defn.sem.withHooks H), Step (defn.sem.withHooks H) x y → y.val ∈ ys),
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) x.val ⇒
          KoreAML.allNext (KoreAML.disjList (ys.map (den (defn.sem.withHooks H)))))) :=
  complete_at

example : ∀ (H : HookParams) {n : Nat} {x : Config (defn.sem.withHooks H)}
    (_hfu : CExec.outOfFuel (defn.sem.withHooks H) n x.val = false),
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) x.val ⇒ KoreAML.allNext (KoreAML.disjList
          ((CExec.successorsN (defn.sem.withHooks H) n x.val).map (den (defn.sem.withHooks H)))))) ∧
      ∀ y ∈ CExec.successorsN (defn.sem.withHooks H) n x.val,
        (Γ (defn.sem.withHooks H) ⊧
          (den (defn.sem.withHooks H) x.val ⇒ KoreAML.sNext (den (defn.sem.withHooks H) y))) :=
  @run_exact

example : FnHyp defn.sem → SoundC defn.sem := sound_hyp

example : ∀ ref : OutFn, FnHyp defn.sem → CompleteC defn.sem ref := complete_hyp

open KCore.Reachability RefKimp.Syntax in
/-- The consumer's statement: for every H, every complete path of the package's `Step` from the
claim's left side passes through its right side, for `N ≥ 0`. -/
example : Claims.Expected.«sum-spec» =
    ∀ (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (_hreq : N ≥ 0),
      AllPath (Step (defn.sem.withHooks H))
        (fun x => x.val =
          («<generatedTop>»
            («<k>» (Tm.kseq
              («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
                («{_}» («__»
                  («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                  («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
              K))
            («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
            («<generatedCounter>» (Tm.int C))).val)
        (fun z => z.val =
          («<generatedTop>»
            («<k>» K)
            («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0),
              (Tm.ident "$s", Tm.int (S + ((N + 1) * N).tdiv 2))]))
            («<generatedCounter>» (Tm.int C))).val) := rfl

open KCore.Reachability RefKimp.Syntax in
/-- The statement of the claim's KORE sentence: the same, with the target's counter existential. -/
example : Claims.ExpectedKore.«sum-spec» =
    ∀ (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (_hreq : N ≥ 0),
      AllPath (Step (defn.sem.withHooks H))
        (fun x => x.val =
          («<generatedTop>»
            («<k>» (Tm.kseq
              («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
                («{_}» («__»
                  («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                  («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
              K))
            («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
            («<generatedCounter>» (Tm.int C))).val)
        (fun z => ∃ C' : Int, z.val =
          («<generatedTop>»
            («<k>» K)
            («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0),
              (Tm.ident "$s", Tm.int (S + ((N + 1) * N).tdiv 2))]))
            («<generatedCounter>» (Tm.int C'))).val) := rfl

/-- The generated statement is the statement of the claim's KORE sentence. -/
example : Claims.Generated.«sum-spec» = Claims.ExpectedKore.«sum-spec» := rfl

/-- The pinned statement implies the statement of the claim's KORE sentence: the target's counter is
the left side's. -/
example : Claims.Expected.«sum-spec» → Claims.ExpectedKore.«sum-spec» :=
  fun h H N S K C hreq => (h H N S K C hreq).mono (fun _ hx => hx) (fun _ hz => ⟨C, hz⟩)

/-- The claim proved at every interpretation, with no hypothesis on the functions
(examples/ref-kimp/User/SumSpecHolds.lean). -/
example : Claims.Expected.«sum-spec» := Claims.sum_spec_holds

/-- `complete_at`'s hypothesis at every configuration, under every interpretation
(examples/ref-kimp/User/SumSpecML.lean). -/
example : ∀ (H : HookParams) (x : Config (defn.sem.withHooks H)),
    StepDecided (defn.sem.withHooks H) x.val :=
  stepDecided_all

open RefKimp.Syntax in
/-- The claim in matching logic, (reach): from the left side, `Γ` has a model and entails that the
right side is reached, `⟦x⟧ → eventually ⟦y⟧`. -/
example : ∀ (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (_hN : N ≥ 0)
    (x : Config (defn.sem.withHooks H))
    (_hx : x.val =
      («<generatedTop>»
        («<k>» (Tm.kseq
          («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
            («{_}» («__»
              («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
              («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
          K))
        («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
        («<generatedCounter>» (Tm.int C))).val),
    ∃ y : Config (defn.sem.withHooks H),
      y.val =
        («<generatedTop>»
          («<k>» K)
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0),
            (Tm.ident "$s", Tm.int (S + ((N + 1) * N).tdiv 2))]))
          («<generatedCounter>» (Tm.int C))).val ∧
      Consistent (defn.sem.withHooks H) ∧
      (Γ (defn.sem.withHooks H) ⊧
        (den (defn.sem.withHooks H) x.val ⇒ eventually (den (defn.sem.withHooks H) y.val))) :=
  Claims.sum_spec_ml

/-- (closure), at a configuration with a successor: with the step's closure, every successor of `u`
is `Step`'s successor `v`. -/
example : ∀ (H : HookParams) (u v : Config (defn.sem.withHooks H))
    (_huv : Step (defn.sem.withHooks H) u v),
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) u.val ⇒
          KoreAML.allNext (KoreAML.disjList [den (defn.sem.withHooks H) v.val]))) :=
  Claims.sum_spec_ml_closure

/-- (closure), at a configuration without a successor. -/
example : ∀ (H : HookParams) (u : Config (defn.sem.withHooks H))
    (_hu : ∀ v : Config (defn.sem.withHooks H), ¬ Step (defn.sem.withHooks H) u v),
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) u.val ⇒ KoreAML.allNext (KoreAML.disjList []))) :=
  Claims.sum_spec_ml_stuck

open KCore.Reachability RefKimp.Syntax in
/-- The claim at one concrete initial configuration, under every interpretation
(examples/ref-kimp/User/SumSpecInstance.lean): at `N = 3`, `S = 0`, `K = .K`, `C = 0` the
hypothesis holds, `instCfg H` is the left side, and every complete path from it passes through the
right side, `.K` alone, `$n ↦ 0`, `$s ↦ 6` (`0 + (3 + 1) * 3 / 2`). -/
example : ∀ H : HookParams,
    (3 : Int) ≥ 0 ∧
      (Claims.instCfg H).val =
        («<generatedTop>»
          («<k>» (Tm.kseq
            («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
              («{_}» («__»
                («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
                («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
            Tm.dotk))
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 3), (Tm.ident "$s", Tm.int 0)]))
          («<generatedCounter>» (Tm.int 0))).val ∧
      ∀ l, CPath (Step (defn.sem.withHooks H)) (Claims.instCfg H) l → ∃ z ∈ l, z.val =
        («<generatedTop>»
          («<k>» Tm.dotk)
          («<env>» (Tm.map [(Tm.ident "$n", Tm.int 0), (Tm.ident "$s", Tm.int 6)]))
          («<generatedCounter>» (Tm.int 0))).val :=
  Claims.sum_spec_instance

/-- info: 'RefKimp.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.consistent

/-- info: 'RefKimp.sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.sound_at

/-- info: 'RefKimp.complete_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.complete_at

/-- info: 'RefKimp.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.run_exact

/-- info: 'RefKimp.Claims.sum_spec_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.Claims.sum_spec_instance

end RefKimp.Pins
