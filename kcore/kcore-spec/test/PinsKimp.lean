/-
  The statements of row imp, pinned on the package `kcore gen --wf` writes for kimp read from
  kompile's own KORE (examples/ref-kimp/RefKimp/definition.kore): the types of `consistent`,
  `sound_at`, `complete_at` and `run_exact`, each checked by its proof term at the type written
  out. Each is stated for every interpretation `H` of the hooks, concludes `Consistent` of the
  semantics under `H` (alone, or beside its entailments), and has no hypothesis on the functions:
  `sound_at` takes a step, `complete_at` `StepDecided` at the configuration and a list holding its
  successors, `run_exact` a fuel at which nothing ran out. `sound_hyp` and `complete_hyp` stay
  stated with `FnHyp` as their hypothesis. Their axioms are exactly `propext`, `Classical.choice`,
  `Quot.sound`. test/pins-kimp.sh generates the package under the namespace `RefKimp` into
  .lake/pins/kimp, builds it and checks this file against it:

      gen/gen.sh examples/ref-kimp/RefKimp/definition.kore .lake/pins/kimp RefKimp --wf
      gen/build.sh .lake/pins/kimp
      LEAN_PATH=.lake/pins/kimp/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/PinsKimp.lean
-/
import RefKimp.Sound
import RefKimp.FnHyp

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

/-- info: 'RefKimp.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.consistent

/-- info: 'RefKimp.sound_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.sound_at

/-- info: 'RefKimp.complete_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.complete_at

/-- info: 'RefKimp.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefKimp.run_exact

end RefKimp.Pins
