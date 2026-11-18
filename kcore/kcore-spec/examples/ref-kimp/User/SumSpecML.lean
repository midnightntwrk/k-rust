/-
  What K's claim `sum-spec` proved over the package's step (User/SumSpecHolds.lean) states of the
  theory `Γ` of the definition, for every interpretation `H` of the hooks.

  - `RefKimp.stepDecided_all`: at every configuration under every `H`, the evaluations the step
    reads have results (`StepDecided`): every function terminates under `H`
    (`terminates_withHooks`), and `coreOK` gives the rest (`stepDecided_pp`). This is the
    hypothesis of `RefKimp.complete_at`, so it holds at every configuration a path reaches.
  - `sum_spec_ml` (reach): from the left side, the run of `sum_spec_run_withHooks` is entailed by
    `Γ` step by step through `RefKimp.sound_at`, `⟦x⟧ → eventually ⟦y⟧` with `y` the right side,
    and `Γ` has a model (`RefKimp.consistent`).
  - `sum_spec_ml_closure` and `sum_spec_ml_stuck` (closure): at every configuration `u`, with the
    step's closure `Γstep`, every successor of `u` is `Step`'s one successor `v`
    (`⟦u⟧ → ∘(⟦v⟧)`), or there is none (`⟦u⟧ → ∘⊥`) where `Step` has none, by `RefKimp.complete_at`
    with the list `[v]` (determinism) or `[]`.
  The two are not one matching-logic formula "on every path, eventually the right side": `eventually`
  is the one-path fixpoint, and the library has no all-path fixpoint.

  The check below: the axioms are `propext`, `Classical.choice`, `Quot.sound`; no statement
  mentions `FnHyp`; and none of `FnHyp`, `fnHyp_defn`, `fnHyp_withHooks_defn` is among the
  constants the proof terms name directly. The constants reached through `RefKimp.consistent`,
  `sound_at` and `complete_at` are not checked: those theorems of the package are themselves
  proved from `fnHyp_withHooks_defn`, a theorem, not a hypothesis.
-/
import User.SumSpecHolds
import RefKimp.Facts.Terminates
import KcoreSpec.HoldsDecided

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace RefKimp

open KCore

/-- **The step is decided at every configuration, under every interpretation `H`**: the
evaluations the step at x reads have results. -/
theorem stepDecided_all (H : HookParams) (x : Config (defn.sem.withHooks H)) :
    StepDecided (defn.sem.withHooks H) x.val :=
  have hok := coreOK_withHooks_defn H
  have hs := hypSound_of_core hok
  Faithful.stepDecided_pp hs
    (fun fn hfn vs hvs => terminates_withHooks H fn.label fn (lookupFn_of_core hok hfn) vs hvs)
    (fun r hr => by
      have h := Semantics.sortedOK_sorted hs.1
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      exact h.2 r hr)
    x.val

end RefKimp

namespace RefKimp.Claims

open KCore RefKimp.Syntax
open KCore.Faithful (Γ Γstep)
open RefKimp.SumSpec (init cfg)

/-- A run of the package's step under `H` is entailed by `Γ`, one step at a time by `sound_at`:
`⟦x⟧ → eventually ⟦z⟧`. -/
theorem star_eventually_sumML (H : HookParams) {x z : Config (defn.sem.withHooks H)}
    (h : Star (Step (defn.sem.withHooks H)) x z) :
    Γ (defn.sem.withHooks H) ⊧
      (den (defn.sem.withHooks H) x.val ⇒ eventually (den (defn.sem.withHooks H) z.val)) := by
  induction h with
  | refl =>
    intro M _ I _ e m hm
    exact eventually_base (Faithful.den_closed _ _) e m hm
  | @cons x y z hxy _ ih =>
    intro M _ I hI e m hm
    obtain ⟨a, b, ha, hb, hab⟩ := KoreAML.interp_app.mp ((sound_at H x y hxy).2 hI e m hm)
    exact eventually_step e m a b ha (ih hI e b hb) hab

/-- **The claim `sum-spec` in matching logic, (reach)**: under every interpretation `H`, for
`N ≥ 0`, `S`, rest `K` of the k cell and counter `C`, from the left side's configuration `x`, the
theory `Γ` has a model and entails that `x` reaches the right side's configuration,
`⟦x⟧ → μX. ⟦y⟧ ∨ •X`. -/
theorem sum_spec_ml (H : HookParams) (N S : Int) (K : Tm Srt.k) (C : Int) (hN : N ≥ 0)
    (x : Config (defn.sem.withHooks H))
    (hx : x.val =
      («<generatedTop>»
        («<k>» (Tm.kseq
          («while(_)_» («!_» («_<=_» (Tm.ident "$n") (Tm.int 0)))
            («{_}» («__»
              («_=_;» (Tm.ident "$s") («_+_» (Tm.ident "$s") (Tm.ident "$n")))
              («_=_;» (Tm.ident "$n") («_+_» (Tm.ident "$n") (Tm.int (-1)))))))
          K))
        («<env>» (Tm.map [(Tm.ident "$n", Tm.int N), (Tm.ident "$s", Tm.int S)]))
        («<generatedCounter>» (Tm.int C))).val) :
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
  let ⟨y, hy, hs⟩ := sum_spec_run_withHooks H N S K C hN x hx
  ⟨y, hy, consistent H, star_eventually_sumML H hs⟩

/-- **(closure), at a configuration with a successor**: under every interpretation `H`, for every
step `u → v` of the package, with the step's closure every successor of `u` is `v`. -/
theorem sum_spec_ml_closure (H : HookParams) (u v : Config (defn.sem.withHooks H))
    (huv : Step (defn.sem.withHooks H) u v) :
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) u.val ⇒
          KoreAML.allNext (KoreAML.disjList [den (defn.sem.withHooks H) v.val]))) :=
  complete_at H u (stepDecided_all H u) [v.val] fun y hy => by
    rw [deterministic H hy huv]
    exact List.mem_singleton_self _

/-- **(closure), at a configuration without a successor**: under every interpretation `H`, where
the package's step has no successor of `u`, with the step's closure `u` has none. -/
theorem sum_spec_ml_stuck (H : HookParams) (u : Config (defn.sem.withHooks H))
    (hu : ∀ v : Config (defn.sem.withHooks H), ¬ Step (defn.sem.withHooks H) u v) :
    Consistent (defn.sem.withHooks H) ∧
      ((Γ (defn.sem.withHooks H) ∪ Γstep (defn.sem.withHooks H)) ⊧
        (den (defn.sem.withHooks H) u.val ⇒ KoreAML.allNext (KoreAML.disjList []))) :=
  complete_at H u (stepDecided_all H u) [] fun y hy => absurd hy (hu y)

/- The axioms are Lean's own; no statement mentions `FnHyp`; no proof term names `FnHyp`,
`fnHyp_defn` or `fnHyp_withHooks_defn`. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let banned := [``KCore.FnHyp, ``RefKimp.fnHyp_defn, ``RefKimp.fnHyp_withHooks_defn]
  for n in banned do
    unless env.contains n do throwError "no constant {n}: the check would be vacuous"
  for n in [``RefKimp.stepDecided_all, ``sum_spec_ml, ``sum_spec_ml_closure, ``sum_spec_ml_stuck,
      ``star_eventually_sumML] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"
    let some (.thmInfo t) := env.find? n | throwError "{n}: not a theorem"
    if t.type.getUsedConstants.contains ``KCore.FnHyp then throwError "{n}: the statement mentions FnHyp"
    -- the constants the proof names, and those its own auxiliary declarations (`n._…`) name
    let mut named : Array Name := #[]
    let mut todo := [t.value]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let e := todo.head!
      todo := todo.tail!
      for m in e.getUsedConstants do
        named := named.push m
        if n.isPrefixOf m && !seen.contains m then
          seen := seen.insert m
          match env.find? m with
          | some (.thmInfo a) => todo := a.value :: todo
          | some (.defnInfo a) => todo := a.value :: todo
          | _ => pure ()
    if named.isEmpty then throwError "{n}: no constants named: the check would be vacuous"
    for b in banned do
      if named.contains b then throwError "{n}: the proof names {b}"

end RefKimp.Claims
