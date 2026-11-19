/-
  The value model at a transition T: `model_parts_T`, `den_val_T`, `sNext_iff_T`.
  Run from the package root: `lake env lean -j1 test/ModelPartsT.lean`.

  - For every semantics, the landed goals (`SatSigGoal`, …, `SatFallbackGoal`, `boolClosed_model`,
    `den_val`, `sNext_iff`) are `model_parts_T`, `den_val_T` and `sNext_iff_T` at `T := StepM c`, by
    terms: `stdI c` is `stdI_T c (StepM c)` by definition.
  - At the reader's semantics for `f2-examples/symrule.kompile.kore` (`coreOK` by `decide +kernel`),
    under `FnDet` and `FnSolves`: `model_parts_T` at the empty transition and at the full one on
    configurations, `den_val_T` at a Bool value under the empty transition, and `sNext_iff_T` there:
    no element is a successor of anything, while the parts of `Γ` that do not read the step hold.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore Faithful Faithful.Model

namespace ModelPartsT

/-! ## The landed goals are the instances at `StepM` -/

section
variable {c : Semantics} (h : HypModelCore c) (hc : c.coreOK = true) (hl : OpenLaws c)

example (hFns : SatFnsGoal c) : SatSigGoal c ∧ SatConsGoal c ∧ SatDomainsGoal c ∧ SatCollsGoal c ∧ SatFnsGoal c ∧
    SatFallbackGoal c ∧ (c.litSort Srt.bool = true → (stdI c ⊧ᴵ boolClosed c)) :=
  model_parts_T h hc hl (StepM c) hFns

example (v : GroundTerm) {s : Srt} (hv : c.sortOf v = some s) (e : ML.Valuation Elem) (m : Elem) :
    (den c v).interpret (stdI c) e m ↔ m = .val v :=
  den_val_T h (StepM c) v hv e m

example (φ : KoreAML.P) (e : ML.Valuation Elem) (x : GroundTerm) :
    (KoreAML.sNext φ).interpret (stdI c) e (.val x) ↔
      ∃ y, φ.interpret (stdI c) e (.val y) ∧ StepE c (.val x) (.val y) :=
  sNext_iff_T (StepM c) φ e x

end

/-! ## At a concrete semantics, at transitions other than `StepM` -/

definition_of defn from "f2-examples/symrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

theorem coreOK : c.coreOK = true := by decide_cheap

theorem boolLit : c.litSort Srt.bool = true := by decide +kernel

/-- The parts at the empty transition and at the transition relating every two configurations. -/
example (hd : FnDet c) (hs : FnSolves c) :
    (stdI_T c (fun _ _ => False) ⊧ᴵP ΓSig c) ∧ (stdI_T c (fun _ _ => False) ⊧ᴵP ΓFns c) ∧
    (stdI_T c (fun _ _ => False) ⊧ᴵ boolClosed c) ∧
    (stdI_T c (fun _ _ => True) ⊧ᴵP ΓCons c) ∧ (stdI_T c (fun _ _ => True) ⊧ᴵP ΓDomains c) := by
  have h := hypModel_of_fn coreOK hd hs
  have p0 := model_parts_T h coreOK (openLaws_of_plain (by decide +kernel)) (fun _ _ => False)
    (AtT.satFnsGoal_decided h (Semantics.fnsNoExs_of_all (by decide +kernel)) (clausePreDecided_of_isTop (by decide +kernel)))
  have p1 := model_parts_T h coreOK (openLaws_of_plain (by decide +kernel)) (fun _ _ => True)
    (AtT.satFnsGoal_decided h (Semantics.fnsNoExs_of_all (by decide +kernel)) (clausePreDecided_of_isTop (by decide +kernel)))
  exact ⟨p0.1, p0.2.2.2.2.1, p0.2.2.2.2.2.2 boolLit, p1.2.1, p1.2.2.1⟩

/-- Under the empty transition `true` denotes its own element, and no value has a successor. -/
example (hd : FnDet c) (hs : FnSolves c) (e : ML.Valuation Elem) (φ : KoreAML.P) (x : GroundTerm) :
    ((den c (.dv Srt.bool (.bool true))).interpret (stdI_T c (fun _ _ => False)) e
        (.val (.dv Srt.bool (.bool true)))) ∧
    ¬ (KoreAML.sNext φ).interpret (stdI_T c (fun _ _ => False)) e (.val x) := by
  have h := hypModel_of_fn coreOK hd hs
  refine ⟨(den_val_T h _ _ (by decide +kernel : c.sortOf (.dv Srt.bool (.bool true)) = some Srt.bool) e _).mpr rfl,
    fun hn => ?_⟩
  obtain ⟨y, -, hst⟩ := (sNext_iff_T _ φ e x).mp hn
  exact hst.2.2

end ModelPartsT
