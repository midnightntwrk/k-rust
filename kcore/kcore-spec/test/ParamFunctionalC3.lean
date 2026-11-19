/-
  The tie class `parameter functional` (`tieClasses`) on the text of construct fixture
  c3-hook-only-param-total (`f2-examples/c3-hook-only-param-total.kompile.kore`): `lg`, declared
  `function, total, hook(INT.rand)` with no equation, is a parameter symbol no registry hook
  interprets that the text declares total, and its `functional` sentence (axiom 96) is of the class
  (test/TieC3HookOnlyParamTotal.lean, `paramfunctional_account`). What fixes the class's direction,
  `hypothesis`, kernel-checked on this text:
  - `lg_value_none`, `gamma_lg_bot`: at the interpretation the parsed data carries
    (`HookParams.none`) `lg` has no value at 0, and Γ holds `lg(0) = ⊥` (`ΓDomains`), so the
    sentence, which says `lg(0)` denotes an element, fails in every model there: Γ does not entail it
    for every H, at values or otherwise;
  - `lg_value_of_paramsTotal`, `gamma_lg_value`: at an interpretation H meeting the statements'
    hypothesis `ParamsTotal c defn.totalParams H`, `lg` has a value of sort Int at every Int value
    `v`, and Γ holds `lg(v) = w` for that value `w`, which denotes an element: H decides whether the
    sentence holds at values, and `ParamsTotal` is what it needs;
  - `paramsTotal_witness`: one interpretation meets `ParamsTotal`, so the hypothesis is satisfiable.
  Run from the package root: `lake env lean -j1 test/ParamFunctionalC3.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore.ParamFunctionalC3

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/c3-hook-only-param-total.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `lg`, the one parameter symbol of the text. -/
noncomputable def lg : ParamSig := c.params.headD default

theorem params_eq : c.params = [lg] := by decide +kernel
theorem lg_sig : c.symName lg.sig.name = "Lbllg" ∧ lg.sig.args = [Srt.int] ∧ lg.sig.result = Srt.int ∧
    lg.impl = none ∧ lg.raw = false := by decide +kernel

/-- `lg` is the parameter the text declares total: the one member of `Definition.totalParams`. -/
theorem total_params : defn.totalParams = [lg.sig.name] := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- The value 0 of sort Int. -/
def v0 : GroundTerm := .dv Srt.int (.int 0)

theorem v0_sorts : c.sortsOf [v0] = some lg.sig.args := by decide +kernel

/-- At `HookParams.none` (the interpretation of `c`), `lg` has no value at 0. -/
theorem lg_value_none : c.paramVal lg.sig.name [v0] = none := by decide +kernel

/-- **Γ holds `lg(0) = ⊥` at `HookParams.none`**: the graph `ΓDomains` states of a parameter at
values, where the interpretation gives none. The functional sentence of `lg` says that `lg(0)`
denotes an element, so it fails in every model of `Γ c`. -/
theorem gamma_lg_bot :
    ΓDomains c (KoreAML.den (symApp c lg.sig.name (GroundTerm.koreList c [v0])) ≡ ⊥) := by
  refine Or.inr (Or.inl ⟨lg, [v0], by rw [params_eq]; exact List.mem_singleton_self _, v0_sorts, ?_⟩)
  rw [lg_value_none]

/-- **Under `ParamsTotal`, `lg` has a value of sort Int at every Int value.** -/
theorem lg_value_of_paramsTotal (H : HookParams) (hH : ParamsTotal c defn.totalParams H)
    (v : GroundTerm) (hv : c.sortOf v = some Srt.int) :
    ∃ w, (cH H).paramVal lg.sig.name [v] = some w ∧ c.sortOf w = some Srt.int := by
  have hs : c.sortsOf [v] = some lg.sig.args := by
    rw [lg_sig.2.1]; simp only [Semantics.sortsOf, hv]
  obtain ⟨w, hw, hws⟩ := hH lg (by rw [params_eq]; exact List.mem_singleton_self _) lg_sig.2.2.2.1
    (by rw [total_params]; exact List.mem_singleton_self _) [v] hs
  rw [lg_sig.2.2.1] at hws
  refine ⟨w, ?_, hws⟩
  have hl : (cH H).lookupParam lg.sig.name = some lg := by
    show c.lookupParam lg.sig.name = some lg
    decide +kernel
  have hsw : (cH H).sortOf w = some Srt.int := by
    rw [Semantics.sortOf_withHooks _ _ noRaw]; exact hws
  unfold Semantics.paramVal
  rw [hl]
  simp only [lg_sig.2.2.2.1, lg_sig.2.2.2.2, Bool.false_eq_true, ↓reduceIte]
  show (H.app lg.sig.name [v]).filter (fun w => (cH H).sortOf w == some lg.sig.result) = some w
  rw [hw, lg_sig.2.2.1]
  simp [hsw]

/-- **Γ holds `lg(v) = w` under `ParamsTotal`**: at an interpretation the statements admit, the
graph `ΓDomains` states of `lg` at each Int value is a value's denotation, an element. -/
theorem gamma_lg_value (H : HookParams) (hH : ParamsTotal c defn.totalParams H)
    (v : GroundTerm) (hv : c.sortOf v = some Srt.int) :
    ∃ w, c.sortOf w = some Srt.int ∧
      ΓDomains (cH H) (KoreAML.den (symApp (cH H) lg.sig.name (GroundTerm.koreList (cH H) [v])) ≡ den (cH H) w) := by
  obtain ⟨w, hw, hws⟩ := lg_value_of_paramsTotal H hH v hv
  refine ⟨w, hws, Or.inr (Or.inl ⟨lg, [v], ?_, ?_, ?_⟩)⟩
  · show lg ∈ c.params
    rw [params_eq]; exact List.mem_singleton_self _
  · rw [Semantics.sortsOf_withHooks _ _ noRaw, lg_sig.2.1]
    simp only [Semantics.sortsOf, hv]
  · rw [hw]

/-- An interpretation meeting `ParamsTotal`: `lg` is 0 everywhere. -/
def H₀ : HookParams := ⟨fun _ _ => some v0⟩

/-- **The hypothesis is satisfiable**: `H₀` gives `lg` a value of sort Int at every argument list. -/
theorem paramsTotal_witness : ParamsTotal c defn.totalParams H₀ := by
  intro k hk _ _ vs _
  rw [params_eq, List.mem_singleton] at hk
  subst hk
  exact ⟨v0, rfl, by rw [lg_sig.2.2.1]; decide +kernel⟩

end KCore.ParamFunctionalC3

#check @KCore.ParamFunctionalC3.total_params
#check @KCore.ParamFunctionalC3.gamma_lg_bot
#check @KCore.ParamFunctionalC3.lg_value_of_paramsTotal
#check @KCore.ParamFunctionalC3.gamma_lg_value
#check @KCore.ParamFunctionalC3.paramsTotal_witness
#print axioms KCore.ParamFunctionalC3.gamma_lg_bot
#print axioms KCore.ParamFunctionalC3.gamma_lg_value
#print axioms KCore.ParamFunctionalC3.paramsTotal_witness
