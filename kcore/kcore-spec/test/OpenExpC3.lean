/-
  Expectations of the three construct fixtures whose text declares an open generator of Exp,
  `syntax Exp ::= ".E" | "x" | Exp "+" Exp [KEY, symbol(plus)]` with KEY one of `comm`, `assoc`,
  `idem`, on their kompiled texts (`f2-examples/c3-ctor-{comm,assoc,idem}.kompile.kore`; the
  whole-text ties are test/TieC3Ctor{Comm,Assoc,Idem}.lean). The reader reads `plus` as an open
  generator (`ParamSig.raw`): its value at values of Exp is the interpretation's, the application
  itself where the interpretation gives none. For `assoc` and `idem` the law sentence is an item of
  Γ at every interpretation H, so Γ has no model at an H whose value of `plus` breaks the law
  (`Idem.no_model_none`: at `HookParams.none`, for `idem`), and a statement over Γ at such an H
  holds for that reason alone. Every statement here that needs a model is therefore shown at
  interpretations that satisfy the laws (`OpenLaws`) and give `plus` a value at every pair
  (`OpenTotal`), and none of the expectations takes `OpenLaws` or `OpenTotal` as a hypothesis.

  In each namespace (Comm, Assoc, Idem):
  - `lawHooks_laws`, `fst_laws`: the two interpretations `lawHooks c HookParams.none` (the free
    application of the laws) and `fstH` (the first argument) satisfy `OpenLaws` and `OpenTotal`;
    `consistent_lawHooks`, `consistent_fst`: Γ with the step's closure has a model at each.
  - `plus_values`: `plus(x, .E)` is the application itself at the first, `x` at the second.
  - `plus_undetermined` (C7 form (c)): over all H, Γ entails neither that `plus(x, .E)` has no
    value nor that it is `x` (`KCore.open_undetermined`, KcoreSpec/OpenUndetermined.lean);
    `plus_undetermined_laws`: the same over the H that satisfy `OpenLaws` and `OpenTotal`;
    `plus_x_at_fst`: at `fstH`, Γ entails that it is `x`.

  In Idem, from the idempotency sentence (77) (C7 form (a)):
  - `idem_x`: `plus(x, x)` is `x` for every H, in every model of the sentence as written,
    definedness, the signature and the domains' item for `x` (`Pre`, which holds neither Γ's copy
    of the law nor `plus`'s graph); `pre_model`: these premises have a model;
    `idem_x_gamma`: so Γ entails it for every H, the law being Γ's item (`pre_of_gamma`).
  - `no_model_none`, `not_consistent_none`: Γ at `HookParams.none` has no model.

  Run from the package root: `lake env lean -j1 test/OpenExpC3.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OpenExpC3

open KCore ML Faithful KoreAML ParamSchema

/-! ## c3-ctor-comm: `plus` with `comm`, of which the text states no law -/

namespace Comm

definition_of defn from "f2-examples/c3-ctor-comm.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `plus`, the text's one open generator, Exp, its sort, and Exp's two constructors `.E`, `x`. -/
def plus : Sym := 387
def exp : Srt := 32
def dotE : Sym := 385
def xS : Sym := 386

def plusP : ParamSig := { sig := ⟨plus, [exp, exp], exp⟩, raw := true }

/-- The values `x` and `.E` of Exp. -/
def xV : GroundTerm := .ctor xS []
def eV : GroundTerm := .ctor dotE []

theorem names : c.symName plus = "Lblplus" ∧ c.sortName exp = "Exp" ∧ c.symName dotE = "Lbl'Stop'E" ∧
    c.symName xS = "Lblx" := by decide +kernel

/-- The text's one open generator, as the reader reads it. -/
theorem params_raw : c.params.filter (·.raw) = [plusP] := by decide +kernel

theorem plus_mem : plusP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem lawShape : LawShape c plusP := Semantics.lawShape_core coreOK plusP plus_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = plusP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  exact List.mem_singleton.mp h

/-- `x` and `.E` apply no open generator: they are values of Exp under every interpretation. -/
theorem values_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree eV = true ∧
    c.sortOf eV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.1]; exact values_rawFree.2.1
theorem e_sort (H : HookParams) : (cH H).sortOf eV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.2.2.1]; exact values_rawFree.2.2.2
theorem xe_sorts (H : HookParams) : (cH H).sortsOf [xV, eV] = some plusP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H, e_sort H]; rfl

/-! ### Γ with the step's closure has a model at every interpretation satisfying the laws -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H)
    (FnFacts.of_nil_laws
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop)

/-! ### The two interpretations: both satisfy `OpenLaws` and `OpenTotal` -/

/-- `lawHooks c HookParams.none` satisfies the laws and gives `plus` a value at every pair. -/
theorem lawHooks_laws : OpenLaws (cH (lawHooks c HookParams.none)) ∧ OpenTotal (cH (lawHooks c HookParams.none)) :=
  ⟨openLaws_lawHooks c coreOK _, openTotal_lawHooks c coreOK _⟩

/-- `fstH`, giving `plus` its first argument, satisfies the laws and gives `plus` a value at every
pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · obtain rfl := only_raw k hk hr
    exact ⟨fun _ => openAssoc_fstH lawShape rfl, fun _ => openIdem_fstH lawShape rfl⟩
  · obtain rfl := only_raw k hk hr
    exact openTotal_at_fstH lawShape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-- **The value of `plus(x, .E)` at the two interpretations**: the application itself, a value of
Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem plus_values :
    (cH (lawHooks c HookParams.none)).paramVal plus [xV, eV] = some (.ctor plus [xV, eV]) ∧
    (cH fstH).paramVal plus [xV, eV] = some xV := by
  have happ : lawApp plusP [xV, eV] = .ctor plus [xV, eV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xe_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- At `fstH`, an interpretation satisfying the laws, Γ entails that `plus(x, .E)` is `x`. -/
theorem plus_x_at_fst : Γ (cH fstH) ⊧ (paramApp (cH fstH) plus [xV, eV] ≡ den (cH fstH) xV) := by
  intro M _ I hI
  have h := hI _ (gamma_param (cH fstH) (k := plusP) plus_mem (xe_sorts _))
  rw [show (cH fstH).paramVal plusP.sig.name [xV, eV] = some xV from plus_values.2] at h
  exact h

/-- **`plus(x, .E)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations satisfy the laws (`fst_laws`, `lawHooks_laws`) and their theories have models. -/
theorem plus_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := plusP) plus_mem lawShape.1
    consistent_fst (xe_sorts _) plus_values.2
    consistent_lawHooks (xe_sorts _) plus_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give `plus` a value at every pair:
the two interpretations are among them. -/
theorem plus_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := plusP) plus_mem consistent_fst (xe_sorts _) plus_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := plusP) plus_mem consistent_lawHooks (xe_sorts _) plus_values.1
      lawShape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

end Comm

/-! ## c3-ctor-assoc: `plus` with `assoc`, its associativity sentence an item of Γ -/

namespace Assoc

definition_of defn from "f2-examples/c3-ctor-assoc.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `plus`, the text's one open generator, Exp, its sort, and Exp's two constructors `.E`, `x`. -/
def plus : Sym := 387
def exp : Srt := 32
def dotE : Sym := 385
def xS : Sym := 386

def plusP : ParamSig := { sig := ⟨plus, [exp, exp], exp⟩, raw := true, assoc := true }

/-- The values `x` and `.E` of Exp. -/
def xV : GroundTerm := .ctor xS []
def eV : GroundTerm := .ctor dotE []

theorem names : c.symName plus = "Lblplus" ∧ c.sortName exp = "Exp" ∧ c.symName dotE = "Lbl'Stop'E" ∧
    c.symName xS = "Lblx" := by decide +kernel

/-- The text's one open generator, as the reader reads it. -/
theorem params_raw : c.params.filter (·.raw) = [plusP] := by decide +kernel

theorem plus_mem : plusP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem lawShape : LawShape c plusP := Semantics.lawShape_core coreOK plusP plus_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = plusP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  exact List.mem_singleton.mp h

/-- `x` and `.E` apply no open generator: they are values of Exp under every interpretation. -/
theorem values_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree eV = true ∧
    c.sortOf eV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.1]; exact values_rawFree.2.1
theorem e_sort (H : HookParams) : (cH H).sortOf eV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.2.2.1]; exact values_rawFree.2.2.2
theorem xe_sorts (H : HookParams) : (cH H).sortsOf [xV, eV] = some plusP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H, e_sort H]; rfl

/-! ### Γ with the step's closure has a model at every interpretation satisfying the laws -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H)
    (FnFacts.of_nil_laws
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop)

/-! ### The two interpretations: both satisfy `OpenLaws` and `OpenTotal` -/

/-- `lawHooks c HookParams.none` satisfies the laws and gives `plus` a value at every pair. -/
theorem lawHooks_laws : OpenLaws (cH (lawHooks c HookParams.none)) ∧ OpenTotal (cH (lawHooks c HookParams.none)) :=
  ⟨openLaws_lawHooks c coreOK _, openTotal_lawHooks c coreOK _⟩

/-- `fstH`, giving `plus` its first argument, satisfies the laws and gives `plus` a value at every
pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · obtain rfl := only_raw k hk hr
    exact ⟨fun _ => openAssoc_fstH lawShape rfl, fun _ => openIdem_fstH lawShape rfl⟩
  · obtain rfl := only_raw k hk hr
    exact openTotal_at_fstH lawShape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-- **The value of `plus(x, .E)` at the two interpretations**: the application itself, a value of
Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem plus_values :
    (cH (lawHooks c HookParams.none)).paramVal plus [xV, eV] = some (.ctor plus [xV, eV]) ∧
    (cH fstH).paramVal plus [xV, eV] = some xV := by
  have happ : lawApp plusP [xV, eV] = .ctor plus [xV, eV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xe_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- At `fstH`, an interpretation satisfying the laws, Γ entails that `plus(x, .E)` is `x`. -/
theorem plus_x_at_fst : Γ (cH fstH) ⊧ (paramApp (cH fstH) plus [xV, eV] ≡ den (cH fstH) xV) := by
  intro M _ I hI
  have h := hI _ (gamma_param (cH fstH) (k := plusP) plus_mem (xe_sorts _))
  rw [show (cH fstH).paramVal plusP.sig.name [xV, eV] = some xV from plus_values.2] at h
  exact h

/-- **`plus(x, .E)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations satisfy the laws (`fst_laws`, `lawHooks_laws`) and their theories have models. -/
theorem plus_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := plusP) plus_mem lawShape.1
    consistent_fst (xe_sorts _) plus_values.2
    consistent_lawHooks (xe_sorts _) plus_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give `plus` a value at every pair:
the two interpretations are among them. -/
theorem plus_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := plusP) plus_mem consistent_fst (xe_sorts _) plus_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := plusP) plus_mem consistent_lawHooks (xe_sorts _) plus_values.1
      lawShape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

end Assoc

/-! ## c3-ctor-idem: `plus` with `idem`, its idempotency sentence an item of Γ -/

namespace Idem

definition_of defn from "f2-examples/c3-ctor-idem.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `plus`, the text's one open generator, Exp, its sort, and Exp's two constructors `.E`, `x`. -/
def plus : Sym := 387
def exp : Srt := 32
def dotE : Sym := 385
def xS : Sym := 386

def plusP : ParamSig := { sig := ⟨plus, [exp, exp], exp⟩, raw := true, idem := true }

/-- The values `x` and `.E` of Exp. -/
def xV : GroundTerm := .ctor xS []
def eV : GroundTerm := .ctor dotE []

theorem names : c.symName plus = "Lblplus" ∧ c.sortName exp = "Exp" ∧ c.symName dotE = "Lbl'Stop'E" ∧
    c.symName xS = "Lblx" := by decide +kernel

/-- The text's one open generator, as the reader reads it. -/
theorem params_raw : c.params.filter (·.raw) = [plusP] := by decide +kernel

theorem plus_mem : plusP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem lawShape : LawShape c plusP := Semantics.lawShape_core coreOK plusP plus_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = plusP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  exact List.mem_singleton.mp h

/-- `x` and `.E` apply no open generator: they are values of Exp under every interpretation. -/
theorem values_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree eV = true ∧
    c.sortOf eV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.1]; exact values_rawFree.2.1
theorem e_sort (H : HookParams) : (cH H).sortOf eV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.2.2.1]; exact values_rawFree.2.2.2
theorem xe_sorts (H : HookParams) : (cH H).sortsOf [xV, eV] = some plusP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H, e_sort H]; rfl

/-! ### Γ with the step's closure has a model at every interpretation satisfying the laws -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H)
    (FnFacts.of_nil_laws
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) hop)

/-! ### The two interpretations: both satisfy `OpenLaws` and `OpenTotal` -/

/-- `lawHooks c HookParams.none` satisfies the laws and gives `plus` a value at every pair. -/
theorem lawHooks_laws : OpenLaws (cH (lawHooks c HookParams.none)) ∧ OpenTotal (cH (lawHooks c HookParams.none)) :=
  ⟨openLaws_lawHooks c coreOK _, openTotal_lawHooks c coreOK _⟩

/-- `fstH`, giving `plus` its first argument, satisfies the laws and gives `plus` a value at every
pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · obtain rfl := only_raw k hk hr
    exact ⟨fun _ => openAssoc_fstH lawShape rfl, fun _ => openIdem_fstH lawShape rfl⟩
  · obtain rfl := only_raw k hk hr
    exact openTotal_at_fstH lawShape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-- **The value of `plus(x, .E)` at the two interpretations**: the application itself, a value of
Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem plus_values :
    (cH (lawHooks c HookParams.none)).paramVal plus [xV, eV] = some (.ctor plus [xV, eV]) ∧
    (cH fstH).paramVal plus [xV, eV] = some xV := by
  have happ : lawApp plusP [xV, eV] = .ctor plus [xV, eV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xe_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- At `fstH`, an interpretation satisfying the laws, Γ entails that `plus(x, .E)` is `x`. -/
theorem plus_x_at_fst : Γ (cH fstH) ⊧ (paramApp (cH fstH) plus [xV, eV] ≡ den (cH fstH) xV) := by
  intro M _ I hI
  have h := hI _ (gamma_param (cH fstH) (k := plusP) plus_mem (xe_sorts _))
  rw [show (cH fstH).paramVal plusP.sig.name [xV, eV] = some xV from plus_values.2] at h
  exact h

/-- **`plus(x, .E)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations satisfy the laws (`fst_laws`, `lawHooks_laws`) and their theories have models. -/
theorem plus_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := plusP) plus_mem lawShape.1
    consistent_fst (xe_sorts _) plus_values.2
    consistent_lawHooks (xe_sorts _) plus_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give `plus` a value at every pair:
the two interpretations are among them. -/
theorem plus_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) plus [xV, eV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := plusP) plus_mem consistent_fst (xe_sorts _) plus_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := plusP) plus_mem consistent_lawHooks (xe_sorts _) plus_values.1
      lawShape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

/-! ### `plus(x, x)` is `x`, from the idempotency sentence (77), for every H -/

kore_term kore from "f2-examples/c3-ctor-idem.kompile.kore"
user_axioms U from "f2-examples/c3-ctor-idem.kompile.kore" module "C3-CTOR-IDEM"

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The domains' item for the value `x`: it is one element of Exp. -/
noncomputable def xItem (H : HookParams) : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP ((cH H).sortName exp)) (den (cH H) xV ≡ .evar ⟨1⟩)

/-- The premises: the idempotency sentence of `plus` (77) as written, definedness, the signature
(a family of the reading) and the domains' one item for the value `x`. No other item of Γ is among
them: not the constructors' items, which hold Γ's own copy of the law, and not `plus`'s graph at
H, which the domains hold. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => φ = (trS U.ax77).pat ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∨ φ = xItem H) ∪ ΓSig (cH H)

/-- The text's variable `K:SortExp{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Exp")

theorem law_pattern : U.ax77.ax.pattern = .equals (srtOf c exp) KoreAML.R (symApp c plus [kVar, kVar]) kVar := by
  decide +kernel
theorem law_trS : (trS U.ax77).pat = (trAxiom [] [] U.ax77).pat := by decide +kernel
theorem law_vars : (U.ax77.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax77.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Exp")] := by decide +kernel
theorem law_sort : KoreAML.sortOf [] U.ax77.ax.pattern = some KoreAML.R := by decide +kernel
theorem exp_numbered (H : HookParams) : exp < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : exp < nRegSorts + c.sortNames.length)
theorem exp_name (H : HookParams) : (cH H).sortName exp = "Exp" := names.2.1
theorem symApp_withHooks (H : HookParams) (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl
theorem plus_writes : ∀ ps, symApp c plus ps = .app ⟨⟨"Lblplus"⟩⟩ ([].map KoreAML.srt) ps := fun ps => by
  unfold symApp; rw [names.1]; rfl
theorem plus_writesH (H : HookParams) :
    ∀ ps, symApp (cH H) plusP.sig.name ps = .app ⟨⟨"Lblplus"⟩⟩ ([].map KoreAML.srt) ps := fun ps => by
  show symApp (cH H) plus ps = _
  rw [symApp_withHooks]; exact plus_writes ps
/-- `plus(x, x)` as Γ writes the parameter's application is the term's own pattern. -/
theorem app_den (H : HookParams) : paramApp (cH H) plus [xV, xV] = den (cH H) (.ctor plus [xV, xV]) := by
  unfold paramApp den
  rw [GroundTerm.kore, symApp_withHooks, plus_writes, show (cH H).symName plus = "Lblplus" from names.1]
  rfl
theorem plus_kernel (H : HookParams) : plusP.sig ∈ kernelSyms (cH H) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨plusP, plus_mem, rfl⟩)))
theorem xx_sorts (H : HookParams) : (cH H).sortsOf [xV, xV] = some plusP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H]; rfl

/-- **`plus(x, x)` is `x`, for every H, from sentence 77**: in every model of the sentence as
written, definedness, the signature and `x`'s item. The sentence at `K := x`'s element says the
elements of Exp in `plus(x, x)` are `x`'s; `plus`'s arity (the signature) puts every element of
`plus(x, x)` in Exp. -/
theorem idem_x (H : HookParams) : Pre H ⊧ (paramApp (cH H) plus [xV, xV] ≡ den (cH H) xV) := by
  intro M _ I hI
  have hax : I ⊧ᴵ (trS U.ax77).pat := hI _ (Or.inl (Or.inl rfl))
  have hD : DefOK I := KoreAML.defOK_of fun x => hI _ (Or.inl (Or.inr (Or.inl ⟨x, rfl⟩)))
  have hSig : I ⊧ᴵP ΓSig (cH H) := fun φ h => hI φ (Or.inr h)
  rw [law_trS] at hax
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hc := hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef (c := cH H), rfl⟩))
  obtain ⟨σS, hσS1, hσS2⟩ := TieRhs.sortSing_sig hD hSig (exp_numbered H)
  rw [exp_name] at hσS1
  -- `x` is one element `a`, of Exp: its item
  have hxI := hI _ (Or.inl (Or.inr (Or.inr rfl))) KoreAML.val0 default
  unfold xItem at hxI
  rw [KoreAML.interp_sExists] at hxI
  obtain ⟨a, h1, h2⟩ := hxI
  rw [KoreAML.interp_member hD] at h1
  simp only [Function.update_same] at h1
  rw [KoreAML.interp_equal hD] at h2
  have hxa : ∀ m, (den (cH H) xV).interpret I KoreAML.val0 m ↔ m = a := fun m => by
    rw [(den_closed (cH H) xV).interp KoreAML.val0
      ⟨Function.update KoreAML.val0.evalEvar ⟨1⟩ a, KoreAML.val0.evalSvar⟩ m, h2 m, KoreAML.interp_evar]
    simp only [Function.update_same]
  have hasort : (KoreAML.inhOf (sortP ((cH H).sortName exp))).interpret I KoreAML.val0 a :=
    (((Closed.sym _).app (Closed.sym _)).interp _ KoreAML.val0 a).mp h1
  have hasort' := hasort
  rw [exp_name] at hasort'
  have ha : KoreAML.Inh I σS a := (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp hasort'
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax77.ax.sortVars U.ax77.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Exp") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Exp"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax77.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax77.ax.pattern).eraseDups,
      ∀ m, (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m
    rw [law_vars] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσS2
    · rw [List.mem_singleton.mp hk, KoreAML.interp_guard_evar hD, trSort_srt, hKv]
      exact hasort'
  have hP := (KoreAML.trAxiom_at hD hax e' hg a).mpr (by
    rw [law_sort]
    show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' a
    rw [KoreAML.interp_inhOf_of hRv]; exact ha)
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c exp) KoreAML.R (symApp c plus [kVar, kVar]) kVar)).interpret
      I e' a := by
    have := hP; simp only [tbl] at this ⊢; rw [law_pattern] at this ⊢; exact this
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c exp)).interpret I e' b ↔ b = σS := fun b => by
    unfold srtOf; rw [show c.sortName exp = "Exp" from names.2.1, trSort_srt]; exact hσS1 b
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc hS hRv hσS2 hσS2] at hP
  obtain ⟨-, hall⟩ := hP
  have hK : ∀ b, (KoreAML.tr ⟨tbl, []⟩ kVar).interpret I e' b ↔ b = a := fun b => by
    unfold kVar KoreAML.ev
    rw [KoreAML.tr, KoreAML.interp_evar]
    show b = e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Exp"))) ↔ b = a
    rw [hKv]
  -- `plus(x, x)` as Γ writes it and the sentence's left side at `K := x`'s element are one set
  have happ : ∀ b, (paramApp (cH H) plus [xV, xV]).interpret I KoreAML.val0 b ↔
      (KoreAML.tr ⟨tbl, []⟩ (symApp c plus [kVar, kVar])).interpret I e' b := by
    intro b
    unfold paramApp KoreAML.den
    rw [symApp_withHooks, tr_symApp, tr_symApp]
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    constructor
    · intro h
      obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
      obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
      exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, (symHead_congr plus f0).mp hf0,
        (hK b0).mpr ((hxa b0).mp hb0), h0⟩, (hK b1).mpr ((hxa b1).mp hb1), h1⟩
    · intro h
      obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
      obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
      exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, (symHead_congr plus f0).mp hf0,
        (hxa b0).mpr ((hK b0).mp hb0), h0⟩, (hxa b1).mpr ((hK b1).mp hb1), h1⟩
  -- every element of `plus(x, x)` is in Exp: `plus`'s arity
  have harity := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (c := cH H) (plus_kernel H), rfl⟩))
  rw [symArityItem_of_symApp (c := cH H) (k := plusP.sig) (h := "Lblplus") (xs := []) (plus_writesH H)] at harity
  have hinh : ∀ b, (paramApp (cH H) plus [xV, xV]).interpret I KoreAML.val0 b → KoreAML.Inh I σS b := by
    intro b h
    have hsub := (KoreAML.interp_included hD (m := default)).mp (harity KoreAML.val0 default) b
    simp only [plusP, List.map, KoreAML.appList] at hsub
    rw [exp_name] at hsub
    refine (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp (hsub ?_)
    unfold paramApp KoreAML.den at h
    rw [symApp_withHooks, tr_symApp, symHead_of_symApp plus_writes] at h
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at h
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, hf0,
      by rw [(hxa b0).mp hb0]; exact hasort', h0⟩, by rw [(hxa b1).mp hb1]; exact hasort', h1⟩
  intro e m
  rw [KoreAML.interp_equal hD]
  intro b
  rw [app_den H,
    (den_closed (cH H) (.ctor plus [xV, xV])).interp e KoreAML.val0 b,
    (den_closed (cH H) xV).interp e KoreAML.val0 b, hxa b, ← app_den H]
  constructor
  · intro h
    exact (hK b).mp ((hall b (hinh b h)).mp ((happ b).mp h))
  · rintro rfl
    exact (happ _).mpr ((hall _ ha).mpr ((hK _).mpr rfl))

/-- Γ's law item is the sentence's translation: one of the constructors' items. -/
theorem openlaw_cons : (consItemsK c).any (·.pat == (trS U.ax77).pat) = true := by decide +kernel

kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c

/-- A model of Γ is a model of the premises, for every H. -/
theorem pre_of_gamma (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) : I ⊧ᴵP Pre H := by
  rintro φ ((rfl | ⟨x, rfl⟩ | rfl) | h)
  · obtain ⟨it, hit, he⟩ := List.any_eq_true.mp openlaw_cons
    rw [← of_decide_eq_true he]
    exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)
  · exact sat_sig hI (Or.inl (Or.inr ⟨x, rfl⟩))
  · exact sat_dom hI (Or.inr (Or.inr (Or.inl ⟨xV, exp, x_sort H, rfl⟩)))
  · exact sat_sig hI h

/-- **The premises have a model**: at `lawHooks c HookParams.none`, a model of Γ with the step's
closure. -/
theorem pre_model : ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Pre (lawHooks c HookParams.none) := by
  obtain ⟨M, i, I, hI⟩ := consistent_lawHooks
  exact ⟨M, i, I, pre_of_gamma _ (fun φ h => hI φ (Or.inl (Or.inl h)))⟩

/-- **Γ entails that `plus(x, x)` is `x`, for every H**, with no hypothesis on H: the law is Γ's
item. -/
theorem idem_x_gamma (H : HookParams) : Γ (cH H) ⊧ (paramApp (cH H) plus [xV, xV] ≡ den (cH H) xV) := by
  intro M _ I hI
  exact idem_x H (pre_of_gamma H hI)

/-! ### Γ at an interpretation that breaks the law has no model -/

/-- At `HookParams.none` the value of `plus(x, x)` is the application itself, a value of Exp apart
from `x`: the interpretation breaks idempotence. -/
theorem xx_none : (cH HookParams.none).paramVal plus [xV, xV] = some (.ctor plus [xV, xV]) :=
  paramVal_raw_keep (c := cH HookParams.none) lawShape.1 lawShape.2.2.1 lawShape.2.1 lawShape.2.2.2.1
    lawShape.2.2.2.2.1 rfl (xx_sorts _)

/-- **Γ at `HookParams.none` has no model**: Γ holds the law, so `plus(x, x)` is `x`
(`idem_x_gamma`), and `plus`'s graph at that interpretation, so `plus(x, x)` is the application
itself, another value of Exp. Every statement over Γ at that interpretation holds for that reason
alone, which is why `plus_undetermined` and `pre_model` are shown at interpretations satisfying the
law. -/
theorem no_model_none : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    ¬ (I ⊧ᴵP Γ (cH HookParams.none)) :=
  fun _ _ _ hI => param_other_absurd c coreOK (k := plusP) plus_mem hI (xx_sorts _) xx_none lawShape.1
    (x_sort _) (by decide) (idem_x_gamma _ hI)

theorem not_consistent_none : ¬ Consistent (cH HookParams.none) :=
  fun ⟨M, i, I, hI⟩ => no_model_none M i I (fun φ h => hI φ (Or.inl (Or.inl h)))

end Idem

end KCore.OpenExpC3

/-- info: 'KCore.OpenExpC3.Comm.plus_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Comm.plus_undetermined
/-- info: 'KCore.OpenExpC3.Comm.plus_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Comm.plus_undetermined_laws
/-- info: 'KCore.OpenExpC3.Comm.plus_x_at_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Comm.plus_x_at_fst
/-- info: 'KCore.OpenExpC3.Assoc.plus_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Assoc.plus_undetermined
/-- info: 'KCore.OpenExpC3.Assoc.plus_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Assoc.plus_undetermined_laws
/-- info: 'KCore.OpenExpC3.Assoc.plus_x_at_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Assoc.plus_x_at_fst
/-- info: 'KCore.OpenExpC3.Idem.plus_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.plus_undetermined
/-- info: 'KCore.OpenExpC3.Idem.plus_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.plus_undetermined_laws
/-- info: 'KCore.OpenExpC3.Idem.plus_x_at_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.plus_x_at_fst
/-- info: 'KCore.OpenExpC3.Idem.idem_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.idem_x
/-- info: 'KCore.OpenExpC3.Idem.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.pre_model
/-- info: 'KCore.OpenExpC3.Idem.idem_x_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.idem_x_gamma
/-- info: 'KCore.OpenExpC3.Idem.no_model_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.no_model_none
/-- info: 'KCore.OpenExpC3.Idem.not_consistent_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpC3.Idem.not_consistent_none
