/-
  The families table's companions at an open generator's application (`test/Guards.lean`, rows
  domValElem, domDistinctLit and domDistinctLib), on `f2-examples/c3-ctor-assoc.kompile.kore`, whose
  one open generator is `plus`, of Exp, associative.

  The value items and the distinctness items of `ΓDomains` are stated at the values of a sort
  (`Semantics.sortOf`), and an open generator's application is a value exactly where the
  interpretation leaves it raw (`Semantics.keepsRaw`). So these two pieces read the interpretation
  at such an application, and only there (`Semantics.sortOf_withHooks_rawFree`).

  Three interpretations, each of which satisfies the law of `plus`, so that Γ with the step's
  closure has a model at each (`consistent_raw`, `consistent_bot`, `consistent_E`):
  - `Hraw := lawHooks c HookParams.none`, which leaves `plus(.E, .E)` raw;
  - `Hbot`, which answers a value of sort Int at `plus`, so that `plus` has no value anywhere and Γ
    holds `plus(.E, .E) = ⊥`;
  - `HE`, which answers `.E` at `plus`, so that Γ holds `plus(.E, .E) = .E`.

  - `valElem_open_reached`: `plus(.E, .E)` is a value of Exp at `Hraw` and none at `Hbot`; its value
    item `∃y:Exp. plus(.E, .E) = y` is a premise of Γ at `Hraw`, and no model of Γ at `Hbot`
    satisfies it.
  - `distinct_open_reached`: the list `ListItem(inj(plus(.E, .E)))` is a value of List at `Hraw` and
    none at `HE`; its distinctness from `ListItem(inj(.E))` is a premise of Γ at `Hraw`, and no model
    of Γ at `HE` satisfies it.
  So a value item, or a distinctness item, stated at every application of the open generator to
  values of its argument sorts, whatever the interpretation, would leave Γ without a model at `Hbot`,
  or at `HE`.
  - `not_total_bot`, `valItem_entailed_E`: `Hbot` gives `plus` no value, so it does not meet
    `OpenTotal`, the text's owed `functional` sentence of `plus`; at `HE`, which gives the application
    a value (`total_E`), Γ entails the value item from the parameter's graph and the item of `.E`. The
    value item is refuted only where the application has no value.

  - `litSort_everyH`: for every semantics and every H, a sort that holds only literals
    (`Semantics.litSort`) has the same values at `c.withHooks H` as at `c`: a value of it is a domain
    value (`litValue_dv`). `lit_c3`: Int, Bool, KConfigVar, Float, String and Bytes are such sorts
    on this text.

  Run from the package root: `lake env lean -j1 test/GuardOpenGen.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.GuardOpenGen

open KCore ML Faithful KoreAML

definition_of defn from "f2-examples/c3-ctor-assoc.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def plus : KCore.Sym := 387
def dotE : KCore.Sym := 385
def exp : Srt := 32

theorem names : c.symName plus = "Lblplus" ∧ c.symName dotE = "Lbl'Stop'E" ∧ c.sortName exp = "Exp" := by
  decide +kernel

/-- `plus`, the text's one open generator, as the parsed data holds it. -/
def plusK : ParamSig := { sig := ⟨plus, [exp, exp], exp⟩, raw := true, assoc := true }

theorem plus_open : c.params.filter (·.raw) = [plusK] ∧ c.lookupParam plus = some plusK := by decide +kernel

def e0 : GroundTerm := .ctor dotE []
def app : GroundTerm := .ctor plus [e0, e0]
def junk : GroundTerm := .dv Srt.int (.int 0)

/-- The associative normal form at `plus`: `plus(.E, .E)` is left raw. -/
noncomputable def Hraw : HookParams := lawHooks c HookParams.none
/-- A value of sort Int at `plus`: no value of Exp, so `plus` has no value. -/
def Hbot : HookParams := ⟨fun f _ => if f == plus then some junk else none⟩
/-- `.E` at `plus`. -/
def HE : HookParams := ⟨fun f _ => if f == plus then some e0 else none⟩

theorem sort_raw : (cH Hraw).sortOf app = some exp := by decide +kernel
theorem sort_bot : (cH Hbot).sortOf app = none := by decide +kernel
theorem sort_E : (cH HE).sortOf app = none := by decide +kernel
theorem sorts_bot : (cH Hbot).sortsOf [e0, e0] = some [exp, exp] := by decide +kernel
theorem sorts_E : (cH HE).sortsOf [e0, e0] = some [exp, exp] := by decide +kernel
theorem pv_bot : (cH Hbot).paramVal plus [e0, e0] = none := by decide +kernel
theorem pv_E : (cH HE).paramVal plus [e0, e0] = some e0 := by decide +kernel

/-- The value item of `plus(.E, .E)` at Exp: `∃y:Exp. ⟦plus(.E, .E)⟧ = y`. -/
noncomputable def valItem : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP (c.sortName exp)) (den c app ≡ .evar ⟨1⟩)

/-- At `Hraw` the value item is a premise of `ΓDomains`. -/
theorem valItem_stated : ΓDomains (cH Hraw) valItem :=
  Or.inr (Or.inr (Or.inl ⟨app, exp, sort_raw, rfl⟩))

/-- At `Hbot` Γ holds `plus(.E, .E) = ⊥` (the parameter's graph), so no model of Γ satisfies the
value item. -/
theorem valItem_refuted (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M)
    (hI : I ⊧ᴵP Γ (cH Hbot)) : ¬ (I ⊧ᴵ valItem) := by
  intro hval
  have hD := defOK hI
  have hgp := hI _ (ParamSchema.gamma_param (cH Hbot) (k := plusK) (by decide +kernel) sorts_bot)
  rw [show plusK.sig.name = plus from rfl, pv_bot] at hgp
  obtain ⟨a, -, hb⟩ := KoreAML.interp_sExists.mp (hval KoreAML.val0 default)
  have h1 := (KoreAML.interp_equal hD).mp hb a
  have h2 := (KoreAML.interp_equal hD).mp
    (hgp ⟨Function.update KoreAML.val0.evalEvar ⟨1⟩ a, KoreAML.val0.evalSvar⟩ default) a
  exact absurd (h2.mp (h1.mpr (by simp [Pattern.interpret]))) (by simp [Pattern.interpret])

/-- At `HE` Γ holds `plus(.E, .E) = .E` (the parameter's graph). -/
theorem app_is_E : Γ (cH HE) (den c app ≡ den c e0) := by
  have h := ParamSchema.gamma_param (cH HE) (k := plusK) (by decide +kernel) sorts_E
  rw [show plusK.sig.name = plus from rfl, pv_E] at h
  exact h

def l1 : GroundTerm := .list Srt.list [.inj exp Srt.kitem app]
def l2 : GroundTerm := .list Srt.list [.inj exp Srt.kitem e0]

theorem lsort_raw : (cH Hraw).sortOf l1 = some Srt.list ∧ (cH Hraw).sortOf l2 = some Srt.list ∧
    (distinctSorts (cH Hraw)).contains Srt.list = true ∧ GroundTerm.cmp l1 l2 ≠ .eq := by decide +kernel
theorem lsort_E : (cH HE).sortOf l1 = none ∧ (cH HE).sortOf l2 = some Srt.list := by decide +kernel

/-- The distinctness item of the two lists: `¬(⟦ListItem(inj(plus(.E, .E)))⟧ ∧ ⟦ListItem(inj(.E))⟧)`. -/
noncomputable def distItem : KoreAML.P := ∼(den c l1 ⋀ den c l2)

/-- At `Hraw` the two lists are distinct values of List, and their distinctness is a premise of
`ΓDomains`. -/
theorem distItem_stated : ΓDomains (cH Hraw) distItem :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨l1, l2, Srt.list, lsort_raw.2.2.1, lsort_raw.1, lsort_raw.2.1, lsort_raw.2.2.2, rfl⟩)))

theorem l1_shape : den c l1 = (KoreAML.sym (.symbol "LblListItem") ⬝
    KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP "Exp", KoreAML.Cons.sortP "KItem", den c app]) := by
  kernel_rfl
theorem l2_shape : den c l2 = (KoreAML.sym (.symbol "LblListItem") ⬝
    KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP "Exp", KoreAML.Cons.sortP "KItem", den c e0]) := by
  kernel_rfl
theorem l2_den : den (cH HE) l2 = den c l2 := by kernel_rfl

/-- At `HE` the two lists denote one element in every model of Γ (`app_is_E`, and the second is a
value there), so no model of Γ satisfies the distinctness item. -/
theorem distItem_refuted (M : Type) [Inhabited M] (I : Interpretation KoreAML.Sym M)
    (hI : I ⊧ᴵP Γ (cH HE)) : ¬ (I ⊧ᴵ distItem) := by
  intro hd
  have hD := defOK hI
  have hE := hI _ app_is_E
  have hcong : ∀ m, (den c l1).interpret I KoreAML.val0 m ↔ (den c l2).interpret I KoreAML.val0 m := by
    intro m
    rw [l1_shape, l2_shape]
    exact KoreAML.interp_app_congr (fun _ => Iff.rfl)
      (injApp_congr (fun a => (KoreAML.interp_equal hD).mp (hE KoreAML.val0 default) a)) m
  have hs := (elemOf_spec hI lsort_E.2 KoreAML.val0).1
  rw [l2_den] at hs
  have h2 := (hs _).mpr rfl
  have h1 := (hcong _).mpr h2
  have := hd KoreAML.val0 (elemOf (cH HE) I l2)
  simp only [distItem, interpret_neg, interpret_conj] at this
  exact this ⟨h1, h2⟩

/-! ## Consistency at the three interpretations -/

theorem coreOK : c.coreOK = true := by decide_cheap

def callOrder : List Nat := []

theorem facts (H : HookParams) (hop : OpenLaws (cH H)) : FnFacts (cH H) callOrder [] :=
  FnFacts.of_nil_laws
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; decide +kernel)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans (by decide +kernel))
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans (by decide +kernel))
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans (by decide +kernel)) hop

/-- Γ with the step's closure has a model at every H that satisfies the law of `plus`. -/
theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=
  consistent_of_fnFacts ((Semantics.coreOK_withHooks c H).trans coreOK)
    (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hop)

theorem consistent_raw : Consistent (cH Hraw) := consistent _ (openLaws_lawHooks c coreOK HookParams.none)

theorem raw_eq {k : ParamSig} (hk : k ∈ c.params) (hr : k.raw = true) : k = plusK := by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [plus_open.1] at h
  exact List.mem_singleton.mp h

theorem sort_junk : (cH Hbot).sortOf junk = some Srt.int := by decide +kernel

/-- At `Hbot` the open generator has no value at any argument list: the answer is of sort Int. -/
theorem pv_bot_all (vs : List GroundTerm) : (cH Hbot).paramVal plus vs = none := by
  cases h : (cH Hbot).paramVal plus vs with
  | none => rfl
  | some v =>
    obtain ⟨hv, hs⟩ := (paramVal_raw_sorted (c := cH Hbot) (k := plusK) (by decide +kernel) rfl rfl).mp h
    have hj : ((cH Hbot).hooks.app plus vs).getD (.ctor plus vs) = junk := rfl
    rw [hv, hj, sort_junk] at hs
    exact absurd hs (by decide)

theorem pv_E_all (vs : List GroundTerm) : (cH HE).paramVal plus vs = some e0 :=
  (paramVal_raw_sorted (c := cH HE) (k := plusK) (by decide +kernel) rfl rfl).mpr ⟨rfl, by decide +kernel⟩

theorem laws_bot : OpenLaws (cH Hbot) := by
  intro k hk hr
  obtain rfl := raw_eq hk hr
  refine ⟨fun _ a b d _ => ?_, fun h => absurd h (by decide)⟩
  show ((cH Hbot).paramVal plus [a, b]).bind _ = ((cH Hbot).paramVal plus [b, d]).bind _
  rw [pv_bot_all, pv_bot_all]; rfl

theorem laws_E : OpenLaws (cH HE) := by
  intro k hk hr
  obtain rfl := raw_eq hk hr
  refine ⟨fun _ a b d _ => ?_, fun h => absurd h (by decide)⟩
  show ((cH HE).paramVal plus [a, b]).bind (fun ab => (cH HE).paramVal plus [ab, d]) =
    ((cH HE).paramVal plus [b, d]).bind (fun bd => (cH HE).paramVal plus [a, bd])
  simp only [pv_E_all, Option.bind_some]

theorem consistent_bot : Consistent (cH Hbot) := consistent _ laws_bot
theorem consistent_E : Consistent (cH HE) := consistent _ laws_E

theorem gammaDomains {c : Semantics} {φ : KoreAML.P} (h : ΓDomains c φ) : Γ c φ :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

/-! ## The companions -/

/-- **The value item at an open generator's application reads the interpretation.** At `Hraw`,
where Γ has a model, `plus(.E, .E)` is a value of Exp and its value item is a premise of Γ; at
`Hbot`, where Γ has a model, it is no value and no model of Γ satisfies that item. -/
theorem valElem_open_reached :
    (Consistent (cH Hraw) ∧ (cH Hraw).sortOf app = some exp ∧ Γ (cH Hraw) valItem) ∧
    (Consistent (cH Hbot) ∧ (cH Hbot).sortOf app = none ∧
      ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH Hbot) → ¬ (I ⊧ᴵ valItem)) :=
  ⟨⟨consistent_raw, sort_raw, gammaDomains valItem_stated⟩,
   ⟨consistent_bot, sort_bot, fun M _ I hI => valItem_refuted M I hI⟩⟩

/-- **Distinctness at a collection holding an open generator's application reads the
interpretation.** At `Hraw`, where Γ has a model, `ListItem(inj(plus(.E, .E)))` is a value of List
and its distinctness from `ListItem(inj(.E))` is a premise of Γ; at `HE`, where Γ has a model, it is
no value and no model of Γ satisfies that item. -/
theorem distinct_open_reached :
    (Consistent (cH Hraw) ∧ (cH Hraw).sortOf l1 = some Srt.list ∧ Γ (cH Hraw) distItem) ∧
    (Consistent (cH HE) ∧ (cH HE).sortOf l1 = none ∧
      ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH HE) → ¬ (I ⊧ᴵ distItem)) :=
  ⟨⟨consistent_raw, lsort_raw.1, gammaDomains distItem_stated⟩,
   ⟨consistent_E, lsort_E.1, fun M _ I hI => distItem_refuted M I hI⟩⟩

/-- `Hbot` does not meet `OpenTotal`, the text's owed `functional` sentence of `plus` at values. -/
theorem not_total_bot : ¬ OpenTotal (cH Hbot) := fun h => by
  have := h plusK (by decide +kernel) rfl [e0, e0] sorts_bot
  rw [show plusK.sig.name = plus from rfl, pv_bot] at this
  cases this

/-- `HE` meets `OpenTotal`: `plus` has the value `.E` at every argument list. -/
theorem total_E : OpenTotal (cH HE) := by
  intro k hk hr vs _
  obtain rfl := raw_eq hk hr
  show ((cH HE).paramVal plus vs).isSome = true
  rw [pv_E_all]; rfl

/-- At `HE`, where `plus(.E, .E)` is no value but has the value `.E`, Γ entails its value item, from
the parameter's graph and the value item of `.E`: an interpretation that gives the application a
value does not separate the readings of the value items. -/
theorem valItem_entailed_E : Γ (cH HE) ⊧ valItem := by
  intro M _ I hI e m
  have hD := defOK hI
  have hE := hI _ app_is_E
  have h0 : ΓDomains (cH HE) (KoreAML.sExists ⟨1⟩ (sortP (c.sortName exp)) (den c e0 ≡ .evar ⟨1⟩)) :=
    Or.inr (Or.inr (Or.inl ⟨e0, exp, by decide +kernel, rfl⟩))
  obtain ⟨a, hin, heq⟩ := KoreAML.interp_sExists.mp (hI _ (gammaDomains h0) e m)
  refine KoreAML.interp_sExists.mpr ⟨a, hin, (KoreAML.interp_equal hD).mpr fun b => ?_⟩
  exact ((KoreAML.interp_equal hD).mp (hE _ default) b).trans ((KoreAML.interp_equal hD).mp heq b)

/-! ## The literal sorts -/

/-- A value of a sort that holds only literals is a domain value. -/
theorem litValue_dv {c : Semantics} {s : Srt} (hl : c.litSort s = true) {v : GroundTerm}
    (hv : c.sortOf v = some s) : ∃ l, v = .dv s l := by
  simp only [Semantics.litSort, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at hl
  obtain ⟨⟨⟨⟨⟨⟨⟨hct, hov⟩, hsub⟩, hpr⟩, hcoll⟩, htok⟩, hbyte⟩, -⟩ := hl
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, -, hs⟩ | ⟨-, o, ho, -, -, hs⟩ | ⟨-, -, k, hk, -, -, hs⟩
    · exact absurd hs.symm (hct k (lookupSig_spec hk).1)
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec ho
      exact absurd hs.symm (hov o.sig (List.mem_map.mpr ⟨o, he ▸ List.getElem_mem hi, rfl⟩))
    · obtain ⟨hm, hraw, -, -⟩ := c.lookupOpen_spec hk
      have := hpr k hm
      simp [hraw, ← hs] at this
  | inj a b t =>
    obtain ⟨hab, -, -, rfl⟩ := OvlLaws.sortOf_inj_iff.mp hv
    exact (hsub _ hab rfl).elim
  | dv s' lit => obtain ⟨-, rfl⟩ := sortOf_dv.mp hv; exact ⟨lit, rfl⟩
  | map s' es => obtain ⟨rfl, hk⟩ := sortOf_map_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | set s' es => obtain ⟨rfl, hk⟩ := sortOf_set_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk
  | list s' es => obtain ⟨rfl, hk⟩ := sortOf_list_sort hv; rw [Option.isNone_iff_eq_none.mp hcoll] at hk; cases hk

/-- **A sort that holds only literals has the same values at every interpretation**: no open
generator's application is a value of it. -/
theorem litSort_everyH (c : Semantics) (H : HookParams) {s : Srt} (hl : c.litSort s = true) (v : GroundTerm) :
    (c.withHooks H).sortOf v = some s ↔ c.sortOf v = some s := by
  constructor
  · intro h
    obtain ⟨l, rfl⟩ := litValue_dv (c := c.withHooks H) hl h
    rwa [Semantics.sortOf_withHooks_rawFree c H (by rw [Semantics.rawFree])] at h
  · intro h
    obtain ⟨l, rfl⟩ := litValue_dv hl h
    rwa [Semantics.sortOf_withHooks_rawFree c H (by rw [Semantics.rawFree])]

/-- On this text, with its open generator, the six literal sorts hold only literals. -/
theorem lit_c3 : [Srt.int, Srt.bool, Srt.kconfigVar, Srt.float, Srt.string, Srt.bytes].all c.litSort = true := by
  decide +kernel

end KCore.GuardOpenGen

#check @KCore.GuardOpenGen.valElem_open_reached
#check @KCore.GuardOpenGen.distinct_open_reached
#check @KCore.GuardOpenGen.litSort_everyH
#check @KCore.GuardOpenGen.lit_c3
#check @KCore.GuardOpenGen.valItem_entailed_E
#check @KCore.GuardOpenGen.not_total_bot
#check @KCore.GuardOpenGen.total_E
/-- info: 'KCore.GuardOpenGen.valElem_open_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.valElem_open_reached
/-- info: 'KCore.GuardOpenGen.distinct_open_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.distinct_open_reached
/-- info: 'KCore.GuardOpenGen.litSort_everyH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.litSort_everyH
/-- info: 'KCore.GuardOpenGen.valItem_entailed_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.valItem_entailed_E
/-- info: 'KCore.GuardOpenGen.not_total_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.not_total_bot
/-- info: 'KCore.GuardOpenGen.lit_c3' does not depend on any axioms -/
#guard_msgs in
#print axioms KCore.GuardOpenGen.lit_c3
