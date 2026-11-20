/-
  Expectations of the two construct fixtures whose text declares open generators of Exp with laws
  beside the constructors, on their kompiled texts (the whole-text ties are test/TieE2CommCtor.lean
  and test/TieE2BandCtor.lean):
  - e2-comm-ctor (`f2-examples/e2-comm-ctor.kompile.kore`):
    `syntax Exp ::= "x" | Exp "&" Exp [symbol(and), comm] | Exp "|" Exp [symbol(or), assoc]`;
    the reader reads `and` as an open generator without a law and `or` as one with associativity,
    whose sentence is an item of Γ at every interpretation H.
  - e2-band-ctor (`f2-examples/e2-band-ctor.kompile.kore`):
    `syntax Exp ::= "x" | "y" | Exp "|" Exp [assoc, idem, symbol(or)]`; `or` an open generator with
    associativity (sentence 75) and idempotence (sentence 76), both items of Γ at every H.
  An open generator's value at values of Exp is the interpretation's, the application itself where
  the interpretation gives none. Γ holds the laws at every H, so at an H whose value of a generator
  breaks a law Γ has no model (`BandCtor.no_model_none`, at `HookParams.none`), and a statement over
  Γ at such an H holds for that reason alone. Every statement here that needs a model is therefore
  shown at interpretations that satisfy the laws (`OpenLaws`) and give each generator a value at
  every pair (`OpenTotal`), and none of the expectations takes `OpenLaws` or `OpenTotal` as a
  hypothesis.

  In each namespace (CommCtor, BandCtor):
  - `lawHooks_laws`, `fst_laws`: the two interpretations `lawHooks c HookParams.none` (the free
    application of the laws) and `fstH` (the first argument) satisfy `OpenLaws` and `OpenTotal`;
    `consistent_lawHooks`, `consistent_fst`: Γ with the step's closure has a model at each.

  CommCtor, on `x`, the one value of Exp that applies no open generator:
  - `and_values`, `or_values`: `and(x, x)` and `or(x, x)` are the application itself at the first,
    `x` at the second.
  - `and_undetermined`, `or_undetermined` (C7 form (c)): over all H, Γ entails neither that the
    application has no value nor that it is `x` (`KCore.open_undetermined`); `*_undetermined_laws`:
    the same over the H that satisfy `OpenLaws` and `OpenTotal`.

  BandCtor:
  - `or_values`: `or(x, y)` is the application itself at the first, `x` at the second;
    `or_undetermined`, `or_undetermined_laws` (C7 form (c)) as above.
  - From the idempotency sentence (76) (C7 form (a)): `idem_x`: `or(x, x)` is `x` for every H, in
    every model of the sentence as written, definedness, the signature and the domains' item for
    `x` (`Pre`, which holds neither the associativity sentence, nor Γ's copy of the laws, nor `or`'s
    graph); `pre_model`: these premises have a model; `idem_x_gamma`: so Γ entails it for every H,
    the law being Γ's item (`pre_of_gamma`).
  - `no_model_none`, `not_consistent_none`: Γ at `HookParams.none` has no model.

  Run from the package root: `lake env lean -j1 test/OpenExpE2Ctor.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OpenExpE2Ctor

open KCore ML Faithful KoreAML ParamSchema

/-! ## e2-comm-ctor: `and` without a law, `or` with `assoc` -/

namespace CommCtor

definition_of defn from "f2-examples/e2-comm-ctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- Exp, its constructor `x`, and the text's two open generators `and`, `or`. -/
def exp : Srt := 32
def xS : Sym := 385
def andS : Sym := 386
def orS : Sym := 387

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }
def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true }

/-- The value `x` of Exp. -/
def xV : GroundTerm := .ctor xS []

theorem names : c.sortName exp = "Exp" ∧ c.symName xS = "Lblx" ∧ c.symName andS = "Lbland" ∧
    c.symName orS = "Lblor" := by decide +kernel

/-- The text's two open generators, as the reader reads them. -/
theorem params_raw : c.params.filter (·.raw) = [andP, orP] := by decide +kernel

theorem and_mem : andP ∈ c.params := by decide +kernel
theorem or_mem : orP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem and_shape : LawShape c andP := Semantics.lawShape_core coreOK andP and_mem rfl
theorem or_shape : LawShape c orP := Semantics.lawShape_core coreOK orP or_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = andP ∨ k = orP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  simpa using h

/-- `x` applies no open generator: it is a value of Exp under every interpretation. -/
theorem x_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H x_rawFree.1]; exact x_rawFree.2
theorem xx_sorts (H : HookParams) : (cH H).sortsOf [xV, xV] = some andP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H]; rfl

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

/-- `lawHooks c HookParams.none` satisfies the laws and gives both generators a value at every pair. -/
theorem lawHooks_laws : OpenLaws (cH (lawHooks c HookParams.none)) ∧ OpenTotal (cH (lawHooks c HookParams.none)) :=
  ⟨openLaws_lawHooks c coreOK _, openTotal_lawHooks c coreOK _⟩

/-- `fstH`, giving each generator its first argument, satisfies the laws and gives both a value at
every pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · rcases only_raw k hk hr with rfl | rfl
    · exact ⟨fun _ => openAssoc_fstH and_shape rfl, fun _ => openIdem_fstH and_shape rfl⟩
    · exact ⟨fun _ => openAssoc_fstH or_shape rfl, fun _ => openIdem_fstH or_shape rfl⟩
  · rcases only_raw k hk hr with rfl | rfl
    · exact openTotal_at_fstH and_shape rfl rfl hvs
    · exact openTotal_at_fstH or_shape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-! ### `and(x, x)` -/

/-- **The value of `and(x, x)` at the two interpretations**: the application itself, a value of
Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem and_values :
    (cH (lawHooks c HookParams.none)).paramVal andS [xV, xV] = some (.ctor andS [xV, xV]) ∧
    (cH fstH).paramVal andS [xV, xV] = some xV := by
  have happ : lawApp andP [xV, xV] = .ctor andS [xV, xV] := by decide +kernel
  exact ⟨(law_paramVal and_shape rfl).mpr ⟨happ.symm, (law_sortOf_iff and_shape).mpr ⟨xx_sorts _, happ, rfl⟩⟩,
    paramVal_fstH and_shape rfl (x_sort _)⟩

/-- **`and(x, x)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations satisfy the laws (`fst_laws`, `lawHooks_laws`) and their theories have models. -/
theorem and_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) andS [xV, xV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) andS [xV, xV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := andP) and_mem and_shape.1
    consistent_fst (xx_sorts _) and_values.2
    consistent_lawHooks (xx_sorts _) and_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give both generators a value at
every pair: the two interpretations are among them. -/
theorem and_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) andS [xV, xV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) andS [xV, xV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := andP) and_mem consistent_fst (xx_sorts _) and_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := andP) and_mem consistent_lawHooks (xx_sorts _) and_values.1
      and_shape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

/-! ### `or(x, x)` -/

/-- **The value of `or(x, x)` at the two interpretations**: the application itself (the right
nesting of `x, x`), a value of Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem or_values :
    (cH (lawHooks c HookParams.none)).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) ∧
    (cH fstH).paramVal orS [xV, xV] = some xV := by
  have happ : lawApp orP [xV, xV] = .ctor orS [xV, xV] := by decide +kernel
  exact ⟨(law_paramVal or_shape rfl).mpr ⟨happ.symm, (law_sortOf_iff or_shape).mpr ⟨xx_sorts _, happ, rfl⟩⟩,
    paramVal_fstH or_shape rfl (x_sort _)⟩

/-- **`or(x, x)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`; refuted at `fstH` and at `lawHooks c HookParams.none` as for `and`. -/
theorem or_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) orS [xV, xV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) orS [xV, xV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := orP) or_mem or_shape.1
    consistent_fst (xx_sorts _) or_values.2
    consistent_lawHooks (xx_sorts _) or_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give both generators a value at
every pair. -/
theorem or_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) orS [xV, xV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) orS [xV, xV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := orP) or_mem consistent_fst (xx_sorts _) or_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := orP) or_mem consistent_lawHooks (xx_sorts _) or_values.1
      or_shape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

end CommCtor

/-! ## e2-band-ctor: `or` with `assoc` and `idem`, both sentences items of Γ -/

namespace BandCtor

definition_of defn from "f2-examples/e2-band-ctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `or`, the text's one open generator, Exp, its sort, and Exp's two constructors `x`, `y`. -/
def orS : Sym := 387
def exp : Srt := 32
def xS : Sym := 385
def yS : Sym := 386

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, assoc := true, idem := true }

/-- The values `x` and `y` of Exp. -/
def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem names : c.symName orS = "Lblor" ∧ c.sortName exp = "Exp" ∧ c.symName xS = "Lblx" ∧
    c.symName yS = "Lbly" := by decide +kernel

/-- The text's one open generator, as the reader reads it. -/
theorem params_raw : c.params.filter (·.raw) = [orP] := by decide +kernel

theorem or_mem : orP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem lawShape : LawShape c orP := Semantics.lawShape_core coreOK orP or_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = orP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  exact List.mem_singleton.mp h

/-- `x` and `y` apply no open generator: they are values of Exp under every interpretation. -/
theorem values_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree yV = true ∧
    c.sortOf yV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.1]; exact values_rawFree.2.1
theorem y_sort (H : HookParams) : (cH H).sortOf yV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.2.2.1]; exact values_rawFree.2.2.2
theorem xy_sorts (H : HookParams) : (cH H).sortsOf [xV, yV] = some orP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H, y_sort H]; rfl

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

/-- `lawHooks c HookParams.none` satisfies the laws and gives `or` a value at every pair. -/
theorem lawHooks_laws : OpenLaws (cH (lawHooks c HookParams.none)) ∧ OpenTotal (cH (lawHooks c HookParams.none)) :=
  ⟨openLaws_lawHooks c coreOK _, openTotal_lawHooks c coreOK _⟩

/-- `fstH`, giving `or` its first argument, satisfies the laws and gives `or` a value at every pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · obtain rfl := only_raw k hk hr
    exact ⟨fun _ => openAssoc_fstH lawShape rfl, fun _ => openIdem_fstH lawShape rfl⟩
  · obtain rfl := only_raw k hk hr
    exact openTotal_at_fstH lawShape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-! ### `or(x, y)` -/

/-- **The value of `or(x, y)` at the two interpretations**: the application itself, a value of Exp
apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem or_values :
    (cH (lawHooks c HookParams.none)).paramVal orS [xV, yV] = some (.ctor orS [xV, yV]) ∧
    (cH fstH).paramVal orS [xV, yV] = some xV := by
  have happ : lawApp orP [xV, yV] = .ctor orS [xV, yV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xy_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- **`or(x, y)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations satisfy the laws (`fst_laws`, `lawHooks_laws`) and their theories have models. -/
theorem or_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) orS [xV, yV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) orS [xV, yV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := orP) or_mem lawShape.1
    consistent_fst (xy_sorts _) or_values.2
    consistent_lawHooks (xy_sorts _) or_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give `or` a value at every pair:
the two interpretations are among them. -/
theorem or_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) orS [xV, yV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) orS [xV, yV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := orP) or_mem consistent_fst (xy_sorts _) or_values.2
      (hall _ fst_laws.1 fst_laws.2),
   fun hall => param_not_other_at c coreOK (k := orP) or_mem consistent_lawHooks (xy_sorts _) or_values.1
      lawShape.1 (x_sort _) (by decide) (hall _ lawHooks_laws.1 lawHooks_laws.2)⟩

/-! ### `or(x, x)` is `x`, from the idempotency sentence (76), for every H -/

kore_term kore from "f2-examples/e2-band-ctor.kompile.kore"
user_axioms U from "f2-examples/e2-band-ctor.kompile.kore" module "E2-BAND-CTOR"

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The domains' item for the value `x`: it is one element of Exp. -/
noncomputable def xItem (H : HookParams) : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP ((cH H).sortName exp)) (den (cH H) xV ≡ .evar ⟨1⟩)

/-- The premises: the idempotency sentence of `or` (76) as written, definedness, the signature (a
family of the reading) and the domains' one item for the value `x`. No other item of Γ is among
them: not the associativity sentence (75), not the constructors' items, which hold Γ's own copy of
the laws, and not `or`'s graph at H, which the domains hold. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => φ = (trS U.ax76).pat ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∨ φ = xItem H) ∪ ΓSig (cH H)

/-- The text's variable `K:SortExp{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Exp")

theorem law_pattern : U.ax76.ax.pattern = .equals (srtOf c exp) KoreAML.R (symApp c orS [kVar, kVar]) kVar := by
  decide +kernel
theorem law_trS : (trS U.ax76).pat = (trAxiom [] [] U.ax76).pat := by decide +kernel
theorem law_vars : (U.ax76.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax76.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Exp")] := by decide +kernel
theorem law_sort : KoreAML.sortOf [] U.ax76.ax.pattern = some KoreAML.R := by decide +kernel
theorem exp_numbered (H : HookParams) : exp < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : exp < nRegSorts + c.sortNames.length)
theorem exp_name (H : HookParams) : (cH H).sortName exp = "Exp" := names.2.1
theorem symApp_withHooks (H : HookParams) (f : Sym) (ps : List Kore.Pattern) : symApp (cH H) f ps = symApp c f ps := rfl
theorem or_writes : ∀ ps, symApp c orS ps = .app ⟨⟨"Lblor"⟩⟩ ([].map KoreAML.srt) ps := fun ps => by
  unfold symApp; rw [names.1]; rfl
theorem or_writesH (H : HookParams) :
    ∀ ps, symApp (cH H) orP.sig.name ps = .app ⟨⟨"Lblor"⟩⟩ ([].map KoreAML.srt) ps := fun ps => by
  show symApp (cH H) orS ps = _
  rw [symApp_withHooks]; exact or_writes ps
/-- `or(x, x)` as Γ writes the parameter's application is the term's own pattern. -/
theorem app_den (H : HookParams) : paramApp (cH H) orS [xV, xV] = den (cH H) (.ctor orS [xV, xV]) := by
  unfold paramApp den
  rw [GroundTerm.kore, symApp_withHooks, or_writes, show (cH H).symName orS = "Lblor" from names.1]
  rfl
theorem or_kernel (H : HookParams) : orP.sig ∈ kernelSyms (cH H) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨orP, or_mem, rfl⟩)))
theorem xx_sorts (H : HookParams) : (cH H).sortsOf [xV, xV] = some orP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H]; rfl

/-- **`or(x, x)` is `x`, for every H, from sentence 76**: in every model of the sentence as
written, definedness, the signature and `x`'s item. The sentence at `K := x`'s element says the
elements of Exp in `or(x, x)` are `x`'s; `or`'s arity (the signature) puts every element of
`or(x, x)` in Exp. -/
theorem idem_x (H : HookParams) : Pre H ⊧ (paramApp (cH H) orS [xV, xV] ≡ den (cH H) xV) := by
  intro M _ I hI
  have hax : I ⊧ᴵ (trS U.ax76).pat := hI _ (Or.inl (Or.inl rfl))
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax76.ax.sortVars U.ax76.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Exp") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Exp"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax76.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax76.ax.pattern).eraseDups,
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
  have hP : (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c exp) KoreAML.R (symApp c orS [kVar, kVar]) kVar)).interpret
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
  -- `or(x, x)` as Γ writes it and the sentence's left side at `K := x`'s element are one set
  have happ : ∀ b, (paramApp (cH H) orS [xV, xV]).interpret I KoreAML.val0 b ↔
      (KoreAML.tr ⟨tbl, []⟩ (symApp c orS [kVar, kVar])).interpret I e' b := by
    intro b
    unfold paramApp KoreAML.den
    rw [symApp_withHooks, tr_symApp, tr_symApp]
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil]
    constructor
    · intro h
      obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
      obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
      exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, (symHead_congr orS f0).mp hf0,
        (hK b0).mpr ((hxa b0).mp hb0), h0⟩, (hK b1).mpr ((hxa b1).mp hb1), h1⟩
    · intro h
      obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
      obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
      exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, (symHead_congr orS f0).mp hf0,
        (hxa b0).mpr ((hK b0).mp hb0), h0⟩, (hxa b1).mpr ((hK b1).mp hb1), h1⟩
  -- every element of `or(x, x)` is in Exp: `or`'s arity
  have harity := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (c := cH H) (or_kernel H), rfl⟩))
  rw [symArityItem_of_symApp (c := cH H) (k := orP.sig) (h := "Lblor") (xs := []) (or_writesH H)] at harity
  have hinh : ∀ b, (paramApp (cH H) orS [xV, xV]).interpret I KoreAML.val0 b → KoreAML.Inh I σS b := by
    intro b h
    have hsub := (KoreAML.interp_included hD (m := default)).mp (harity KoreAML.val0 default) b
    simp only [orP, List.map, KoreAML.appList] at hsub
    rw [exp_name] at hsub
    refine (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσS1).mp (hsub ?_)
    unfold paramApp KoreAML.den at h
    rw [symApp_withHooks, tr_symApp, symHead_of_symApp or_writes] at h
    simp only [GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_nil] at h
    obtain ⟨f1, b1, hf1, hb1, h1⟩ := KoreAML.interp_app.mp h
    obtain ⟨f0, b0, hf0, hb0, h0⟩ := KoreAML.interp_app.mp hf1
    exact KoreAML.interp_app.mpr ⟨f1, b1, KoreAML.interp_app.mpr ⟨f0, b0, hf0,
      by rw [(hxa b0).mp hb0]; exact hasort', h0⟩, by rw [(hxa b1).mp hb1]; exact hasort', h1⟩
  intro e m
  rw [KoreAML.interp_equal hD]
  intro b
  rw [app_den H,
    (den_closed (cH H) (.ctor orS [xV, xV])).interp e KoreAML.val0 b,
    (den_closed (cH H) xV).interp e KoreAML.val0 b, hxa b, ← app_den H]
  constructor
  · intro h
    exact (hK b).mp ((hall b (hinh b h)).mp ((happ b).mp h))
  · rintro rfl
    exact (happ _).mpr ((hall _ ha).mpr ((hK _).mpr rfl))

/-- Γ's law item for idempotence is the sentence's translation: one of the constructors' items. -/
theorem openlaw_cons : (consItemsK c).any (·.pat == (trS U.ax76).pat) = true := by decide +kernel

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

/-- **Γ entails that `or(x, x)` is `x`, for every H**, with no hypothesis on H: the law is Γ's
item. -/
theorem idem_x_gamma (H : HookParams) : Γ (cH H) ⊧ (paramApp (cH H) orS [xV, xV] ≡ den (cH H) xV) := by
  intro M _ I hI
  exact idem_x H (pre_of_gamma H hI)

/-! ### Γ at an interpretation that breaks the laws has no model -/

/-- At `HookParams.none` the value of `or(x, x)` is the application itself, a value of Exp apart
from `x`: the interpretation breaks idempotence. -/
theorem xx_none : (cH HookParams.none).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) :=
  paramVal_raw_keep (c := cH HookParams.none) lawShape.1 lawShape.2.2.1 lawShape.2.1 lawShape.2.2.2.1
    lawShape.2.2.2.2.1 rfl (xx_sorts _)

/-- **Γ at `HookParams.none` has no model**: Γ holds the idempotence law, so `or(x, x)` is `x`
(`idem_x_gamma`), and `or`'s graph at that interpretation, so `or(x, x)` is the application itself,
another value of Exp. Every statement over Γ at that interpretation holds for that reason alone,
which is why `or_undetermined` and `pre_model` are shown at interpretations satisfying the laws. -/
theorem no_model_none : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    ¬ (I ⊧ᴵP Γ (cH HookParams.none)) :=
  fun _ _ _ hI => param_other_absurd c coreOK (k := orP) or_mem hI (xx_sorts _) xx_none lawShape.1
    (x_sort _) (by decide) (idem_x_gamma _ hI)

theorem not_consistent_none : ¬ Consistent (cH HookParams.none) :=
  fun ⟨M, i, I, hI⟩ => no_model_none M i I (fun φ h => hI φ (Or.inl (Or.inl h)))

end BandCtor

end KCore.OpenExpE2Ctor

/-- info: 'KCore.OpenExpE2Ctor.CommCtor.and_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.CommCtor.and_undetermined
/-- info: 'KCore.OpenExpE2Ctor.CommCtor.and_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.CommCtor.and_undetermined_laws
/-- info: 'KCore.OpenExpE2Ctor.CommCtor.or_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.CommCtor.or_undetermined
/-- info: 'KCore.OpenExpE2Ctor.CommCtor.or_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.CommCtor.or_undetermined_laws
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.or_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.or_undetermined
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.or_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.or_undetermined_laws
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.idem_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.idem_x
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.pre_model
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.idem_x_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.idem_x_gamma
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.no_model_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.no_model_none
/-- info: 'KCore.OpenExpE2Ctor.BandCtor.not_consistent_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2Ctor.BandCtor.not_consistent_none
