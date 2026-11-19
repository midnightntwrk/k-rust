/-
  Expectations of the two construct fixtures whose text declares an open generator of Exp beside
  the constructors `x` and `y`, on their kompiled texts:
  - e2-open-rule (`f2-examples/openrule.kompile.kore`): `Exp "&" Exp [comm]`, of which the text
    states no law, `same(A, B) => A ==K B` and the rule `<k> go => x & y </k>`;
  - e2-idem-ctor (`f2-examples/idemctor.kompile.kore`): `Exp "|" Exp [idem]`, with its idempotency
    sentence.
  The reader reads the production as an open generator (`ParamSig.raw`): its value at values of Exp
  is the interpretation's, the application itself where the interpretation gives none. A law
  sentence is an item of Γ at every interpretation H, so Γ has no model at an H whose value breaks
  the law (`Idem.no_model_none`), and a statement over Γ at such an H holds for that reason alone.
  Every statement here that needs a model is therefore shown at interpretations that satisfy the
  laws (`OpenLaws`) and give the generator a value at every pair (`OpenTotal`). A statement that
  holds for every H is stated without either as a hypothesis; one that needs a value of the
  generator takes `OpenTotal`, and is stated beside its instance at `lawHooks c H`.

  `closed_value`, `closed_not_bot`, `closed_not_other`: in a model of Γ of a semantics reading no
  confined sort, a closed term with a result denotes what its result denotes; so where Γ has a
  model, it does not entail that the term has no value or another value.

  Rule (e2-open-rule):
  - `openLaws_any`, `consistent`: `and` has no law, and Γ with the step's closure has a model at
    every H; `lawHooks_total`, `fst_total`, `swap_total`: three interpretations giving `and` a value
    at every pair.
  - `and_undetermined` (C7 form (c)): over all H, Γ entails neither that `and(x, y)` has no value
    nor that it is `x` (`KCore.open_undetermined`); `and_undetermined_laws`: the same over the H
    that satisfy `OpenLaws` and `OpenTotal`.
  - `same_undetermined` (C7 form (c)): over all H, Γ entails neither that `same(x & y, y & x)` has
    no value, nor that it is `true`, nor that it is `false`: it is `false` at
    `lawHooks c HookParams.none` (`same_free`) and `true` at `Hswap`, which answers `and(x, y)` at
    `and [y, x]` (`same_swap`); `same_undetermined_laws`: the same over the H that satisfy
    `OpenLaws` and `OpenTotal`.
  - `go_succ` (C7 form (a), through the reading): for every H, the successors of `<k> go </k>` are
    exactly `<k> v </k>` for v the value H gives `and` at `[x, y]`. `go_one`: so one successor for
    every H with `OpenTotal`; `go_one_lawHooks`: its instance at `lawHooks c H`. `xy_value`,
    `xy_value_lawHooks`: the value exists and is a value of Exp. `go_stuck_bad`: at `Hbad`, which
    answers a KItem, `OpenTotal` fails and there is no successor.

  Idem (e2-idem-ctor):
  - `lawHooks_laws`, `fst_laws`, `consistent_lawHooks`, `consistent_fst`, `or_values`: as above.
  - `or_undetermined`, `or_undetermined_laws` (C7 form (c)): `or(x, y)` against the value `x`.
  - `idem_x` (C7 form (a), from sentences): `or(x, x)` is `x` for every H, in every model of the
    idempotency sentence (75) as written, definedness, the signature and the domains' item for `x`
    (`Pre`, which holds neither Γ's copy of the law nor `or`'s graph); `pre_model`: these premises
    have a model; `idem_x_gamma`: so Γ entails it for every H (`pre_of_gamma`).
  - `idem_x_laws`: at values, for every H with `OpenLaws`, the value of `or(x, x)` is `x`;
    `idem_x_lawHooks`: its instance at `lawHooks c H`.
  - `no_model_none`, `not_consistent_none`: Γ at `HookParams.none` has no model.

  Run from the package root: `lake env lean -j1 test/OpenExpE2.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OpenExpE2

open KCore ML Faithful KoreAML ParamSchema

/-! ## A closed term against a value, in a semantics that reads no confined sort -/

/-- The closed term `t` as Γ writes it. -/
noncomputable def closedPat (c : Semantics) (t : Term) : KoreAML.P := KoreAML.tr ⟨[], []⟩ (Term.kore c [] t)

/-- In a model of Γ, a closed term with the result `w` denotes what `w` denotes. -/
theorem closed_value {c : Semantics} (hok : c.coreOK = true) (hrc : c.readsConfined = false) {t : Term}
    {w : GroundTerm} {s : Srt} (he : EvalTerm c [] t (some w))
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) (e : Valuation M) (m : M) :
    (closedPat c t).interpret I e m ↔ (den c w).interpret I e m := by
  have hIc : I ⊧ᴵP Γc c := by rw [Γc_plain hrc]; exact hI
  have hts : HoldsShape.TermSound c I :=
    HoldsShape.termSoundEx (Semantics.coreOK_iff_ex.mp hok) hIc (openDecided_of_readsConfined hrc).2
  exact hts he (vars := []) (vs := []) (tbl := []) (fun i s hs => by simp at hs) rfl
    (fun i v hi => absurd hi (Nat.not_lt_zero _)) ht m

/-- Where Γ has a model and the closed term `t` has the result `w`, Γ does not entail that `t` has
no value. -/
theorem closed_not_bot {c : Semantics} (hok : c.coreOK = true) (hrc : c.readsConfined = false) {t : Term}
    {w : GroundTerm} {s s' : Srt} (he : EvalTerm c [] t (some w))
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s) (hc : Consistent c)
    (hw : c.sortOf w = some s') : ¬ (Γ c ⊧ (closedPat c t ≡ ⊥)) := by
  intro hent
  obtain ⟨M, _, I, hI⟩ := hc
  have hIΓ : I ⊧ᴵP Γ c := fun φ h => hI φ (Or.inl (Or.inl h))
  have hD := defOK hIΓ
  have h2 := (KoreAML.interp_equal hD).mp (hent hIΓ KoreAML.val0 default) (elemOf c I w)
  have h1 := closed_value hok hrc he ht hIΓ KoreAML.val0 (elemOf c I w)
  have hwe := ((elemOf_spec hIΓ hw KoreAML.val0).1 _).mpr rfl
  exact absurd (h2.mp (h1.mpr hwe)) (by simp [Pattern.interpret])

/-- Where Γ has a model and the closed term `t` has the result `w`, Γ does not entail that `t` is
`u`, another value of `w`'s sort. -/
theorem closed_not_other {c : Semantics} (hok : c.coreOK = true) (hrc : c.readsConfined = false) {t : Term}
    {w u : GroundTerm} {s s' : Srt} (he : EvalTerm c [] t (some w))
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s) (hc : Consistent c)
    (hw : c.sortOf w = some s') (hu : c.sortOf u = some s') (hne : u ≠ w) :
    ¬ (Γ c ⊧ (closedPat c t ≡ den c u)) := by
  intro hent
  obtain ⟨M, _, I, hI⟩ := hc
  have hIΓ : I ⊧ᴵP Γ c := fun φ h => hI φ (Or.inl (Or.inl h))
  have hD := defOK hIΓ
  obtain ⟨hsok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core hok
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hsok hsr (OvlOK.ovlCase hno)
  have h2 := (KoreAML.interp_equal hD).mp (hent hIΓ KoreAML.val0 default) (elemOf c I w)
  have h1 := closed_value hok hrc he ht hIΓ KoreAML.val0 (elemOf c I w)
  have hwe := ((elemOf_spec hIΓ hw KoreAML.val0).1 _).mpr rfl
  have hue := ((elemOf_spec hIΓ hu KoreAML.val0).1 _).mp (h2.mp (h1.mpr hwe))
  exact hne (values_apart hIΓ hg hsc.trans (apartSort_of_sorted hg hu) hu hw hue.symm)

/-- A closed term's computed result is its result (`CExec.evalT_sound`). -/
theorem evalTerm_of_exec {c : Semantics} (hr : CExec.execReady c = true) {t : Term}
    {r : Option GroundTerm} {s : Srt} (n : Nat) (he : CExec.evalT c n [] t = some r)
    (ht : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] t = some s) : EvalTerm c [] t r := by
  obtain ⟨-, hsc, hcc, hcm, -⟩ := CExec.execReady_parts hr
  exact CExec.evalT_sound hsc hcc hcm n he (headsOK_fns _) (fun i s hs => by simp at hs) ht

/-! ## e2-open-rule: `and` with `comm`, of which the text states no law, in a rule and under a function -/

namespace Rule

definition_of defn from "f2-examples/openrule.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- Exp, its constructors `x`, `y` and its open generator `and`; the `<k>` cell, `go`, and the
function `same`. -/
def exp : Srt := 32
def kS : Sym := 383
def goS : Sym := 385
def xS : Sym := 386
def yS : Sym := 387
def sameS : Sym := 388
def andS : Sym := 389

def andP : ParamSig := { sig := ⟨andS, [exp, exp], exp⟩, raw := true }

/-- The values `x` and `y` of Exp. -/
def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem names : c.sortName exp = "Exp" ∧ c.symName kS = "Lbl'-LT-'k'-GT-'" ∧ c.symName goS = "Lblgo" ∧
    c.symName xS = "Lblx" ∧ c.symName yS = "Lbly" ∧ c.symName sameS = "Lblsame" ∧
    c.symName andS = "Lbland" := by decide +kernel

/-- The text's one open generator, as the reader reads it. -/
theorem params_raw : c.params.filter (·.raw) = [andP] := by decide +kernel

theorem and_mem : andP ∈ c.params := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The definition reads no confined sort: its theory is Γ. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem readsConfinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans readsConfined_c

theorem lawShape : LawShape c andP := Semantics.lawShape_core coreOK andP and_mem rfl

theorem only_raw : ∀ k ∈ c.params, k.raw = true → k = andP := fun k hk hr => by
  have h : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩
  rw [params_raw] at h
  exact List.mem_singleton.mp h

/-- **`and` has no law: `OpenLaws` holds under every interpretation.** -/
theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by
  obtain rfl := only_raw k hk hr
  exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- `x` and `y` apply no open generator: they are values of Exp under every interpretation. -/
theorem values_rawFree : c.rawFree xV = true ∧ c.sortOf xV = some exp ∧ c.rawFree yV = true ∧
    c.sortOf yV = some exp := by decide +kernel

theorem x_sort (H : HookParams) : (cH H).sortOf xV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.1]; exact values_rawFree.2.1
theorem y_sort (H : HookParams) : (cH H).sortOf yV = some exp := by
  rw [Semantics.sortOf_withHooks_rawFree c H values_rawFree.2.2.1]; exact values_rawFree.2.2.2
theorem xy_sorts (H : HookParams) : (cH H).sortsOf [xV, yV] = some andP.sig.args := by
  simp only [Semantics.sortsOf, x_sort H, y_sort H]; rfl

/-- The two truth values are values of Bool under every interpretation. -/
theorem bool_sort (H : HookParams) (b : Bool) : (cH H).sortOf (bool b) = some Srt.bool := by
  rw [Semantics.sortOf_withHooks_rawFree c H (by cases b <;> decide +kernel)]
  cases b <;> decide +kernel

/-! ### Γ with the step's closure has a model at every interpretation -/

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem rightHeld (H : HookParams) : (cH H).RightHeld :=
  Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H

/-- No function's fact is named: `FnFacts` holds under every interpretation (`and` has no law). -/
theorem facts (H : HookParams) : FnFacts (cH H) callOrder [] :=
  FnFacts.of_nil_laws
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named) (openLaws_any H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of_fnFacts (coreOKH H) (rightHeld H) (facts H)

/-- Every function has at most one result, for every H. -/
theorem fnDet (H : HookParams) : FnDet (cH H) := (fnModel_of_fnFacts (coreOKH H) (rightHeld H) (facts H)).1

/-! ### The interpretations: each satisfies `OpenLaws` and `OpenTotal` -/

/-- `lawHooks c H` gives `and` a value at every pair, for every H. -/
theorem lawHooks_total (H : HookParams) : OpenTotal (cH (lawHooks c H)) := openTotal_lawHooks c coreOK H

/-- `fstH`, giving `and` its first argument, gives `and` a value at every pair. -/
theorem fst_total : OpenTotal (cH fstH) := fun k hk hr vs hvs => by
  obtain rfl := only_raw k hk hr
  exact openTotal_at_fstH lawShape rfl rfl hvs

/-- The interpretation answering `and(x, y)` at `and [y, x]`, and nothing elsewhere: under it
`and` is the application itself except at `[y, x]`. -/
def Hswap : HookParams :=
  ⟨fun f vs => if f == andS && decide (vs = [yV, xV]) then some (.ctor andS [xV, yV]) else none⟩

theorem swap_yx : (cH Hswap).paramVal andS [yV, xV] = some (.ctor andS [xV, yV]) := by decide +kernel

/-- `Hswap` gives `and` a value at every pair. -/
theorem swap_total : OpenTotal (cH Hswap) := fun k hk hr vs hvs => by
  obtain rfl := only_raw k hk hr
  by_cases hyx : vs = [yV, xV]
  · subst hyx
    rw [show (cH Hswap).paramVal andP.sig.name [yV, xV] = some (.ctor andS [xV, yV]) from swap_yx]; rfl
  · have hn : (cH Hswap).hooks.app andP.sig.name vs = none := by
      show (if andS == andS && decide (vs = [yV, xV]) then some (GroundTerm.ctor andS [xV, yV]) else none) = none
      simp [hyx]
    rw [paramVal_raw_keep (c := cH Hswap) lawShape.1 lawShape.2.2.1 lawShape.2.1 lawShape.2.2.2.1
      lawShape.2.2.2.2.1 hn hvs]; rfl

/-! ### `x & y`: the value of the open generator at the rule's arguments (C7 form (c)) -/

/-- **The value of `and(x, y)` at two interpretations**: the application itself, a value of Exp
apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem and_values :
    (cH (lawHooks c HookParams.none)).paramVal andS [xV, yV] = some (.ctor andS [xV, yV]) ∧
    (cH fstH).paramVal andS [xV, yV] = some xV := by
  have happ : lawApp andP [xV, yV] = .ctor andS [xV, yV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xy_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- **`and(x, y)` is not determined by the text**: over all H, Γ entails neither that it has no
value nor that it is `x`. The first is refuted at `fstH`, where it is `x`; the second at
`lawHooks c HookParams.none`, where it is the application itself, another value of Exp. Both
interpretations give `and` a value at every pair (`fst_total`, `lawHooks_total`), every
interpretation satisfies the laws (`openLaws_any`), and their theories have models. -/
theorem and_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) andS [xV, yV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (paramApp (cH H) andS [xV, yV] ≡ den (cH H) xV)) :=
  open_undetermined c coreOK (k := andP) and_mem lawShape.1
    (consistent _) (xy_sorts _) and_values.2
    (consistent _) (xy_sorts _) and_values.1 (x_sort _) (by decide)

/-- The same over the interpretations that satisfy the laws and give `and` a value at every pair:
the two interpretations are among them. -/
theorem and_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) andS [xV, yV] ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (paramApp (cH H) andS [xV, yV] ≡ den (cH H) xV)) :=
  ⟨fun hall => param_not_bot_at c (k := andP) and_mem (consistent _) (xy_sorts _) and_values.2
      (hall _ (openLaws_any _) fst_total),
   fun hall => param_not_other_at c coreOK (k := andP) and_mem (consistent _) (xy_sorts _) and_values.1
      lawShape.1 (x_sort _) (by decide) (hall _ (openLaws_any _) (lawHooks_total _))⟩

/-- For every H with `OpenTotal`, `x & y` has a value, a value of Exp. -/
theorem xy_value (H : HookParams) (ht : OpenTotal (cH H)) :
    ∃ v, (cH H).paramVal andS [xV, yV] = some v ∧ (cH H).sortOf v = some exp := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht andP and_mem rfl [xV, yV] (xy_sorts H))
  exact ⟨v, hv, ((paramVal_raw_sorted (c := cH H) lawShape.1 rfl rfl).mp hv).2⟩

/-- `xy_value` at `lawHooks c H`, the obligation discharged. -/
theorem xy_value_lawHooks (H : HookParams) :
    ∃ v, (cH (lawHooks c H)).paramVal andS [xV, yV] = some v ∧ (cH (lawHooks c H)).sortOf v = some exp :=
  xy_value _ (lawHooks_total H)

/-! ### `same(x & y, y & x)`: the text's sentences entail no value of it (C7 form (c)) -/

/-- `same(x & y, y & x)`. -/
def sameT : Term := .app sameS [.app andS [.app xS [], .app yS []], .app andS [.app yS [], .app xS []]]

/-- At `lawHooks c HookParams.none`, `x & y` and `y & x` are two values and `same` of them is
`false`. -/
theorem same_free : EvalTerm (cH (lawHooks c HookParams.none)) [] sameT (some (bool false)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

/-- At `Hswap`, `y & x` is `and(x, y)`, the value of `x & y`, and `same` of them is `true`. -/
theorem same_swap : EvalTerm (cH Hswap) [] sameT (some (bool true)) :=
  evalTerm_of_exec (by decide +kernel) 50 (by decide +kernel) (s := Srt.bool) (by decide +kernel)

theorem same_sort (H : HookParams) :
    sortOfTerm ((cH H).rhsCtx ((cH H).fns.map Fn.sig)) [] sameT = some Srt.bool :=
  show sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) [] sameT = some Srt.bool by decide +kernel

/-- **`same(x & y, y & x)` is not determined by the text**: over all H, Γ entails neither that it
has no value, nor that it is `true`, nor that it is `false`. The first two are refuted at
`lawHooks c HookParams.none`, where it is `false`; the third at `Hswap`, where it is `true`. Both
interpretations give `and` a value at every pair (`lawHooks_total`, `swap_total`), every
interpretation satisfies the laws (`openLaws_any`), and their theories have models. -/
theorem same_undetermined :
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ den (cH H) (bool true))) ∧
    ¬ (∀ H : HookParams, Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ den (cH H) (bool false))) :=
  ⟨fun hall => closed_not_bot (coreOKH _) (readsConfinedH _) same_free (same_sort _) (consistent _)
      (bool_sort _ false) (hall _),
   fun hall => closed_not_other (coreOKH _) (readsConfinedH _) same_free (same_sort _) (consistent _)
      (bool_sort _ false) (bool_sort _ true) (by decide) (hall _),
   fun hall => closed_not_other (coreOKH _) (readsConfinedH _) same_swap (same_sort _) (consistent _)
      (bool_sort _ true) (bool_sort _ false) (by decide) (hall _)⟩

/-- The same over the interpretations that satisfy the laws and give `and` a value at every pair:
the two interpretations are among them. -/
theorem same_undetermined_laws :
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) → Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ ⊥)) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ den (cH H) (bool true))) ∧
    ¬ (∀ H : HookParams, OpenLaws (cH H) → OpenTotal (cH H) →
      Γ (cH H) ⊧ (closedPat (cH H) sameT ≡ den (cH H) (bool false))) :=
  ⟨fun hall => closed_not_bot (coreOKH _) (readsConfinedH _) same_free (same_sort _) (consistent _)
      (bool_sort _ false) (hall _ (openLaws_any _) (lawHooks_total _)),
   fun hall => closed_not_other (coreOKH _) (readsConfinedH _) same_free (same_sort _) (consistent _)
      (bool_sort _ false) (bool_sort _ true) (by decide) (hall _ (openLaws_any _) (lawHooks_total _)),
   fun hall => closed_not_other (coreOKH _) (readsConfinedH _) same_swap (same_sort _) (consistent _)
      (bool_sort _ true) (bool_sort _ false) (by decide) (hall _ (openLaws_any _) swap_total)⟩

/-! ### The rule `<k> go => x & y </k>`: the successors of `<k> go </k>` (C7 form (a), through the reading) -/

/-- The one-item sequence `kseq(inj{Exp,KItem}(t), dotk)`. -/
def item (t : Term) : Term := .app kseq [.inj exp Srt.kitem t, .app dotk []]

/-- `x & y`, the term of the rule's right side. -/
def andT : Term := .app andS [.app xS [], .app yS []]

/-- `<k> go => x & y </k>`, as the text writes it: the top cell with the counter cell a variable. -/
def ruleGo : Rule :=
  { vars := [Srt.counter]
    lhs := .app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0]
    req := none
    rhs := .app topLabel [.app kS [item andT], .var 0]
    ens := none
    prio := 50 }

/-- The semantics' one rule is the text's. -/
theorem rules_eq : c.rules = [ruleGo] := by kernel_rfl

/-- The counter cell at 0. -/
def cnt : GroundTerm := .ctor counterLabel [int 0]
/-- `<k> go </k>`. -/
def goV : GroundTerm := .ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]
/-- `<k> v </k>`, v a value of Exp. -/
def afterV (v : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kS [.ctor kseq [injNormal exp Srt.kitem v, .ctor dotk []]], cnt]

/-- `<k> go </k>` and the counter cell apply no open generator: their sorts are theirs under every H. -/
theorem go_rawFree : c.rawFree goV = true ∧ c.sortOf goV = some topCellSort ∧
    c.rawFree cnt = true ∧ c.sortOf cnt = some Srt.counter := by decide +kernel

/-- `<k> go </k>` as a configuration under H. -/
def goCfg (H : HookParams) : Config (cH H) :=
  ⟨goV, (Semantics.sortOf_withHooks_rawFree c H go_rawFree.1).trans go_rawFree.2.1⟩

/-- `x & y` has the result the interpretation gives `and` at `[x, y]`. -/
theorem and_eval (H : HookParams) (σ : Subst) :
    EvalTerm (cH H) σ andT ((cH H).paramVal andS [xV, yV]) := by
  have hx : EvalTerm (cH H) σ (.app xS []) (some xV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor xS = true by decide +kernel) .nil
  have hy : EvalTerm (cH H) σ (.app yS []) (some yV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor yS = true by decide +kernel) .nil
  exact EvalTerm.param (rs := [some xV, some yV]) (show c.isCtor andS = false by decide +kernel)
    (by decide +kernel) (show c.isParam andS = true by decide +kernel) (.cons hx (.cons hy .nil)) rfl

/-- The rule's right side under a σ that gives the counter cell: `<k> v </k>` where `x & y` has the
value v, no result where it has none. -/
theorem go_rhs (H : HookParams) {σ : Subst} (h0 : σ.lookup 0 = some cnt) :
    EvalTerm (cH H) σ ruleGo.rhs (((cH H).paramVal andS [xV, yV]).map afterV) := by
  have hand := and_eval H σ
  generalize (cH H).paramVal andS [xV, yV] = r at hand ⊢
  have hinj : EvalTerm (cH H) σ (.inj exp Srt.kitem andT) (r.map (injNormal exp Srt.kitem)) := EvalTerm.inj hand
  have hdot : EvalTerm (cH H) σ (.app dotk []) (some (.ctor dotk [])) :=
    EvalTerm.ctor (rs := []) (show c.isCtor dotk = true by decide +kernel) .nil
  have hseq := EvalTerm.ctor (rs := [r.map (injNormal exp Srt.kitem), some (.ctor dotk [])])
    (show (cH H).isCtor kseq = true from (by decide +kernel : c.isCtor kseq = true)) (.cons hinj (.cons hdot .nil))
  have hk := EvalTerm.ctor (rs := [(allSome [r.map (injNormal exp Srt.kitem), some (.ctor dotk [])]).map (.ctor kseq)])
    (show (cH H).isCtor kS = true from (by decide +kernel : c.isCtor kS = true)) (.cons hseq .nil)
  have hvar : EvalTerm (cH H) σ (.var 0) (some cnt) := h0 ▸ EvalTerm.var
  have htop := EvalTerm.ctor (rs := [_, some cnt])
    (show (cH H).isCtor topLabel = true from (by decide +kernel : c.isCtor topLabel = true)) (.cons hk (.cons hvar .nil))
  cases r <;> exact htop

/-- A match of the rule's left side at `<k> go </k>` gives the counter cell to its variable. -/
theorem go_match (H : HookParams) {σ : Subst} (hm : PatVal (cH H) σ ruleGo.lhs goV) :
    σ.lookup 0 = some cnt := by
  have hm' : PatVal (cH H) σ
      (.app topLabel [.app kS [.app kseq [.app goS [], .app dotk []]], .var 0])
      (.ctor topLabel [.ctor kS [.ctor kseq [.ctor goS [], .ctor dotk []]], cnt]) := hm
  have hct : (cH H).isCtor topLabel = true := show c.isCtor topLabel = true by decide +kernel
  cases hm' with
  | ctor _ hs =>
    cases hs with
    | cons _ hs2 =>
      cases hs2 with
      | cons h2 _ =>
        cases h2 with
        | var h => exact h
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => rw [hct] at hc; cases hc
  | ovl hc _ _ _ => rw [hct] at hc; cases hc

/-- **The successors of `<k> go </k>`, for every H**: exactly `<k> v </k>` for v the value the
interpretation gives `and` at `[x, y]`; none where it gives none. The text's rule is the one rule of
the semantics (`rules_eq`) and its right side has that result and no other (`go_rhs`, `fnDet`). -/
theorem go_succ (H : HookParams) (y' : Config (cH H)) :
    Step (cH H) (goCfg H) y' ↔ ∃ v, (cH H).paramVal andS [xV, yV] = some v ∧ y'.val = afterV v := by
  constructor
  · intro hs
    cases hs with
    | rule r mem σ _ hmatch _ _ heval _ _ _ =>
      have hr : r = ruleGo := by
        have : r ∈ c.rules := mem
        rw [rules_eq] at this; exact List.mem_singleton.mp this
      subst hr
      have he := EvalTerm.functional_of_fnDet (fnDet H) heval (go_rhs H (go_match H hmatch))
      cases hp : (cH H).paramVal andS [xV, yV] with
      | none => rw [hp] at he; cases he
      | some v => rw [hp] at he; exact ⟨v, rfl, Option.some.inj he⟩
  · rintro ⟨v, hv, hy⟩
    have hcnt : (cH H).sortOf cnt = some Srt.counter :=
      (Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.1).trans go_rawFree.2.2.2
    have hσ : (cH H).WellSorted ruleGo.vars [(0, cnt)] := fun i s hs => by
      match i, hs with
      | 0, hs => exact ⟨cnt, rfl, by cases hs; exact hcnt⟩
      | i + 1, hs => simp [ruleGo] at hs
    have he : EvalTerm (cH H) [(0, cnt)] ruleGo.rhs (some y'.val) := by
      have h := go_rhs H (σ := [(0, cnt)]) rfl
      rw [hv] at h; rw [hy]; exact h
    have hmem : ruleGo ∈ (cH H).rules := by
      show ruleGo ∈ c.rules; rw [rules_eq]; exact List.mem_singleton_self _
    have hct : ∀ f, c.isCtor f = true → (cH H).isCtor f = true := fun _ h => h
    refine Step.rule ruleGo hmem [(0, cnt)] hσ ?_ (fun _ h => by cases h) .top he
      (fun _ h => by cases h) .top (fun r' hr' hlt => ?_)
    · exact PatVal.ctor (hct _ (by decide +kernel))
        (.cons (PatVal.ctor (hct _ (by decide +kernel))
          (.cons (PatVal.ctor (hct _ (by decide +kernel))
            (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil)
              (.cons (PatVal.ctor (hct _ (by decide +kernel)) .nil) .nil))) .nil))
          (.cons (PatVal.var rfl) .nil))
    · have hr : r' = ruleGo := by
        have : r' ∈ c.rules := hr'
        rw [rules_eq] at this; exact List.mem_singleton.mp this
      subst hr
      exact absurd hlt (Nat.lt_irrefl _)

/-- `<k> v </k>` is a configuration where v is a value of Exp. -/
theorem after_sort (H : HookParams) {v : GroundTerm} (hv : (cH H).paramVal andS [xV, yV] = some v) :
    (cH H).sortOf (afterV v) = some topCellSort := by
  obtain ⟨hok, hsr, -, -, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hcnt : (cH H).sortOf cnt = some Srt.counter :=
    (Semantics.sortOf_withHooks_rawFree c H go_rawFree.2.2.1).trans go_rawFree.2.2.2
  have hσ : (cH H).WellSorted ruleGo.vars [(0, cnt)] := fun i s hs => by
    match i, hs with
    | 0, hs => exact ⟨cnt, rfl, by cases hs; exact hcnt⟩
    | i + 1, hs => simp [ruleGo] at hs
  have he : EvalTerm (cH H) [(0, cnt)] ruleGo.rhs (some (afterV v)) := by
    have h := go_rhs H (σ := [(0, cnt)]) rfl
    rw [hv] at h; exact h
  exact EvalTerm.sorted hsc he (L := (cH H).fns.map Fn.sig) (headsOK_fns _) hσ
    (show sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) ruleGo.vars ruleGo.rhs = some topCellSort by
      decide +kernel) rfl

/-- **For every H with `OpenTotal`, `<k> go </k>` has one successor**: `<k> v </k>`, v the value
of `x & y` under H. -/
theorem go_one (H : HookParams) (ht : OpenTotal (cH H)) :
    ∃ y : Config (cH H), ∀ y', Step (cH H) (goCfg H) y' ↔ y' = y := by
  obtain ⟨v, hv, -⟩ := xy_value H ht
  refine ⟨⟨afterV v, after_sort H hv⟩, fun y' => ⟨fun hs => ?_, fun e => ?_⟩⟩
  · obtain ⟨v', hv', hy⟩ := (go_succ H y').mp hs
    rw [hv] at hv'; cases hv'
    exact Subtype.ext hy
  · subst e
    exact (go_succ H _).mpr ⟨v, hv, rfl⟩

/-- `go_one` at `lawHooks c H`, the obligation discharged. -/
theorem go_one_lawHooks (H : HookParams) :
    ∃ y : Config (cH (lawHooks c H)), ∀ y', Step (cH (lawHooks c H)) (goCfg (lawHooks c H)) y' ↔ y' = y :=
  go_one _ (lawHooks_total H)

/-- At the interpretation answering `go`, of sort KItem, at every application of `and`, `and` has
no value at `[x, y]`, `OpenTotal` fails and `<k> go </k>` has no successor. -/
def Hbad : HookParams := ⟨fun f _ => if f == andS then some (.ctor goS []) else none⟩

theorem bad_none : (cH Hbad).paramVal andS [xV, yV] = none := by decide +kernel
theorem not_openTotal_bad : ¬ OpenTotal (cH Hbad) := fun h => by
  have : ((cH Hbad).paramVal andS [xV, yV]).isSome = true := h andP and_mem rfl [xV, yV] (xy_sorts Hbad)
  rw [bad_none] at this
  cases this
theorem go_stuck_bad (y' : Config (cH Hbad)) : ¬ Step (cH Hbad) (goCfg Hbad) y' := fun hs => by
  obtain ⟨v, hv, -⟩ := (go_succ Hbad y').mp hs
  rw [bad_none] at hv; cases hv

end Rule

/-! ## e2-idem-ctor: `or` with `idem`, its idempotency sentence an item of Γ -/

namespace Idem

definition_of defn from "f2-examples/idemctor.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `or`, the text's one open generator, Exp, its sort, and Exp's two constructors `x`, `y`. -/
def orS : Sym := 387
def exp : Srt := 32
def xS : Sym := 385
def yS : Sym := 386

def orP : ParamSig := { sig := ⟨orS, [exp, exp], exp⟩, raw := true, idem := true }

/-- The values `x` and `y` of Exp. -/
def xV : GroundTerm := .ctor xS []
def yV : GroundTerm := .ctor yS []

theorem names : c.symName orS = "Lblor" ∧ c.sortName exp = "Exp" ∧ c.symName yS = "Lbly" ∧
    c.symName xS = "Lblx" := by decide +kernel

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

/-- `fstH`, giving `or` its first argument, satisfies the laws and gives `or` a value at every
pair. -/
theorem fst_laws : OpenLaws (cH fstH) ∧ OpenTotal (cH fstH) := by
  refine ⟨fun k hk hr => ?_, fun k hk hr vs hvs => ?_⟩
  · obtain rfl := only_raw k hk hr
    exact ⟨fun _ => openAssoc_fstH lawShape rfl, fun _ => openIdem_fstH lawShape rfl⟩
  · obtain rfl := only_raw k hk hr
    exact openTotal_at_fstH lawShape rfl rfl hvs

theorem consistent_lawHooks : Consistent (cH (lawHooks c HookParams.none)) := consistent _ lawHooks_laws.1
theorem consistent_fst : Consistent (cH fstH) := consistent _ fst_laws.1

/-- **The value of `or(x, y)` at the two interpretations**: the application itself, a value of
Exp apart from `x`, at `lawHooks c HookParams.none`; `x` at `fstH`. -/
theorem or_values :
    (cH (lawHooks c HookParams.none)).paramVal orS [xV, yV] = some (.ctor orS [xV, yV]) ∧
    (cH fstH).paramVal orS [xV, yV] = some xV := by
  have happ : lawApp orP [xV, yV] = .ctor orS [xV, yV] := by decide +kernel
  exact ⟨(law_paramVal lawShape rfl).mpr ⟨happ.symm, (law_sortOf_iff lawShape).mpr ⟨xy_sorts _, happ, rfl⟩⟩,
    paramVal_fstH lawShape rfl (x_sort _)⟩

/-- At `fstH`, an interpretation satisfying the laws, Γ entails that `or(x, y)` is `x`. -/
theorem or_x_at_fst : Γ (cH fstH) ⊧ (paramApp (cH fstH) orS [xV, yV] ≡ den (cH fstH) xV) := by
  intro M _ I hI
  have h := hI _ (gamma_param (cH fstH) (k := orP) or_mem (xy_sorts _))
  rw [show (cH fstH).paramVal orP.sig.name [xV, yV] = some xV from or_values.2] at h
  exact h

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

/-! ### `or(x, x)` is `x`, from the idempotency sentence (75), for every H -/

kore_term kore from "f2-examples/idemctor.kompile.kore"
user_axioms U from "f2-examples/idemctor.kompile.kore" module "E2-IDEM-CTOR"

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The domains' item for the value `x`: it is one element of Exp. -/
noncomputable def xItem (H : HookParams) : KoreAML.P :=
  KoreAML.sExists ⟨1⟩ (sortP ((cH H).sortName exp)) (den (cH H) xV ≡ .evar ⟨1⟩)

/-- The premises: the idempotency sentence of `or` (75) as written, definedness, the signature
(a family of the reading) and the domains' one item for the value `x`. No other item of Γ is among
them: not the constructors' items, which hold Γ's own copy of the law, and not `or`'s graph at
H, which the domains hold. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => φ = (trS U.ax75).pat ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∨ φ = xItem H) ∪ ΓSig (cH H)

/-- The text's variable `K:SortExp{}`. -/
def kVar : Kore.Pattern := KoreAML.ev "K" (KoreAML.srt "Exp")

theorem law_pattern : U.ax75.ax.pattern = .equals (srtOf c exp) KoreAML.R (symApp c orS [kVar, kVar]) kVar := by
  decide +kernel
theorem law_trS : (trS U.ax75).pat = (trAxiom [] [] U.ax75).pat := by decide +kernel
theorem law_vars : (U.ax75.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax75.ax.pattern).eraseDups =
    [.sortVar "R", .evar "K" (KoreAML.srt "Exp")] := by decide +kernel
theorem law_sort : KoreAML.sortOf [] U.ax75.ax.pattern = some KoreAML.R := by decide +kernel
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

/-- **`or(x, x)` is `x`, for every H, from sentence 75**: in every model of the sentence as
written, definedness, the signature and `x`'s item. The sentence at `K := x`'s element says the
elements of Exp in `or(x, x)` are `x`'s; `or`'s arity (the signature) puts every element of
`or(x, x)` in Exp. -/
theorem idem_x (H : HookParams) : Pre H ⊧ (paramApp (cH H) orS [xV, xV] ≡ den (cH H) xV) := by
  intro M _ I hI
  have hax : I ⊧ᴵ (trS U.ax75).pat := hI _ (Or.inl (Or.inl rfl))
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
  let tbl : KoreAML.VarTable := KoreAML.tableOf U.ax75.ax.sortVars U.ax75.ax.pattern
  let val : KoreAML.VarKey → M := fun
    | .sortVar _ => σS
    | _ => a
  let e' : Valuation M := valOf tbl val
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by decide +kernel
  have hKmem : KoreAML.VarKey.evar "K" (KoreAML.srt "Exp") ∈ tbl := by decide +kernel
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e' b ↔ b = σS := fun b => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]
  have hKv : e'.evalEvar (tbl.ev (.evar "K" (KoreAML.srt "Exp"))) = a := valOf_ev hKmem
  have hg : ∀ k ∈ (U.ax75.ax.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] U.ax75.ax.pattern).eraseDups,
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

/-- Γ's law item is the sentence's translation: one of the constructors' items. -/
theorem openlaw_cons : (consItemsK c).any (·.pat == (trS U.ax75).pat) = true := by decide +kernel

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

/-! ### Γ at an interpretation that breaks the law has no model -/

/-- At `HookParams.none` the value of `or(x, x)` is the application itself, a value of Exp apart
from `x`: the interpretation breaks idempotence. -/
theorem xx_none : (cH HookParams.none).paramVal orS [xV, xV] = some (.ctor orS [xV, xV]) :=
  paramVal_raw_keep (c := cH HookParams.none) lawShape.1 lawShape.2.2.1 lawShape.2.1 lawShape.2.2.2.1
    lawShape.2.2.2.2.1 rfl (xx_sorts _)

/-- **Γ at `HookParams.none` has no model**: Γ holds the law, so `or(x, x)` is `x`
(`idem_x_gamma`), and `or`'s graph at that interpretation, so `or(x, x)` is the application
itself, another value of Exp. Every statement over Γ at that interpretation holds for that reason
alone, which is why `or_undetermined` and `pre_model` are shown at interpretations satisfying the
law. -/
theorem no_model_none : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    ¬ (I ⊧ᴵP Γ (cH HookParams.none)) :=
  fun _ _ _ hI => param_other_absurd c coreOK (k := orP) or_mem hI (xx_sorts _) xx_none lawShape.1
    (x_sort _) (by decide) (idem_x_gamma _ hI)

theorem not_consistent_none : ¬ Consistent (cH HookParams.none) :=
  fun ⟨M, i, I, hI⟩ => no_model_none M i I (fun φ h => hI φ (Or.inl (Or.inl h)))

/-! ### The value at values, for every H with `OpenLaws`, and its instance at `lawHooks c H` -/

/-- **For every H with `OpenLaws`, the value of `or(x, x)` is `x`.** -/
theorem idem_x_laws (H : HookParams) (hl : OpenLaws (cH H)) : (cH H).paramVal orS [xV, xV] = some xV :=
  (hl orP or_mem rfl).2 rfl xV (x_sort H)

/-- `idem_x_laws` at `lawHooks c H`, the obligation discharged. -/
theorem idem_x_lawHooks (H : HookParams) : (cH (lawHooks c H)).paramVal orS [xV, xV] = some xV :=
  idem_x_laws _ (openLaws_lawHooks c coreOK H)

end Idem

end KCore.OpenExpE2

/-- info: 'KCore.OpenExpE2.closed_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.closed_value
/-- info: 'KCore.OpenExpE2.closed_not_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.closed_not_bot
/-- info: 'KCore.OpenExpE2.closed_not_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.closed_not_other
/-- info: 'KCore.OpenExpE2.Rule.openLaws_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.openLaws_any
/-- info: 'KCore.OpenExpE2.Rule.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.consistent
/-- info: 'KCore.OpenExpE2.Rule.swap_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.swap_total
/-- info: 'KCore.OpenExpE2.Rule.and_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.and_undetermined
/-- info: 'KCore.OpenExpE2.Rule.and_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.and_undetermined_laws
/-- info: 'KCore.OpenExpE2.Rule.xy_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.xy_value
/-- info: 'KCore.OpenExpE2.Rule.xy_value_lawHooks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.xy_value_lawHooks
/-- info: 'KCore.OpenExpE2.Rule.same_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.same_free
/-- info: 'KCore.OpenExpE2.Rule.same_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.same_swap
/-- info: 'KCore.OpenExpE2.Rule.same_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.same_undetermined
/-- info: 'KCore.OpenExpE2.Rule.same_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.same_undetermined_laws
/-- info: 'KCore.OpenExpE2.Rule.go_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.go_succ
/-- info: 'KCore.OpenExpE2.Rule.go_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.go_one
/-- info: 'KCore.OpenExpE2.Rule.go_one_lawHooks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.go_one_lawHooks
/-- info: 'KCore.OpenExpE2.Rule.go_stuck_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Rule.go_stuck_bad
/-- info: 'KCore.OpenExpE2.Idem.or_undetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.or_undetermined
/-- info: 'KCore.OpenExpE2.Idem.or_undetermined_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.or_undetermined_laws
/-- info: 'KCore.OpenExpE2.Idem.idem_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.idem_x
/-- info: 'KCore.OpenExpE2.Idem.pre_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.pre_model
/-- info: 'KCore.OpenExpE2.Idem.idem_x_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.idem_x_gamma
/-- info: 'KCore.OpenExpE2.Idem.idem_x_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.idem_x_laws
/-- info: 'KCore.OpenExpE2.Idem.idem_x_lawHooks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.idem_x_lawHooks
/-- info: 'KCore.OpenExpE2.Idem.no_model_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.no_model_none
/-- info: 'KCore.OpenExpE2.Idem.not_consistent_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.OpenExpE2.Idem.not_consistent_none
