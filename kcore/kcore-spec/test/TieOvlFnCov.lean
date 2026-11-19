/-
  The constructor sentences of a function-overloaded symbol at values (KcoreSpec/TieOvlFnCov.lean),
  kernel-checked on two texts and a semantics built from the second, at every interpretation `H`
  of the hooks' parameters where it says so. Run from the
  package root: `lake env lean -j1 test/TieOvlFnCov.lean`.

  - `Lhs`: `f2-examples/e5-ovl-fun-lhs.kompile.kore`. `capGas : Gas → Gas` overloads the function
    `capN : N → N` (declared total, `capN(z) = z`), N < Gas; Gas has the constructor `inf`. The
    text states `capGas`'s `functional` sentence (axiom 81), its same-constructor sentence (82) and
    the different-constructors sentence of `capGas` and `inf` (83).
    - `OvlFnTotal` holds under `FnHyp` (`total`: `capN` is declared total), so the `functional`
      sentence holds at values (`fun_atValues`).
    - `OvlFnDist capGas inf` holds (`dist`: `capGas`'s one overload is a function of the result
      sort N, so a covered application's value is an injection), so the different-constructors
      sentence holds at values (`dist_atValues`).
    - `OvlFnInj` is asked at covered value lists only (`inj_of_cov`), and under it the
      same-constructor sentence holds at values (`inj_atValues`). That N holds `z` only, which
      gives the hypothesis on this text, is not shown here.
  - `Keep`: `f2-examples/e5-ovl-fun-keep-run.kompile.kore`. The same symbols with `capN : N → Gas`
    and `capN(z) = inf`.
    - `capGas(inj z)` has the value `inf` (`res`, built on `Eval`; `res_F`, computed by
      `ovlFnResF`), so `OvlFnDist capGas inf` fails (`not_dist`) and no model of `Γc` satisfies the
      different-constructors sentence, axiom 60 (`dist_refuted`).
    - The `functional` sentence (58) holds at values (`fun_atValues`).
  - `Bare`: `Keep`'s semantics with `capN`'s clause removed and `capN` not total, the reading of no
    text: it holds the two witnesses the two texts lack (in them `capN` has a value at the one
    value of N). `capN(z)` is its rest, the interpretation's value.
    - At `HookParams.none`, `capGas(inj z)` has no value (`res_none`), `OvlFnTotal` fails
      (`not_total`) and no model of `Γc` satisfies the `functional` sentence (`fun_refuted`); nor
      does any model of `Γ`, with no hypothesis on the functions (`fun_refuted_Γ`, from
      `ΓFallback`'s item of `capN` at `z`).
    - At `Hc`, whose rest of `capN` is `capGas(inf)`, `capGas(inj z)` and `capGas(inf)` have one
      value (`res_injZ`, `res_inf`), `OvlFnInj` fails (`not_inj`) and no model of `Γc` satisfies
      the same-constructor sentence (`inj_refuted`).

  `FnHyp` stays a hypothesis on `H` throughout. The semantics read a confined sort
  (`reads_confined`), so the theory of the statements is `Γc`, which is `Γ` with the closure axiom
  of Bool.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieOvlFnCovTest

open KCore ML Faithful KoreAML

def gasS : Srt := 32
def nS : Srt := 33
def infS : Sym := 388
def zS : Sym := 390
def capN : Sym := 391
/-- `capGas : Gas → Gas`. -/
def capGasSig : CtorSig := ⟨392, [gasS], gasS⟩
/-- `inf : Gas`. -/
def infSig : CtorSig := ⟨infS, [], gasS⟩
/-- `capGas` overloads `capN`. -/
def oCap : OvlSig := ⟨capGasSig, [capN]⟩

def zT : GroundTerm := .ctor zS []
def infT : GroundTerm := .ctor infS []
/-- `inj{N, Gas}(z)` -/
def injZ : GroundTerm := .inj nS gasS zT

namespace Lhs

definition_of defn from "f2-examples/e5-ovl-fun-lhs.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-lhs.kompile.kore" module "E5-OVL-FUN-LHS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem names : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName zS = "Lblz" ∧
    c.symName infS = "Lblinf" ∧ c.symName capN = "LblcapN" ∧ c.symName capGasSig.name = "LblcapGas" := by
  decide +kernel

theorem reads_confined : c.readsConfined = true := by decide +kernel

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig
-- `capN`, the one function `capGas` overloads, is declared total.
kernel_rfl total_H : ∀ H : HookParams,
  ((cH H).fns.all fun fn => !((cH H).ovlOver oCap).any (·.name == fn.label) || fn.total) = true
-- `capGas`'s one overload is a function, of the result sort N.
kernel_rfl lifted_H : ∀ H : HookParams,
  (((cH H).ovlOver oCap).all fun kg => (cH H).ovlByFn kg && kg.result != oCap.sig.result) = true
kernel_rfl toK_H : ∀ H : HookParams, (Gen.toK (cH H) (.ctor oCap.sig), Gen.toK (cH H) (.ctor infSig)) =
  (Gen.toK c (.ctor oCap.sig), Gen.toK c (.ctor infSig))

theorem fun_shape0 : tieOvlFnFunShapeB c gasS (Gen.toK c (.ctor oCap.sig)) U.ax81.ax = true := by decide +kernel
theorem inj_shape0 : tieOvlFnInjShapeB c gasS (Gen.toK c (.ctor oCap.sig)) U.ax82.ax = true := by decide +kernel
theorem dist_shape0 : tieOvlFnDistShapeB c gasS (Gen.toK c (.ctor oCap.sig)) (Gen.toK c (.ctor infSig)) U.ax83.ax = true := by
  decide +kernel

theorem fun_shape (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax81.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1]
  exact (tieOvlFnFunShapeB_withHooks c H _ _ _).trans fun_shape0

theorem inj_shape (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax82.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1]
  exact (tieOvlFnInjShapeB_withHooks c H _ _ _).trans inj_shape0

theorem dist_shape (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax83.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1, (Prod.mk.inj (toK_H H)).2]
  exact (tieOvlFnDistShapeB_withHooks c H _ _ _ _).trans dist_shape0

/-- **`OvlFnTotal`**, under `FnHyp`: `capN` is declared total. -/
theorem total (H : HookParams) (hf : FnHyp (cH H)) : OvlFnTotal (cH H) oCap :=
  ovlFnTotal_of_total (coreOKH H) hf (lookup_H H) (total_H H)

/-- **The `functional` sentence of `capGas` holds at values**, under `FnHyp`. -/
theorem fun_atValues (H : HookParams) (hf : FnHyp (cH H)) :
    EntailsAtValuesΓc (cH H) U.ax81 (trAxiom [] [] U.ax81).pat :=
  ovlFnTotal_atValues (coreOKH H) hf (lookup_H H) (total H hf) (fun_shape H)

/-- **`OvlFnDist capGas inf`**: no value of `capGas`'s application is `inf`. -/
theorem dist (H : HookParams) : OvlFnDist (cH H) oCap infSig :=
  ovlFnDist_of_lifted (lookup_H H) (lifted_H H) (by decide)

/-- **The different-constructors sentence of `capGas` and `inf` holds at values**, under `FnHyp`. -/
theorem dist_atValues (H : HookParams) (hf : FnHyp (cH H)) :
    EntailsAtValuesΓc (cH H) U.ax83 (trAxiom [] [] U.ax83).pat :=
  ovlFnDist_atValues (coreOKH H) hf (lookup_H H) (inf_H H) rfl (dist H) (dist_shape H)

/-- `OvlFnInj` is asked of `capGas` at the value lists `capN` covers only. -/
theorem inj_of_cov (H : HookParams)
    (hcov : ∀ us vs kg kg' v v', (cH H).sortsOf us = some oCap.sig.args → (cH H).sortsOf vs = some oCap.sig.args →
      (cH H).fnCover oCap.sig.name us = some kg → (cH H).fnCover oCap.sig.name vs = some kg' →
      Eval (cH H) kg.name (stripAll kg.args oCap.sig.args us) (some v) →
      Eval (cH H) kg'.name (stripAll kg'.args oCap.sig.args vs) (some v') →
      lift kg.result oCap.sig.result v = lift kg'.result oCap.sig.result v' → us = vs) :
    OvlFnInj (cH H) oCap :=
  ovlFnInj_of_cov (lookup_H H) (lifted_H H) hcov

/-- **The same-constructor sentence of `capGas` holds at values**, under `FnHyp` and `OvlFnInj`. -/
theorem inj_atValues (H : HookParams) (hf : FnHyp (cH H)) (hinj : OvlFnInj (cH H) oCap) :
    EntailsAtValuesΓc (cH H) U.ax82 (trAxiom [] [] U.ax82).pat :=
  ovlFnInj_atValues (coreOKH H) hf (lookup_H H) hinj (inj_shape H)

end Lhs

namespace Keep

definition_of defn from "f2-examples/e5-ovl-fun-keep-run.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-keep-run.kompile.kore" module "E5-OVL-FUN-KEEP-RUN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem reads_confined : c.readsConfined = true := by decide +kernel

/-- `capN : N → Gas`. -/
def capNSig : CtorSig := ⟨capN, [nS], gasS⟩
/-- `capN(z) = inf`. -/
def capCl : Clause := { vars := [], pats := [.app zS []], req := none, rhs := .app infS [], ens := none }
def capNFn : Fn := ⟨capN, [nS], gasS, [capCl], true⟩

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig
kernel_rfl total_H : ∀ H : HookParams,
  ((cH H).fns.all fun fn => !((cH H).ovlOver oCap).any (·.name == fn.label) || fn.total) = true
kernel_rfl toK_H : ∀ H : HookParams, (Gen.toK (cH H) (.ctor oCap.sig), Gen.toK (cH H) (.ctor infSig)) =
  (Gen.toK c (.ctor oCap.sig), Gen.toK c (.ctor infSig))
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn
kernel_rfl isCtor_H : ∀ H : HookParams, ((cH H).isCtor zS, (cH H).isCtor infS) = (true, true)
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl sorts_nil : ∀ H : HookParams, (cH H).sortsOf [] = some infSig.args
-- `capN` covers `inj z`.
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some capNSig

theorem fun_shape0 : tieOvlFnFunShapeB c gasS (Gen.toK c (.ctor oCap.sig)) U.ax58.ax = true := by decide +kernel
theorem dist_shape0 : tieOvlFnDistShapeB c gasS (Gen.toK c (.ctor oCap.sig)) (Gen.toK c (.ctor infSig)) U.ax60.ax = true := by
  decide +kernel

theorem fun_shape (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) U.ax58.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1]
  exact (tieOvlFnFunShapeB_withHooks c H _ _ _).trans fun_shape0

theorem dist_shape (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax60.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1, (Prod.mk.inj (toK_H H)).2]
  exact (tieOvlFnDistShapeB_withHooks c H _ _ _ _).trans dist_shape0

/-- **The `functional` sentence of `capGas` holds at values**, under `FnHyp`. -/
theorem fun_atValues (H : HookParams) (hf : FnHyp (cH H)) :
    EntailsAtValuesΓc (cH H) U.ax58 (trAxiom [] [] U.ax58).pat :=
  ovlFnTotal_atValues (coreOKH H) hf (lookup_H H)
    (ovlFnTotal_of_total (coreOKH H) hf (lookup_H H) (total_H H)) (fun_shape H)

/-- **`capN(z)` evaluates to `inf`**, by its one clause. -/
theorem eval_z (H : HookParams) : Eval (cH H) capN [zT] (some infT) :=
  .clause (cl := capCl) (σ := []) (lookupFn_H H) (List.mem_singleton_self _) (fun i s h => by simp [capCl] at h)
    (.cons (.ctor (congrArg Prod.fst (isCtor_H H)) .nil) .nil) (fun t h => by cases h) .top
    (fun cl' h _ hlt => by
      rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl (.ctor (congrArg Prod.snd (isCtor_H H)) .nil) (fun t h => by cases h) .top

/-- **`capGas(inj z)` has the value `inf`**: `capN` covers `inj z`, and `capN(z)` is `inf`, of
`capGas`'s result sort. -/
theorem res (H : HookParams) : OvlFnRes (cH H) oCap [injZ] (some infT) :=
  OvlFnRes.fn (cover_H H) (eval_z H)

/-- **The same value, computed** by `ovlFnResF` on the data, where the executable evaluator is
sound (`ovlFnExecB`). -/
theorem res_F : OvlFnRes c oCap [injZ] (some infT) :=
  ovlFnRes_of_F coreOK (by decide +kernel) (lookup_H HookParams.none) (sorts_injZ HookParams.none)
    (n := 5) (by decide +kernel)

/-- **`OvlFnDist capGas inf` fails**, at every interpretation. -/
theorem not_dist (H : HookParams) : ¬ OvlFnDist (cH H) oCap infSig :=
  fun h => h [injZ] [] (sorts_injZ H) (sorts_nil H) (res H)

/-- **No model of `Γc` satisfies the different-constructors sentence of `capGas` and `inf`**, under
`FnHyp`: `capGas(inj z)` is `inf`. -/
theorem dist_refuted (H : HookParams) (hf : FnHyp (cH H)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH H) →
      ¬ (I ⊧ᴵ (trAxiom [] [] U.ax60).pat) :=
  ovlFnDist_refuted (coreOKH H) hf (lookup_H H) (inf_H H) rfl (dist_shape H) (sorts_injZ H) (sorts_nil H) (res H)

end Keep

/-! ## A covering function without a clause

`Keep`'s semantics with `capN`'s clause removed and `capN` not total: the reading of no text here,
built to hold the two witnesses the texts lack. `capN(z)` is then its rest, the interpretation's
value. The sentences are `Keep`'s text's, whose form is decided against this semantics (the
signature is `Keep`'s). -/
namespace Bare

/-- `capN : N → Gas`, without a clause, not total. -/
def capNFn0 : Fn := ⟨capN, [nS], gasS, [], false⟩

noncomputable abbrev c : Semantics := { Keep.c with fns := [capNFn0] }
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `capGas(inf)`, a raw application: `inf` is no lift of a value of N. -/
def capGasInf : GroundTerm := .ctor capGasSig.name [infT]
/-- The interpretation whose rest of `capN` is `capGas(inf)`. -/
def Hc : HookParams := ⟨fun f _ => if f = capN then some capGasInf else none⟩

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl toK_H : ∀ H : HookParams, Gen.toK (cH H) (.ctor oCap.sig) = Gen.toK c (.ctor oCap.sig)
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn0
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl sort_z : ∀ H : HookParams, (cH H).sortOf zT = some nS
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some Keep.capNSig
kernel_rfl rest_Hc : (cH Hc).fnRest capNFn0 [zT] = some capGasInf
kernel_rfl sorts_inf : (cH Hc).sortsOf [infT] = some oCap.sig.args
kernel_rfl cover_inf : (cH Hc).fnCover oCap.sig.name [infT] = none
kernel_rfl norm_inf : (cH Hc).norm oCap.sig.name [infT] = capGasInf

theorem fun_shape0 : tieOvlFnFunShapeB c gasS (Gen.toK c (.ctor oCap.sig)) Keep.U.ax58.ax = true := by decide +kernel
theorem inj_shape0 : tieOvlFnInjShapeB c gasS (Gen.toK c (.ctor oCap.sig)) Keep.U.ax59.ax = true := by decide +kernel

theorem fun_shape (H : HookParams) :
    tieOvlFnFunShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) Keep.U.ax58.ax = true := by
  rw [toK_H H]
  exact (tieOvlFnFunShapeB_withHooks c H _ _ _).trans fun_shape0

theorem inj_shape (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) Keep.U.ax59.ax = true := by
  rw [toK_H H]
  exact (tieOvlFnInjShapeB_withHooks c H _ _ _).trans inj_shape0

/-- `capN(z)` is its rest: it has no clause. -/
theorem eval_z (H : HookParams) : Eval (cH H) capN [zT] ((cH H).fnRest capNFn0 [zT]) :=
  .rest (lookupFn_H H) (fun _ h => nomatch h)

/-- **At `HookParams.none`, `capGas(inj z)` has no value**: `capN` covers `inj z` and has none. -/
theorem res_none : OvlFnRes (cH HookParams.none) oCap [injZ] none := by
  have h := OvlFnRes.fn (cover_H HookParams.none) (eval_z HookParams.none)
  rw [Semantics.fnRest_withHooks_none] at h
  exact h

/-- **`OvlFnTotal` fails at `HookParams.none`.** -/
theorem not_total : ¬ OvlFnTotal (cH HookParams.none) oCap := fun h => by
  obtain ⟨v, hv⟩ := h [injZ] _ (sorts_injZ _) (cover_H _)
  cases hv with
  | clause hfn hmem =>
    have e := (lookupFn_H HookParams.none).symm.trans hfn
    cases e
    exact absurd hmem (by simp [capNFn0])
  | clauseEx hfn hmem =>
    have e := (lookupFn_H HookParams.none).symm.trans hfn
    cases e
    exact absurd hmem (by simp [capNFn0])

/-- **At `HookParams.none`, no model of `Γc` satisfies the `functional` sentence of `capGas`**,
under `FnHyp`: `capGas(inj z)` has no value. -/
theorem fun_refuted (hf : FnHyp (cH HookParams.none)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH HookParams.none) →
      ¬ (I ⊧ᴵ (trAxiom [] [] Keep.U.ax58).pat) :=
  ovlFnTotal_refuted (coreOKH _) hf (lookup_H _) (fun_shape _) (sorts_injZ _) res_none (sort_z _)

kernel_rfl fns_H : ∀ H : HookParams, (cH H).fns = [capNFn0]
kernel_rfl sorts_z : ∀ H : HookParams, (cH H).sortsOf [zT] = some capNFn0.args

/-- **At `HookParams.none`, no model of `Γ` satisfies the `functional` sentence of `capGas`**, with
no hypothesis on the functions: `ΓFallback` states `capN(z) ≡ ⊥` (`rest_den`), the overload's
equation then leaves `capGas(inj z)` empty (`ovlFnCov_gs_fn`), and the sentence makes it one
element (`ovlFnTotal_refuted_gs`). The route of `test/OvlFnCovered.lean`, through the library. -/
theorem fun_refuted_Γ : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
    I ⊧ᴵP Γ (cH HookParams.none) → ¬ (I ⊧ᴵ (trAxiom [] [] Keep.U.ax58).pat) := by
  intro M _ I hI
  obtain ⟨hok, hsr, hnn, -, -, -, -, -, hno⟩ := hypSoundEx_of_coreEx (Semantics.coreOK_iff_ex.mp (coreOKH HookParams.none))
  haveI : OvlOK (cH HookParams.none) := hno
  have hsc := sortCtx_of_allCEx hok hsr (OvlOK.ovlCase hno)
  have hmem : capNFn0 ∈ (cH HookParams.none).allFns :=
    List.mem_append_left _ (by rw [fns_H]; exact List.mem_singleton_self _)
  have hg := rest_den hI hmem (sorts_z HookParams.none) (fun _ h => nomatch h) KoreAML.val0
  have hgs := ovlFnCov_gs_fn hI hsc.trans hnn (lookup_H _) (sorts_injZ _) (cover_H _) (r := none)
    (fun v hv => by cases hv) (fun m => by
      have h1 := hg m
      rw [Semantics.fnRest_withHooks_none] at h1
      exact h1)
  exact ovlFnTotal_refuted_gs (coreOKH _) hI (lookup_H _) (fun_shape _) (sorts_injZ _)
    (fun m hm => (hgs m).mp hm) (sort_z _)

/-- At `Hc`, `capGas(inj z)` has the value `capGas(inf)`: `capN(z)`'s rest, of `capGas`'s sort. -/
theorem res_injZ : OvlFnRes (cH Hc) oCap [injZ] (some capGasInf) := by
  have h := OvlFnRes.fn (cover_H Hc) (eval_z Hc)
  rw [rest_Hc] at h
  exact h

/-- At `Hc`, `capGas(inf)` has the value `capGas(inf)`: no overload covers `inf`. -/
theorem res_inf : OvlFnRes (cH Hc) oCap [infT] (some capGasInf) := by
  have h := OvlFnRes.norm (c := cH Hc) (o := oCap) (vs := [infT]) cover_inf
  rw [norm_inf] at h
  exact h

/-- **`OvlFnInj` fails at `Hc`.** -/
theorem not_inj : ¬ OvlFnInj (cH Hc) oCap := fun h =>
  absurd (h [injZ] [infT] _ (sorts_injZ _) sorts_inf res_injZ res_inf) (by simp [injZ, infT])

/-- **At `Hc`, no model of `Γc` satisfies the same-constructor sentence of `capGas`**, under
`FnHyp`: `capGas(inj z)` and `capGas(inf)` have one value. -/
theorem inj_refuted (hf : FnHyp (cH Hc)) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γc (cH Hc) →
      ¬ (I ⊧ᴵ (trAxiom [] [] Keep.U.ax59).pat) :=
  ovlFnInj_refuted (coreOKH _) hf (lookup_H _) (inj_shape _) (sorts_injZ _) sorts_inf (by simp [injZ, infT])
    res_injZ res_inf

end Bare

end KCore.TieOvlFnCovTest

#print axioms KCore.Faithful.ovlFnRes_gs
#print axioms KCore.Faithful.ovlFnTotal_atValues
#print axioms KCore.Faithful.ovlFnInj_atValues
#print axioms KCore.Faithful.ovlFnDist_atValues
#print axioms KCore.Faithful.ovlFnTotal_refuted
#print axioms KCore.Faithful.ovlFnInj_refuted
#print axioms KCore.Faithful.ovlFnDist_refuted
#print axioms KCore.Faithful.ovlFnRes_of_F
#print axioms KCore.Faithful.ovlFnInj_of_cov
#print axioms KCore.TieOvlFnCovTest.Lhs.fun_atValues
#print axioms KCore.TieOvlFnCovTest.Lhs.dist_atValues
#print axioms KCore.TieOvlFnCovTest.Lhs.inj_atValues
#print axioms KCore.TieOvlFnCovTest.Lhs.inj_of_cov
#print axioms KCore.TieOvlFnCovTest.Keep.fun_atValues
#print axioms KCore.TieOvlFnCovTest.Keep.res
#print axioms KCore.TieOvlFnCovTest.Keep.res_F
#print axioms KCore.TieOvlFnCovTest.Keep.not_dist
#print axioms KCore.TieOvlFnCovTest.Keep.dist_refuted
#print axioms KCore.TieOvlFnCovTest.Bare.fun_refuted
#print axioms KCore.TieOvlFnCovTest.Bare.not_total
#print axioms KCore.TieOvlFnCovTest.Bare.inj_refuted
#print axioms KCore.TieOvlFnCovTest.Bare.not_inj
#print axioms KCore.TieOvlFnCovTest.Bare.fun_refuted_Γ
