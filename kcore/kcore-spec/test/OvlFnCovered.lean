/-
  A function-overloaded symbol at a covered argument where the covering function has no value, on
  K 7.1.337 kompile's KORE of the fixture e5-ovl-fun-partial (test/constructs/fixtures/NAME; the
  kompiled text in f2-examples with its paths restored). Run from the package root:
  `lake env lean -j1 test/OvlFnCovered.lean`. Every statement is on the literal `defn`; nothing
  reads `Parse.parse`.

  The text: `N ::= z | y`, `Gas ::= N | cap(Gas) [symbol(capGas), overload(cap)]`,
  `N ::= cap(N) [function, symbol(capN), overload(cap)]` (not total), `rule cap(z) => z`.
  `capGas` overloads the function `capN`, so it is function-overloaded (`fnOvlSyms`), and Γ states
  its Cons-Fun, Cons-Inj and Cons-Dist items only at the arguments no overload covers. `capN` has
  one clause, `capN(z #as G0) = G0`, which fails at `y`.

  - The reading (`reading`): `coreOK`; `capN`'s one clause; `capGas` overloading `capN`.
  - `FnHyp` for every H (no obligation is named; `capN` is not total, so its result at `y` may be
    none), hence `Consistent` for every H, in particular at `HookParams.none`.
  - At every H whose rest gives `capN` nothing at `[y]` (`HookParams.none` is one,
    `Semantics.fnRest_withHooks_none`), Γ states `capN(y) ≡ ⊥` (`ΓFallback`'s item of `capN` at
    `[y]`) and, by the overload equation `capGas(inj x) = inj(capN(x))`, `capGas(inj y) ≡ ⊥`
    (`capGasInjY_bot`).
  - There **no model of Γ satisfies the text's `functional` sentence of `capGas`** as written,
    `∃ Val:Gas. Val = capGas(K0:Gas)` (axiom index 57, sentence 157 of the main module, line 30 of
    the fixture's kore.txt): read at `K0 := inj y` it makes `capGas(inj y)` one element
    (`TieFR.one_of_fnl`). `fnl_refuted_none` at `HookParams.none`, where `Consistent` holds: the
    refutation is not vacuous.
  - At the H whose rest gives `capN` the value `z` (`Hz`), Γ states `capN(y) ≡ z`; at the one whose
    rest gives `y` (`Hy`), `capN(y) ≡ y` (`capNY_Hz`, `capNY_Hy`).

  The text with its sentences and with `inj{N, Gas}` functional and injective has `capN(y) = y`
  (the functional sentence of `capGas` at `inj y` with the overload axiom: `capN(y)` is one element;
  N's no-junk sentence: it is `z` or `y`; the rule's equation `capN(z) = z`, the distinctness of
  `y` and `z` and the same-constructor sentence of `capGas`: it is not `z`). So of the three only
  `Hy` agrees with the text. That argument is not kernel-checked here: the text's sentences are not
  read as facts beside the functional one.

  Row: E2 `OVERLOAD(overload)@frontend`, note `overloadFunction`. This is a test of the note (C14,
  the failing theorem), not evidence for the row: the reading leaves out of Γ that the covering
  function is total there, and nothing states it as a hypothesis on H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OvlFnCovered

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-partial.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-partial.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-partial.kompile.kore" module "E5-OVL-FUN-PARTIAL"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

-- The axioms the constants `U.axN` hold are the module's.
kernel_rfl U_all : kore.axiomDecls.filter (·.module == "E5-OVL-FUN-PARTIAL") = U.all

/-- A sentence of the text, as a tie translates it. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def gasS : Srt := 32
def nS : Srt := 33
def yS : Sym := 386
def zS : Sym := 387
def capN : Sym := 388
def capGas : Sym := 389

theorem names : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName yS = "Lbly" ∧
    c.symName zS = "Lblz" ∧ c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem wf_defn : wf defn = true := by decide_cheap
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-! ## The reading -/

/-- `capN(z #as G0) = G0`. -/
def capCl : Clause := { vars := [nS], pats := [.as (.app zS []) 0], req := none, rhs := .var 0, ens := none }
/-- `capN : N → N`, not total. -/
def capNFn : Fn := ⟨capN, [nS], nS, [capCl], false⟩
def capNSig : CtorSig := ⟨capN, [nS], nS⟩
def capGasSig : CtorSig := ⟨capGas, [gasS], gasS⟩
/-- `capGas` overloads `capN`. -/
def oCap : OvlSig := ⟨capGasSig, [capN]⟩

kernel_rfl fns_c : c.fns = [capNFn]
kernel_rfl ovls_c : c.ovls = [oCap]

/-- **The reading**: `capN`'s one clause, `capGas` overloading it, `capGas` function-overloaded. -/
theorem reading : c.fns = [capNFn] ∧ c.ovls = [oCap] ∧ c.fnOvlSyms = [capGas] :=
  ⟨fns_c, ovls_c, by decide +kernel⟩

/-- The text's sentences named here, by `AxiomDecl.index`: 57 the functional sentence of `capGas`
(kore.txt line 30), 101 the overload axiom (line 50). -/
theorem text_ax : U.ax57.index = 57 ∧ U.ax101.index = 101 := ⟨rfl, rfl⟩

/-! ## `FnHyp` and `Consistent`, for every H -/

def callOrder : List Nat := [capN]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel
theorem confined_named : c.readsConfined = false := by decide +kernel

/-- None named, for every H. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_readsConfined ((Semantics.readsConfined_withHooks c H).trans confined_named),
   openLaws_of_plain (c := cH H) noRaw⟩

/-- **`FnHyp`**, for every H. -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **`Consistent`**, for every H. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

theorem fnHyp_none : FnHyp (cH HookParams.none) := fnHyp _
theorem consistent_none : Consistent (cH HookParams.none) := consistent _

/-! ## The values and the facts every H shares -/

def yT : GroundTerm := .ctor yS []
def zT : GroundTerm := .ctor zS []
/-- `inj{N, Gas}(y)` -/
def injY : GroundTerm := .inj nS gasS yT
/-- `capN(y)` -/
def capNY : GroundTerm := .ctor capN [yT]
/-- `capGas(inj{N, Gas}(y))` -/
def capGasInjY : GroundTerm := .ctor capGas [injY]

kernel_rfl sorts_y : ∀ H : HookParams, (cH H).sortsOf [yT] = some capNFn.args
kernel_rfl sorts_injY : ∀ H : HookParams, (cH H).sortsOf [injY] = some capGasSig.args
kernel_rfl sort_y : ∀ H : HookParams, (cH H).sortOf yT = some nS
kernel_rfl sort_z : ∀ H : HookParams, (cH H).sortOf zT = some nS
kernel_rfl sort_injY : ∀ H : HookParams, (cH H).sortOf injY = some gasS
kernel_rfl fns_H : ∀ H : HookParams, (cH H).fns = [capNFn]
kernel_rfl ovls_H : ∀ H : HookParams, (cH H).ovls = [oCap]
kernel_rfl over_H : ∀ H : HookParams, (cH H).ovlOver oCap = [capNSig]
kernel_rfl isCtor_zH : ∀ H : HookParams, (cH H).isCtor zS = true
kernel_rfl gas_lt : ∀ H : HookParams, decide (gasS < nRegSorts + (cH H).sortNames.length) = true
kernel_rfl sortName_gas : ∀ H : HookParams, (cH H).sortName gasS = "Gas"
kernel_rfl sortName_n : ∀ H : HookParams, (cH H).sortName nS = "N"

/-- `capN` and `capGas` as KORE signatures. -/
def capNK : KoreAML.CtorSig := ⟨"LblcapN", ["N"], "N"⟩
def capGasK : KoreAML.CtorSig := ⟨"LblcapGas", ["Gas"], "Gas"⟩

kernel_rfl toK_capN : ∀ H : HookParams, toK (cH H) capNSig = capNK
kernel_rfl toK_capGas : ∀ H : HookParams, toK (cH H) capGasSig = capGasK
-- `ΓFallback` writes `capN(y)` as the application of its symbol: no `ite` instance.
kernel_rfl symApp_capN : ∀ H : HookParams,
  KoreAML.den (symApp (cH H) capNFn.label (GroundTerm.koreList (cH H) [yT])) = den (cH H) capNY

theorem capN_allFns (H : HookParams) : capNFn ∈ (cH H).allFns :=
  List.mem_append_left _ (by rw [fns_H]; exact List.mem_singleton_self _)

theorem hook_z : patternHooks.contains zS = false := by decide

/-- The pattern of `z` denotes `z` only. -/
theorem patVal_z {H : HookParams} {σ : Subst} {v : GroundTerm} (h : PatVal (cH H) σ (.app zS []) v) : v = zT := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => rw [hook_z] at hp; cases hp
  | coll hc _ _ _ => rw [isCtor_zH H] at hc; cases hc
  | ovl hc _ _ _ => rw [isCtor_zH H] at hc; cases hc

/-- **`capN`'s one clause fails at `y`**: its pattern `z #as G0` does not denote `y`. -/
theorem cl_fails (H : HookParams) : ∀ cl ∈ capNFn.clauses, Fails (cH H) [yT] cl := by
  intro cl hcl
  rw [show capNFn.clauses = [capCl] from rfl, List.mem_singleton] at hcl
  subst hcl
  exact .intro fun σ _ hp => by
    cases hp with
    | cons h _ =>
      cases h with
      | as h' _ => exact absurd (patVal_z h') (by simp [yT, zT, yS, zS])

/-! ## In a model of Γ at an H whose rest gives `capN` nothing at `y` -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The element of `capN(y)` is what `capN`'s generator builds from `y`'s. -/
theorem capNY_gs {H : HookParams} (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M) :
    (den (cH H) capNY).interpret I e m ↔ GS I "N" (.ctor capNK) [elemOf (cH H) I yT] m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hgs := den_sig_gs hI (k := capNSig) rfl (sorts_y H) e m
  rw [show Gen.toK (cH H) (.ctor capNSig) = .ctor capNK from congrArg KoreAML.Gen.ctor (toK_capN H),
    show (cH H).sortName capNSig.result = "N" from sortName_n H] at hgs
  exact hgs

/-- The element of `capGas(inj y)` is what `capGas`'s generator builds from `inj y`'s. -/
theorem capGasInjY_gs {H : HookParams} (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) (m : M) :
    (den (cH H) capGasInjY).interpret I e m ↔ GS I "Gas" (.ctor capGasK) [elemOf (cH H) I injY] m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hgs := den_sig_gs hI (k := capGasSig) rfl (sorts_injY H) e m
  rw [show Gen.toK (cH H) (.ctor capGasSig) = .ctor capGasK from congrArg KoreAML.Gen.ctor (toK_capGas H),
    show (cH H).sortName capGasSig.result = "Gas" from sortName_gas H] at hgs
  exact hgs

/-- `capN(y)` holds no element. -/
theorem capNY_empty {H : HookParams} (hI : I ⊧ᴵP Γ (cH H)) (hr : (cH H).fnRest capNFn [yT] = none) (m : M) :
    ¬ GS I "N" (.ctor capNK) [elemOf (cH H) I yT] m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hfb := sat_rest hI (capN_allFns H) (sorts_y H) (cl_fails H)
  rw [hr, symApp_capN H] at hfb
  have h1 := hfb KoreAML.val0 default
  rw [KoreAML.interp_equal hD] at h1
  intro hm
  have hgs := capNY_gs hI KoreAML.val0 m
  exact absurd ((h1 m).mp (hgs.mpr hm)) (by simp)

/-- `capGas(inj y)` holds no element: the overload equation gives it what `inj{N, Gas}` builds
from `capN(y)`'s elements. -/
theorem capGasInjY_empty {H : HookParams} (hI : I ⊧ᴵP Γ (cH H)) (hr : (cH H).fnRest capNFn [yT] = none) (m : M) :
    ¬ GS I "Gas" (.ctor capGasK) [elemOf (cH H) I injY] m := by
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hov : oCap ∈ (cH H).ovls := by rw [ovls_H]; exact List.mem_singleton_self _
  have hkg : capNSig ∈ (cH H).ovlOver oCap := by rw [over_H]; exact List.mem_singleton_self _
  have hit := sat_cons hI (Or.inl ⟨_, ovlEqItem_mem hov hkg, rfl⟩)
  rw [show toK (cH H) oCap.sig = capGasK from toK_capGas H, toK_capN H] at hit
  have hy := elemOf_spec hI (sort_y H) KoreAML.val0
  have hzs : ∀ (i : Nat) x s, [elemOf (cH H) I yT][i]? = some x → capNK.args[i]? = some s → InS I s x := by
    refine single_sorts ?_
    have := (inS_iff (I := I) KoreAML.val0).mp hy.2
    rwa [sortName_n H] at this
  have hys : ∀ (i : Nat) A B z y, capNK.args[i]? = some A → capGasK.args[i]? = some B →
      [elemOf (cH H) I yT][i]? = some z → [elemOf (cH H) I injY][i]? = some y →
      ∀ m, (if A == B then m = z else GS I B (.inj A) [z] m) ↔ m = y := by
    intro i A B z y hA hB hz hy' m'
    match i, hA, hB, hz, hy' with
    | 0, hA, hB, hz, hy' =>
      simp only [capNK, capGasK, List.getElem?_cons_zero, Option.some.injEq] at hA hB hz hy'
      subst hA hB hz hy'
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
      have hinj := den_inj_gs hI (a := nS) (b := gasS) (sort_y H) KoreAML.val0 m'
      rw [sortName_gas H, sortName_n H] at hinj
      exact hinj.symm.trans ((elemOf_spec hI (sort_injY H) KoreAML.val0).1 m')
    | _ + 1, _, hB, _, _ => simp [capGasK] at hB
  have e1 := ovlEq_at hD (N := "Gas") (N' := "N") hit (zs := [elemOf (cH H) I yT])
    (ys := [elemOf (cH H) I injY]) rfl rfl rfl hzs hys m
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at e1
  intro hm
  obtain ⟨x, hx, -⟩ := e1.mp hm
  exact capNY_empty hI hr x hx

end

/-- **Γ states `capN(y) ≡ ⊥`** at every H whose rest gives `capN` nothing at `y` (`ΓFallback`). -/
theorem capNY_bot {H : HookParams} (hr : (cH H).fnRest capNFn [yT] = none) :
    Γ (cH H) ⊧ (den (cH H) capNY ≡ ⊥) := by
  intro M _ I hI e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  rw [KoreAML.interp_equal (defOK hI)]
  intro b
  rw [capNY_gs hI e b]
  exact ⟨fun h => absurd h (capNY_empty hI hr b), fun h => by simp at h⟩

/-- **Γ states `capGas(inj y) ≡ ⊥`** at every H whose rest gives `capN` nothing at `y`. -/
theorem capGasInjY_bot {H : HookParams} (hr : (cH H).fnRest capNFn [yT] = none) :
    Γ (cH H) ⊧ (den (cH H) capGasInjY ≡ ⊥) := by
  intro M _ I hI e m
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  rw [KoreAML.interp_equal (defOK hI)]
  intro b
  rw [capGasInjY_gs hI e b]
  exact ⟨fun h => absurd h (capGasInjY_empty hI hr b), fun h => by simp at h⟩

/-! ## The functional sentence of `capGas`, as written -/

/-- `axiom{R} \exists{R} (Val:SortGas{}, \equals{SortGas{}, R} (Val:SortGas{}, LblcapGas{}(K0:SortGas{})))`. -/
noncomputable abbrev fnlAx : AxiomDecl := U.ax57

noncomputable def tblF : VarTable := tableOf fnlAx.ax.sortVars fnlAx.ax.pattern
noncomputable def rF : EVar := tblF.ev (sortVarKey Rv)
noncomputable def vF : EVar := tblF.ev (evarKey (evar "Val" (srt "Gas")))
noncomputable def k0 : EVar := tblF.ev (evarKey (evar "K0" (srt "Gas")))
def GasP : P := sym (.sort "SortGas")
def hHead : P := sym (.symbol "LblcapGas")
/-- The functional sentence read at its own variable K0. -/
noncomputable def tsF : List (EVar × EVar × P) := [(k0, k0, GasP)]

/-- The sentence's translation: its guards (R a sort, K0 of Gas) imply that `∃ Val:Gas.
Val = capGas(K0)` is the whole of R. -/
theorem fnl_shape : (trS fnlAx).pat =
    TieFR.fnlPat (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF vF GasP
      (appList hHead (tsF.map fun t => .evar t.2.1)) := by
  decide +kernel

theorem idx_facts : (tsF.map (·.2.1)).Nodup ∧ rF ∉ tsF.map (·.2.1) ∧ vF ∉ tsF.map (·.2.1) ∧ vF ≠ rF := by
  decide +kernel

/-- **No model of Γ satisfies the functional sentence of `capGas`**, at every H whose rest gives
`capN` nothing at `y`: read at `K0 := inj y`, it makes `capGas(inj y)` one element of Gas, which
Γ leaves empty. -/
theorem fnl_refuted {H : HookParams} (hr : (cH H).fnRest capNFn [yT] = none) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS fnlAx).pat) := by
  intro M _ I hI hF
  rw [fnl_shape] at hF
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := cH H))
  obtain ⟨σG, hσ1, hσ2⟩ := sortSing hI (s := gasS) (of_decide_eq_true (gas_lt H))
  rw [sortName_gas H] at hσ1
  have hS : ∀ (e : Valuation M) a, GasP.interpret I e a ↔ a = σG := fun e a => by
    rw [GasP, interp_sym]; exact hσ1 a
  obtain ⟨hnd, hrk, hvk, hvr⟩ := idx_facts
  have hkr : k0 ≠ rF := fun h => hrk (by rw [← h]; exact List.mem_singleton_self _)
  let a := elemOf (cH H) I injY
  let e : Valuation M := ⟨fun x => if x = rF then σG else a, fun _ _ => False⟩
  have heR : e.evalEvar rF = σG := by
    show (if rF = rF then σG else a) = σG
    exact ite_eq_left_iff.mpr fun h => absurd rfl h
  have hek : e.evalEvar k0 = a := by
    show (if k0 = rF then σG else a) = a
    exact ite_eq_right_iff.mpr fun h => absurd h hkr
  have hInh : Inh I σG a := by
    have h := (elemOf_spec hI (sort_injY H) e).2
    rw [sortName_gas H] at h
    exact (interp_inhOf_of (hS e)).mp h
  have hat : TieFR.At I (sortGuard rF :: tsF.map fun t => (t.2.1 ∈∈ inhOf t.2.2)) rF e a := by
    refine ⟨fun w hw => ?_, by rw [heR]; exact hInh⟩
    simp only [tsF, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · unfold sortGuard; rw [interp_member hD, interp_sortsDomain, heR]; exact hσ2
    · rw [interp_member hD, hek, interp_inhOf_of (hS e)]; exact hInh
  obtain ⟨y', hy', hone⟩ := TieFR.one_of_fnl hD hc hS hσ2 (List.mem_cons_self ..) hF (Closed.sym _)
    hnd hrk hvk hvr rfl
    (fun t ht => by
      simp only [tsF, List.mem_singleton] at ht
      subst ht
      exact ⟨List.mem_cons_of_mem _ (List.mem_singleton_self _), Closed.sym _⟩) hat
  have h1 := (hone y' hy').mpr rfl
  have h2 := (interp_genPat_vars "Gas" (.ctor capGasK) e [k0] y').mp h1
  rw [List.map_cons, List.map_nil, hek] at h2
  exact capGasInjY_empty hI hr y' h2

/-! ## At `HookParams.none` -/

theorem rest_none : (cH HookParams.none).fnRest capNFn [yT] = none := Semantics.fnRest_withHooks_none c capNFn [yT]

/-- **At `HookParams.none`, Γ states `capN(y) ≡ ⊥` and `capGas(inj y) ≡ ⊥`.** -/
theorem bot_none : (Γ (cH HookParams.none) ⊧ (den (cH HookParams.none) capNY ≡ ⊥)) ∧
    (Γ (cH HookParams.none) ⊧ (den (cH HookParams.none) capGasInjY ≡ ⊥)) :=
  ⟨capNY_bot rest_none, capGasInjY_bot rest_none⟩

/-- **At `HookParams.none`, where Γ has a model and `FnHyp` holds, no model of Γ satisfies the
text's functional sentence of `capGas`.** -/
theorem fnl_refuted_none : Consistent (cH HookParams.none) ∧ FnHyp (cH HookParams.none) ∧
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH HookParams.none) → ¬ (I ⊧ᴵ (trS fnlAx).pat) :=
  ⟨consistent_none, fnHyp_none, fnl_refuted rest_none⟩

/-! ## The rests `z` and `y` -/

/-- The interpretation whose rest of `capN` is `z`. -/
def Hz : HookParams := ⟨fun f _ => if f = capN then some zT else none⟩
/-- The interpretation whose rest of `capN` is `y`. -/
def Hy : HookParams := ⟨fun f _ => if f = capN then some yT else none⟩

kernel_rfl rest_Hz : (cH Hz).fnRest capNFn [yT] = some zT
kernel_rfl rest_Hy : (cH Hy).fnRest capNFn [yT] = some yT

/-- **At `Hz`, Γ states `capN(y) ≡ z`.** -/
theorem capNY_Hz : Γ (cH Hz) ⊧ (den (cH Hz) capNY ≡ den (cH Hz) zT) := by
  intro M _ I hI
  have h := sat_rest hI (capN_allFns Hz) (sorts_y Hz) (cl_fails Hz)
  rw [rest_Hz] at h
  exact h

/-- **At `Hy`, Γ states `capN(y) ≡ y`.** -/
theorem capNY_Hy : Γ (cH Hy) ⊧ (den (cH Hy) capNY ≡ den (cH Hy) yT) := by
  intro M _ I hI
  have h := sat_rest hI (capN_allFns Hy) (sorts_y Hy) (cl_fails Hy)
  rw [rest_Hy] at h
  exact h

/-- info: 'KCore.OvlFnCovered.fnl_refuted_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnl_refuted_none
/-- info: 'KCore.OvlFnCovered.bot_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bot_none
/-- info: 'KCore.OvlFnCovered.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent
/-- info: 'KCore.OvlFnCovered.capNY_Hz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capNY_Hz
/-- info: 'KCore.OvlFnCovered.capNY_Hy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capNY_Hy
/-- info: 'KCore.OvlFnCovered.coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms coreOK

end KCore.OvlFnCovered
