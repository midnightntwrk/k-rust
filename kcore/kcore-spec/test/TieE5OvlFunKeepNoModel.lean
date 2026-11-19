/-
  Fixture e5-ovl-fun-keep (`test/constructs/fixtures/e5-ovl-fun-keep`): `N ::= z`,
  `Gas ::= N | inf | cap(Gas) [symbol(capGas), overload(cap)]`,
  `Gas ::= cap(N) [function, total, symbol(capN), overload(cap)]`, `rule cap(z) => inf`. The text is
  `f2-examples/e5-ovl-fun-keep.kompile.kore`; sentence numbers are `AxiomDecl.index`: 59 is the
  different-constructors sentence of `capGas` and `inf`, `¬ (capGas(X0) ∧ inf)`; 102 the overload
  axiom `capGas(inj{N, Gas}(K0)) = capN(K0)`; 104 `capN`'s equation `capN(z) = inf`. Run from the
  package root: `lake env lean -j1 test/TieE5OvlFunKeepNoModel.lean`. Every statement is on the
  literals `kore` and `defn`, for every interpretation H of the hooks' parameters.

  `capGas` overloads the function `capN`, so Γ states its distinctness from `inf` only at the
  arguments no overload covers. At `inj z`, which `capN` covers, the overload axiom and `capN`'s
  equation make `capGas(inj z)` the element of `inf`, and sentence 59 says no element is both.

  - The reading has a model (`consistent`): the one fact the functions' hypotheses name is the
    totality of `capN`, which holds because N holds `z` only (`total_capN`, `fnHyp`).
  - No model of Γ satisfies sentence 59 as the text writes it (`dist_refuted`): `capGas(inj z)` has
    the value `inf` (`res`), so in a model of Γ its application holds `inf`'s element. The text
    reads no confined sort (`confined`), so `Γc` is `Γ` and the refutation is against Γ.

  So the text has no model while KCore's theory of it has one. The statement from the translated
  sentences alone (59, 102, 104 with the signature and the constructor items they need, and no
  other item of Γ) is not shown here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunKeepNoModel

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun-keep.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun-keep.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-keep.kompile.kore" module "E5-OVL-FUN-KEEP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- A sentence of the text, as a tie translates it. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def gasS : Srt := 32
def nS : Srt := 33
def infS : Sym := 386
def zS : Sym := 387
def capN : Sym := 388
def capGas : Sym := 389

theorem names : c.sortName gasS = "Gas" ∧ c.sortName nS = "N" ∧ c.symName infS = "Lblinf" ∧
    c.symName zS = "Lblz" ∧ c.symName capN = "LblcapN" ∧ c.symName capGas = "LblcapGas" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text reads no confined sort: `Γc` is `Γ`. -/
theorem confined : c.readsConfined = false := by decide +kernel
theorem confinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans confined

/-! ## The reading -/

/-- `capN(z) = inf`. -/
def capCl : Clause := { vars := [], pats := [.app zS []], req := none, rhs := .app infS [], ens := none }
/-- `capN : N → Gas`, declared total. -/
def capNFn : Fn := ⟨capN, [nS], gasS, [capCl], true⟩
def capNSig : CtorSig := ⟨capN, [nS], gasS⟩
def capGasSig : CtorSig := ⟨capGas, [gasS], gasS⟩
def infSig : CtorSig := ⟨infS, [], gasS⟩
def zSig : CtorSig := ⟨zS, [], nS⟩
/-- `capGas` overloads `capN`. -/
def oCap : OvlSig := ⟨capGasSig, [capN]⟩

kernel_rfl fns_c : c.fns = [capNFn]
kernel_rfl ovls_c : c.ovls = [oCap]

/-- **The reading**: `capN`'s one clause, `capGas` overloading it, `capGas` function-overloaded. -/
theorem reading : c.fns = [capNFn] ∧ c.ovls = [oCap] ∧ c.fnOvlSyms = [capGas] :=
  ⟨fns_c, ovls_c, by decide +kernel⟩

/-- The text's sentences named here, by `AxiomDecl.index`. -/
theorem text_ax : U.ax59.index = 59 ∧ U.ax102.index = 102 ∧ U.ax104.index = 104 := ⟨rfl, rfl, rfl⟩

def zT : GroundTerm := .ctor zS []
def infT : GroundTerm := .ctor infS []
/-- `inj{N, Gas}(z)` -/
def injZ : GroundTerm := .inj nS gasS zT

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oCap.sig.name = some oCap
kernel_rfl inf_H : ∀ H : HookParams, lookupSig (cH H).ctorSigs infSig.name = some infSig
kernel_rfl toK_H : ∀ H : HookParams, (Gen.toK (cH H) (.ctor oCap.sig), Gen.toK (cH H) (.ctor infSig)) =
  (Gen.toK c (.ctor oCap.sig), Gen.toK c (.ctor infSig))
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn capN = some capNFn
kernel_rfl isCtor_H : ∀ H : HookParams, ((cH H).isCtor zS, (cH H).isCtor infS) = (true, true)
kernel_rfl sorts_injZ : ∀ H : HookParams, (cH H).sortsOf [injZ] = some oCap.sig.args
kernel_rfl sorts_nil : ∀ H : HookParams, (cH H).sortsOf [] = some infSig.args
-- `capN` covers `inj z`.
kernel_rfl cover_H : ∀ H : HookParams, (cH H).fnCover oCap.sig.name [injZ] = some capNSig

/-! ## `capN(z)` and `capGas(inj z)` at values -/

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

/-- **`OvlFnDist capGas inf` fails**, at every interpretation. -/
theorem not_dist (H : HookParams) : ¬ OvlFnDist (cH H) oCap infSig :=
  fun h => h [injZ] [] (sorts_injZ H) (sorts_nil H) (res H)

/-! ## `FnHyp` and `Consistent`, for every H -/

/-- A sort whose one generator is a constant holds that constant only: no other constructor, no
overloading symbol and no raw parameter ends at it, nothing is below it, and it has neither
literals nor collections. -/
theorem onlyConst_wcnm {c : Semantics} {s : Srt} {k0 : CtorSig} (ha : k0.args = [])
    (hk : ∀ k ∈ c.ctorSigs, k.result = s → k = k0)
    (ho : ∀ o ∈ c.ovls, o.sig.result ≠ s)
    (hp : ∀ k ∈ c.params, k.raw = false)
    (hsub : ∀ p ∈ c.subsorts, p.2 ≠ s)
    (hdv : ∀ lit, dvOK c.lib s lit = false)
    (hcoll : c.collOf s = none)
    {v : GroundTerm} (h : c.sortOf v = some s) : v = .ctor k0.name [] := by
  cases v with
  | ctor f ts =>
    rcases c.sortOf_ctor_iff.mp h with ⟨k, hk', hs, hr⟩ | ⟨-, o, hlo, -, -, hr⟩ | ⟨-, -, k, hko, -⟩
    · obtain ⟨hm, hn⟩ := lookupSig_spec hk'
      have := hk k hm hr.symm
      subst this
      rw [ha] at hs
      rw [sortsOf_inv_nil hs, hn]
    · obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
      exact absurd hr.symm (ho o (he ▸ List.getElem_mem hi))
    · obtain ⟨hm, hraw, -⟩ := Semantics.lookupOpen_spec _ hko
      rw [hp k hm] at hraw; cases hraw
  | inj a b t =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact absurd rfl (hsub _ (List.contains_iff_mem.mp hc.1.1))
    · cases h
  | dv s' lit =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc; cases h; rw [hdv lit] at hc; cases hc
    · cases h
  | map s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_map_sort h
    rw [hcoll] at hc; cases hc
  | set s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_set_sort h
    rw [hcoll] at hc; cases hc
  | list s' es =>
    obtain ⟨rfl, hc⟩ := sortOf_list_sort h
    rw [hcoll] at hc; cases hc

/-- A sort that is no carrier of literals has none. -/
theorem noLit_wcnm {l : Lib} {s : Srt}
    (h : (l.carrier s == Srt.int || l.carrier s == Srt.bool || l.carrier s == Srt.kconfigVar ||
      l.carrier s == Srt.string || l.tokenSorts.contains (l.carrier s) || l.carrier s == Srt.bytes ||
      l.byteSorts.contains (l.carrier s) || l.carrier s == Srt.float) = false) (lit : Lit) :
    dvOK l s lit = false := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases lit <;> simp only [dvOK, h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_and, Bool.or_self]

/-- N holds `z` only. -/
theorem val_N {v : GroundTerm} (h : c.sortOf v = some nS) : v = zT :=
  onlyConst_wcnm (k0 := zSig) rfl (by decide +kernel) (by decide +kernel) noRaw (by decide +kernel)
    (noLit_wcnm (by decide +kernel)) (by decide +kernel) h

def callOrder : List Nat := [capN]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
/-- The totality decider does not confirm `capN`: its totality is the named fact, proved below. -/
theorem total_named : c.totalObligationsRP callOrder [] = [capN] := by decide +kernel

/-- **`capN` is `Total`, for every H**: its one clause decides at `z`, the one value of N. -/
theorem total_capN (H : HookParams) : Total (cH H) capN := fun fn' hfn' vs hvs => by
  obtain rfl : fn' = capNFn := Option.some.inj (hfn'.symm.trans (lookupFn_H H))
  rw [show capNFn.args = [nS] from rfl, Semantics.sortsOf_withHooks _ _ noRaw] at hvs
  obtain ⟨w, ws', rfl, hw, hws⟩ := sortsOf_inv_cons hvs
  cases sortsOf_inv_nil hws
  cases val_N hw
  exact ⟨_, eval_z H⟩

/-- The facts the deciders leave hold, for every H: the one named is the totality of `capN`. -/
theorem obl (H : HookParams) : FnObligations (cH H) callOrder [] :=
  have h1 : (cH H).rankObligations callOrder ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP callOrder [] = [capN] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; rw [List.mem_singleton.mp hf]; exact total_capN H,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_readsConfined (confinedH H),
   openLaws_of_plain (c := cH H) noRaw⟩

/-- **`FnHyp`**, for every H. -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl H)

/-- **`Consistent`**, for every H: the reading has a model. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

/-! ## The different-constructors sentence of `capGas` and `inf`, as written -/

theorem dist_shape0 : tieOvlFnDistShapeB c gasS (Gen.toK c (.ctor oCap.sig)) (Gen.toK c (.ctor infSig)) U.ax59.ax = true := by
  decide +kernel

theorem dist_shape (H : HookParams) :
    tieOvlFnDistShapeB (cH H) oCap.sig.result (Gen.toK (cH H) (.ctor oCap.sig)) (Gen.toK (cH H) (.ctor infSig))
      U.ax59.ax = true := by
  rw [(Prod.mk.inj (toK_H H)).1, (Prod.mk.inj (toK_H H)).2]
  exact (tieOvlFnDistShapeB_withHooks c H _ _ _ _).trans dist_shape0

/-- The sentence's translation reads none of the text's declarations. -/
theorem dist_trS : (trS U.ax59).pat = (trAxiom [] [] U.ax59).pat := by decide +kernel

/-- **No model of Γ satisfies the different-constructors sentence of `capGas` and `inf`**
(`\not(\and(LblcapGas(X0), Lblinf()))`, sentence 59), for every H: `capGas(inj z)` is `inf`. -/
theorem dist_refuted (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax59).pat) := by
  intro M inst I hI
  rw [dist_trS]
  have hIc : I ⊧ᴵP Γc (cH H) := by rw [Γc_plain (confinedH H)]; exact hI
  exact ovlFnDist_refuted (coreOKH H) (fnHyp H) (lookup_H H) (inf_H H) rfl (dist_shape H) (sorts_injZ H)
    (sorts_nil H) (res H) M inst I hIc

/-- info: 'KCore.TieE5OvlFunKeepNoModel.dist_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dist_refuted
/-- info: 'KCore.TieE5OvlFunKeepNoModel.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent
/-- info: 'KCore.TieE5OvlFunKeepNoModel.not_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_dist

end KCore.TieE5OvlFunKeepNoModel
