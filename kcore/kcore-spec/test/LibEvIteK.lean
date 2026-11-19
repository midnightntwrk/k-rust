/-
  K-EQUAL's two equations of `#if _ #then _ #else _ #fi` (domains.md 2357 and 2358), axioms 239
  and 240 of the text of the fixture e6-ite-k (`f2-examples/e6-ite-k.kompile.kore`: INT and K-EQUAL
  imported, one rule `go => #if 1 <Int 2 #then a ~> b #else .K #fi`), entailed at values for every
  interpretation H. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/LibEvIteK.lean`.

  2357: `#if C #then B1 #else _ #fi => B1 requires C`; 2358: `#if C #then _ #else B2 #fi => B2
  requires notBool C`. The text states both at the sort K (the head `Lblite{SortK{}}`).

  On this text the rule applies `#if` at K, so the reading has it as its one parameter symbol
  `ite{K}` (`iteK`, 387, of arguments Bool, K, K and result K, implemented by the registry's
  `kIte`; `params_ite`), a symbol of Γ applied at the head `Lblite{SortK{}}` (`ite_k_in_gamma`), and
  every head the two equations apply is one of Γ's (`heads_in_gamma`). Its value at a Bool literal
  and two values of sort K is the second or the third (`Semantics.paramVal`, `paramVal_ite`), which
  no interpretation H changes; `notBool` is an interpreted hooked symbol.
  - `E239`, `E240`: the equations in the function form over terms applying the parameter symbol
    (`LibEv.FnEqn`, `LibEv.koreP`); `pattern239`, `pattern240`: the axioms' patterns are theirs.
  - `holds239`, `holds240`: their sides have the same value (`LibEv.valP`) at every substitution
    meeting their `requires`, for every H.
  - `ev239`, `ev240`: entailed at values for every H (`LibEv.FnEqn.entailedP`).
  - `consistent`: Γ of the text has a model for every H (`FnHyp` holds for every H: the reading
    has no function and its one parameter symbol is implemented).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.LibEvIteK

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/e6-ite-k.kompile.kore"
definition_of defn from "f2-examples/e6-ite-k.kompile.kore"
user_axioms U from "f2-examples/e6-ite-k.kompile.kore" module "E6-ITE-K"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-! ## The parameter symbol `ite{K}` and Γ's heads -/

/-- The parameter symbol `ite{K}`. -/
abbrev iteK : Sym := 387

/-- The head at which the text applies `ite` at K. -/
def iteKHead : String × List Kore.KSort := ("Lblite", [KoreAML.srt "K"])

/-- The axiom applies `ite` at K. -/
def appliesIteK (ad : AxiomDecl) : Bool := (appHeadsOf ad.ax.pattern).any (fun h => decide (h = iteKHead))

/-- The sentences of the user module applying `ite` at K: the fixture's rule (153) and K-EQUAL's
two equations. -/
theorem ite_k_sentences : (U.all.filter appliesIteK).map (·.index) = [153, 239, 240] := by
  decide +kernel

/-- **The reading's parameter symbols**: one, `ite{K}`, `Bool × K × K → K`, implemented by
`kIte`. -/
theorem params_ite :
    (c.params.map fun k => (k.sig.name, c.symName k.sig.name, k.sig.args, k.sig.result, k.impl)) =
      [(iteK, Parse.iteName "K", [Srt.bool, Srt.k, Srt.k], Srt.k, some kIte)] := by
  decide +kernel

kernel_rfl gammaHeads_withHooks : ∀ (c : Semantics) (H : HookParams), gammaHeads (c.withHooks H) = gammaHeads c
kernel_rfl kernelSyms_withHooks : ∀ (c : Semantics) (H : HookParams), kernelSyms (c.withHooks H) = kernelSyms c

theorem ite_k_in_gamma_c :
    (kernelSyms c).any (fun k => c.symName k.name == Parse.iteName "K") = true ∧
    gammaHasHead c iteKHead = true ∧
    (appHeadsOf U.ax239.ax.pattern).all (gammaHasHead c) = true ∧
    (appHeadsOf U.ax240.ax.pattern).all (gammaHasHead c) = true := by
  decide +kernel

/-- **Γ holds `ite{K}`**, for every H: a symbol of Γ under the name `ite{K}`, applied at the head
`Lblite{SortK{}}`. -/
theorem ite_k_in_gamma (H : HookParams) :
    (kernelSyms (cH H)).any (fun k => (cH H).symName k.name == Parse.iteName "K") = true ∧
    gammaHasHead (cH H) iteKHead = true := by
  rw [kernelSyms_withHooks]
  unfold gammaHasHead
  rw [gammaHeads_withHooks]
  exact ⟨ite_k_in_gamma_c.1, ite_k_in_gamma_c.2.1⟩

/-- The heads the two equations apply, each with its sort arguments. -/
noncomputable def eqnHeads : List (String × List Kore.KSort) :=
  appHeadsOf U.ax239.ax.pattern ++ appHeadsOf U.ax240.ax.pattern

/-- Every head the two equations apply, with its sort arguments, is one of Γ's, for every H. -/
theorem heads_in_gamma (H : HookParams) : eqnHeads.all (gammaHasHead (cH H)) = true := by
  unfold gammaHasHead
  rw [gammaHeads_withHooks]
  show (appHeadsOf U.ax239.ax.pattern ++ appHeadsOf U.ax240.ax.pattern).all _ = true
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨ite_k_in_gamma_c.2.2.1, ite_k_in_gamma_c.2.2.2⟩

kernel_rfl lookupIte : ∀ H : HookParams,
  ((cH H).lookupParam iteK).map (fun k => (k.impl, k.sig.result)) = some (some kIte, Srt.k)

/-! ## Γ of the text has a model, for every H -/

theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H.** -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-! ## The equations -/

/-- 2357 in the function form. -/
def E239 : FnEqn :=
  { vars := [("VarC", Srt.bool), ("VarB1", Srt.k), ("Var'Unds'Gen0", Srt.k)], f := iteK,
    pats := [(Srt.bool, .var 0, none), (Srt.k, .var 1, none), (Srt.k, .var 2, none)],
    s := Srt.k, req := some (.var 0), rhs := .var 1 }

/-- 2358 in the function form. -/
def E240 : FnEqn :=
  { vars := [("VarC", Srt.bool), ("Var'Unds'Gen0", Srt.k), ("VarB2", Srt.k)], f := iteK,
    pats := [(Srt.bool, .var 0, none), (Srt.k, .var 1, none), (Srt.k, .var 2, none)],
    s := Srt.k, req := some (.app boolNot [.var 0]), rhs := .var 2 }

kernel_rfl pattern239 : ∀ H : HookParams, U.ax239.ax.pattern = E239.patternP (cH H)
kernel_rfl typed239 : ∀ H : HookParams, E239.typedP (cH H) = true
kernel_rfl pattern240 : ∀ H : HookParams, U.ax240.ax.pattern = E240.patternP (cH H)
kernel_rfl typed240 : ∀ H : HookParams, E240.typedP (cH H) = true

theorem sortVars : U.ax239.ax.sortVars = [KoreAML.Rv] ∧ U.ax240.ax.sortVars = [KoreAML.Rv] := by decide +kernel

kernel_rfl vkey_withHooks : ∀ (H : HookParams) (vars : Vars) (i : Nat), vkey (cH H) vars i = vkey c vars i

theorem free239 : ∀ i, i < E239.av.length → vkey c E239.av i ∈ KoreAML.freeOf [] U.ax239.ax.pattern := by
  decide +kernel
theorem free240 : ∀ i, i < E240.av.length → vkey c E240.av i ∈ KoreAML.freeOf [] U.ax240.ax.pattern := by
  decide +kernel

/-! ## Γ's values of the heads -/

kernel_rfl appValIte' : ∀ (H : HookParams) (ws : List GroundTerm),
  appValP (cH H) iteK ws = (cH H).paramVal iteK ws

theorem appValIte (H : HookParams) : appValP (cH H) iteK = (cH H).paramVal iteK := funext (appValIte' H)

theorem appValNot (H : HookParams) : appValP (cH H) boolNot = (cH H).hv boolNot := by
  funext ws
  unfold appValP
  rw [(by decide +kernel : lookupSig hookSigs boolNot = some ⟨boolNot, [Srt.bool], Srt.bool⟩)]

/-- `ite{K}` at a Bool literal and two values, the chosen one of sort K. -/
theorem pvIte (H : HookParams) (b : Bool) {x y : GroundTerm}
    (hz : (cH H).sortOf (if b then x else y) = some Srt.k) :
    (cH H).paramVal iteK [bool b, x, y] = some (if b then x else y) := by
  have hl := lookupIte H
  cases hk : (cH H).lookupParam iteK with
  | none => rw [hk] at hl; cases hl
  | some k =>
    rw [hk] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    exact paramVal_ite (c := cH H) hk hl.1 b (by rw [hl.2]; exact hz)

theorem hvNot (H : HookParams) (b : Bool) : (cH H).hv boolNot [bool b] = some (bool (!b)) :=
  hv_of_value rfl

theorem bool_inj {a b : Bool} (h : bool a = bool b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- 2357 holds: where C is `true`, `ite{K}(C, B1, _)` is B1. -/
theorem holds239 (H : HookParams) : E239.HoldsP (cH H) := by
  intro σ hσ hreq hm
  obtain ⟨v0, h0, -⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, s1⟩ := hσ 1 _ rfl
  obtain ⟨v2, h2, -⟩ := hσ 2 _ rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  rw [fq_valP_var] at h3 h4 h5
  have hq := hreq _ rfl
  rw [fq_valP_var, h0] at hq
  cases hq
  show valP (cH H) σ (.app iteK [.var 3, .var 4, .var 5]) = valP (cH H) σ (.var 1)
  have e3 : List.lookup 3 σ = some _ := h3.symm.trans h0
  have e4 : List.lookup 4 σ = some v1 := h4.symm.trans h1
  have e5 : List.lookup 5 σ = some v2 := h5.symm.trans h2
  have e1 : List.lookup 1 σ = some v1 := h1
  simp only [valP, valPList, allSome, appValIte]
  rw [e3, e4, e5, e1]
  simp only [Option.bind_some, Option.map_some]
  exact pvIte H true s1

/-- 2358 holds: where `notBool C` is `true`, `ite{K}(C, _, B2)` is B2. -/
theorem holds240 (H : HookParams) : E240.HoldsP (cH H) := by
  intro σ hσ hreq hm
  obtain ⟨v0, h0, s0⟩ := hσ 0 _ rfl
  obtain ⟨v1, h1, -⟩ := hσ 1 _ rfl
  obtain ⟨v2, h2, s2⟩ := hσ 2 _ rfl
  obtain ⟨h3, -, h4, -, h5, -, -⟩ := hm
  rw [fq_valP_var] at h3 h4 h5
  obtain ⟨b, rfl⟩ := shape_bool (shapesOKH H) s0
  have hq := hreq _ rfl
  simp only [valP, valPList, allSome, h0, Option.bind_some, Option.map_some, appValNot, hvNot] at hq
  have hb : b = false := by
    have := bool_inj (Option.some.inj hq)
    cases b <;> first | rfl | cases this
  subst hb
  show valP (cH H) σ (.app iteK [.var 3, .var 4, .var 5]) = valP (cH H) σ (.var 2)
  have e3 : List.lookup 3 σ = some _ := h3.symm.trans h0
  have e4 : List.lookup 4 σ = some v1 := h4.symm.trans h1
  have e5 : List.lookup 5 σ = some v2 := h5.symm.trans h2
  have e2 : List.lookup 2 σ = some v2 := h2
  simp only [valP, valPList, allSome, appValIte]
  rw [e3, e4, e5, e2]
  simp only [Option.bind_some, Option.map_some]
  exact pvIte H false s2

/-! ## Entailed at values -/

/-- **2357** `#if C #then B1 #else _ #fi => B1 requires C`, at K: entailed at values for every H. -/
theorem ev239 (H : HookParams) : EntailsAtValues (cH H) U.ax239 (trS U.ax239).pat := by
  rw [(by decide +kernel : (trS U.ax239).pat = (trAxiom [] [] U.ax239).pat)]
  exact FnEqn.entailedP (coreOKH H) E239 (typed239 H) (holds239 H) U.ax239 (pattern239 H) sortVars.1
    (fun i hi => by rw [vkey_withHooks]; exact free239 i hi)

/-- **2358** `#if C #then _ #else B2 #fi => B2 requires notBool C`, at K: entailed at values for
every H. -/
theorem ev240 (H : HookParams) : EntailsAtValues (cH H) U.ax240 (trS U.ax240).pat := by
  rw [(by decide +kernel : (trS U.ax240).pat = (trAxiom [] [] U.ax240).pat)]
  exact FnEqn.entailedP (coreOKH H) E240 (typed240 H) (holds240 H) U.ax240 (pattern240 H) sortVars.2
    (fun i hi => by rw [vkey_withHooks]; exact free240 i hi)

end KCore.LibEvIteK

#check @KCore.LibEvIteK.params_ite
#check @KCore.LibEvIteK.ite_k_in_gamma
#check @KCore.LibEvIteK.heads_in_gamma
#check @KCore.LibEvIteK.consistent
/-- info: 'KCore.LibEvIteK.ev239' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIteK.ev239
/-- info: 'KCore.LibEvIteK.ev240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIteK.ev240
/-- info: 'KCore.LibEvIteK.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.LibEvIteK.consistent
#print axioms KCore.LibEvIteK.params_ite
#print axioms KCore.LibEvIteK.ite_k_in_gamma
#print axioms KCore.LibEvIteK.heads_in_gamma
