/-
  Fixture e5-ovl-fun (`test/constructs/fixtures/e5-ovl-fun`): `Exp ::= Int`,
  `Exp ::= Exp "+" Exp [symbol(plusExp), overload(plus)]`,
  `Int ::= Int "+" Int [function, symbol(plusInt), overload(plus)]`, `rule I1 + I2 => I1 +Int I2`.
  The text is `f2-examples/e5-ovl-fun.kompile.kore`; sentence numbers are `AxiomDecl.index`: 105 is
  the same-constructor sentence of `plusExp`,
  `plusExp(X0, X1) ∧ plusExp(Y0, Y1) → plusExp(X0 ∧ Y0, X1 ∧ Y1)`; 124 the overload axiom
  `plusExp(inj{Int, Exp}(K0), inj{Int, Exp}(K1)) = inj{Int, Exp}(plusInt(K0, K1))`; 247 `plusInt`'s
  equation `plusInt(I1, I2) = I1 +Int I2`. Run from the package root:
  `lake env lean -j1 test/TieE5OvlFunNoModel.lean`. Every statement is on the literals `kore` and
  `defn`, for every interpretation H of the hooks' parameters.

  `plusExp` overloads the function `plusInt`, so Γ states its injectivity only at the arguments no
  overload covers. At `(inj 1, inj 2)` and `(inj 2, inj 1)`, which `plusInt` covers, the overload
  axiom, `plusInt`'s equation and the value of `+Int` make both applications the element of
  `inj 3`, and sentence 105 then makes `inj 1` and `inj 2` one element.

  - The reading has a model (`consistent`): the functions' hypotheses name no fact (`fnHyp`).
  - No model of Γ satisfies sentence 105 as the text writes it (`inj_refuted`):
    `plusExp(inj 1, inj 2)` and `plusExp(inj 2, inj 1)` have the one value `inj 3` (`res12`,
    `res21`), so in a model of Γ both applications hold its element, and the elements of different
    values are different. The text reads no confined sort (`confined`), so `Γc` is `Γ` and the
    refutation is against Γ.

  So sentence 105 has no model with KCore's theory, which has one. That the text's own sentences
  have none is not shown: their refutation needs two different elements of Int and the injectivity
  of `inj{Int, Exp}`, which no sentence of the text states (the commutativity of `+Int`, sentence
  156, stands in for its graph). The statement from the translated sentences (105, 124, 247, 156
  and the functional sentences of `+Int` and `inj{Int, Exp}`) with the distinct elements of distinct
  values and the injection's injectivity, and no other item of Γ, is not shown here.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE5OvlFunNoModel

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e5-ovl-fun.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fun.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun.kompile.kore" module "E5-OVL-FUN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- A sentence of the text, as a tie translates it. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

def expS : Srt := 32
/-- `_+Int_`, the hooked addition. -/
def intAdd : Sym := 12
def plusInt : Sym := 385
def plusExp : Sym := 386

theorem names : c.sortName expS = "Exp" ∧ c.symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧
    c.symName plusInt = "LblplusInt" ∧ c.symName plusExp = "LblplusExp" := by decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The text reads no confined sort: `Γc` is `Γ`. -/
theorem confined : c.readsConfined = false := by decide +kernel
theorem confinedH (H : HookParams) : (cH H).readsConfined = false :=
  (Semantics.readsConfined_withHooks c H).trans confined

/-! ## The reading -/

/-- `plusInt(I1, I2) = I1 +Int I2`. -/
def plusCl : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0, .var 1], req := none, rhs := .app intAdd [.var 0, .var 1], ens := none }
/-- `plusInt : Int × Int → Int`, not declared total. -/
def plusIntFn : Fn := ⟨plusInt, [Srt.int, Srt.int], Srt.int, [plusCl], false⟩
def plusIntSig : CtorSig := ⟨plusInt, [Srt.int, Srt.int], Srt.int⟩
def plusExpSig : CtorSig := ⟨plusExp, [expS, expS], expS⟩
/-- `plusExp` overloads `plusInt`. -/
def oPlus : OvlSig := ⟨plusExpSig, [plusInt]⟩

kernel_rfl fns_c : c.fns = [plusIntFn]
kernel_rfl ovls_c : c.ovls = [oPlus]

/-- **The reading**: `plusInt`'s one clause, `plusExp` overloading it, `plusExp` function-overloaded. -/
theorem reading : c.fns = [plusIntFn] ∧ c.ovls = [oPlus] ∧ c.fnOvlSyms = [plusExp] :=
  ⟨fns_c, ovls_c, by decide +kernel⟩

/-- The text's sentences named here, by `AxiomDecl.index`. -/
theorem text_ax : U.ax105.index = 105 ∧ U.ax124.index = 124 ∧ U.ax247.index = 247 := ⟨rfl, rfl, rfl⟩

/-! ## `FnHyp` and `Consistent`, for every H -/

def callOrder : List Nat := [plusInt]

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

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
   openDecided_of_readsConfined (confinedH H),
   openLaws_of_plain (c := cH H) noRaw⟩

/-- **`FnHyp`**, for every H: no fact is named (`plusInt` is not declared total and calls `+Int`
only). -/
theorem fnHyp (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **`Consistent`**, for every H: the reading has a model. -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHyp H)

/-! ## `plusInt` and `plusExp` at values -/

def int (n : Int) : GroundTerm := .dv Srt.int (.int n)
/-- `inj{Int, Exp}(n)` -/
def injI (n : Int) : GroundTerm := .inj Srt.int expS (int n)

kernel_rfl lookup_H : ∀ H : HookParams, (cH H).lookupOvl oPlus.sig.name = some oPlus
kernel_rfl toK_H : ∀ H : HookParams, Gen.toK (cH H) (.ctor oPlus.sig) = Gen.toK c (.ctor oPlus.sig)
kernel_rfl lookupFn_H : ∀ H : HookParams, (cH H).lookupFn plusInt = some plusIntFn
kernel_rfl isCtor_H : ∀ H : HookParams, (cH H).isCtor intAdd = false
kernel_rfl sort_int_H : ∀ (H : HookParams) (n : Int), (cH H).sortOf (int n) = some Srt.int
kernel_rfl sorts_12 : ∀ H : HookParams, (cH H).sortsOf [injI 1, injI 2] = some oPlus.sig.args
kernel_rfl sorts_21 : ∀ H : HookParams, (cH H).sortsOf [injI 2, injI 1] = some oPlus.sig.args
-- `plusInt` covers `(inj 1, inj 2)` and `(inj 2, inj 1)`.
kernel_rfl cover_12 : ∀ H : HookParams, (cH H).fnCover oPlus.sig.name [injI 1, injI 2] = some plusIntSig
kernel_rfl cover_21 : ∀ H : HookParams, (cH H).fnCover oPlus.sig.name [injI 2, injI 1] = some plusIntSig

/-- **`plusInt(a, b)` evaluates to the value of `a +Int b`**, by its one clause. -/
theorem eval_plus (H : HookParams) {a b : Int} {v : GroundTerm}
    (hh : hook intAdd [int a, int b] = some (some v)) : Eval (cH H) plusInt [int a, int b] (some v) :=
  .clause (cl := plusCl) (σ := [(0, int a), (1, int b)]) (lookupFn_H H) (List.mem_singleton_self _)
    (fun i s' h => by
      match i, h with
      | 0, h => cases h; exact ⟨_, rfl, sort_int_H H a⟩
      | 1, h => cases h; exact ⟨_, rfl, sort_int_H H b⟩
      | i + 2, h => simp [plusCl] at h)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun t ht => by cases ht) .top
    (fun cl' h _ hlt => by
      rw [show plusIntFn.clauses = [plusCl] from rfl, List.mem_singleton] at h
      rw [h] at hlt
      exact absurd hlt (Nat.lt_irrefl _))
    rfl
    (.hook (rs := [some (int a), some (int b)]) (isCtor_H H) rfl
      (.cons .var (.cons .var .nil))
      (fun vs h => by cases h; exact Semantics.hookRes_of_value hh)
      (fun h => by cases h))
    (fun t ht => by cases ht) .top

/-- **`plusExp(inj 1, inj 2)` has the value `inj 3`**: `plusInt` covers the arguments, and
`plusInt(1, 2)` is `3`. -/
theorem res12 (H : HookParams) : OvlFnRes (cH H) oPlus [injI 1, injI 2] (some (injI 3)) :=
  OvlFnRes.fn (cover_12 H) (eval_plus H (a := 1) (b := 2) (v := int 3) (by decide +kernel))

/-- **`plusExp(inj 2, inj 1)` has the same value `inj 3`.** -/
theorem res21 (H : HookParams) : OvlFnRes (cH H) oPlus [injI 2, injI 1] (some (injI 3)) :=
  OvlFnRes.fn (cover_21 H) (eval_plus H (a := 2) (b := 1) (v := int 3) (by decide +kernel))

theorem args_ne : [injI 1, injI 2] ≠ [injI 2, injI 1] := by simp [injI, int]

/-- **`OvlFnInj plusExp` fails**, at every interpretation. -/
theorem not_inj (H : HookParams) : ¬ OvlFnInj (cH H) oPlus :=
  fun h => args_ne (h _ _ _ (sorts_12 H) (sorts_21 H) (res12 H) (res21 H))

/-! ## The same-constructor sentence of `plusExp`, as written -/

theorem inj_shape0 : tieOvlFnInjShapeB c expS (Gen.toK c (.ctor oPlus.sig)) U.ax105.ax = true := by decide +kernel

theorem inj_shape (H : HookParams) :
    tieOvlFnInjShapeB (cH H) oPlus.sig.result (Gen.toK (cH H) (.ctor oPlus.sig)) U.ax105.ax = true := by
  rw [toK_H H]
  exact (tieOvlFnInjShapeB_withHooks c H _ _ _).trans inj_shape0

/-- The sentence's translation reads none of the text's declarations. -/
theorem inj_trS : (trS U.ax105).pat = (trAxiom [] [] U.ax105).pat := by decide +kernel

/-- **No model of Γ satisfies the same-constructor sentence of `plusExp`**
(`plusExp(X0, X1) ∧ plusExp(Y0, Y1) → plusExp(X0 ∧ Y0, X1 ∧ Y1)`, sentence 105), for every H:
`plusExp(inj 1, inj 2)` and `plusExp(inj 2, inj 1)` are both `inj 3`. -/
theorem inj_refuted (H : HookParams) :
    ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax105).pat) := by
  intro M inst I hI
  rw [inj_trS]
  have hIc : I ⊧ᴵP Γc (cH H) := by rw [Γc_plain (confinedH H)]; exact hI
  exact ovlFnInj_refuted (coreOKH H) (fnHyp H) (lookup_H H) (inj_shape H) (sorts_12 H) (sorts_21 H) args_ne
    (res12 H) (res21 H) M inst I hIc

/-- info: 'KCore.TieE5OvlFunNoModel.inj_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inj_refuted
/-- info: 'KCore.TieE5OvlFunNoModel.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms consistent
/-- info: 'KCore.TieE5OvlFunNoModel.not_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_inj

end KCore.TieE5OvlFunNoModel
