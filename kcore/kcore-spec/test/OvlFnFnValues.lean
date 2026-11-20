/-
  The expectations (C7 form (a)) of the two texts in which a `symbol-overload` axiom is a clause of
  a function: e5-ovl-fn-fn (`negExp : Exp → Exp` over `negInt : Int → Int`) and e5-ovl-fn-fn-ctor
  (`sExp : Exp → Exp` over the constructor `sN : N → N`). Each value is derived for every
  interpretation H from the premise set `TiePair.Pre (cH H) textPats`: the text's function
  sentences as written, but at position 0, where it holds Γ's item of the clause read from the
  overload axiom (`ovlmItem0`); Γ's rule items (none: neither text has a rule); and the families of
  the reading (`TiePair.Families`: the signature, the constructors, the domains with the registry
  hooks' graphs, the collections, the fallback). `shape` states that every other position is Γ's
  equation item. Run from the package root: `lake env lean -j1 test/OvlFnFnValues.lean`. Every
  statement is on the literal `defn` of `f2-examples/FIXTURE.kompile.kore`; nothing reads
  `Parse.parse` or `emit`.

  Γ's item 0 binds the argument by the membership `x ∈ inj{A, Exp}(V0)`, where the overload axiom
  applies the function to that pattern. The text's overload axiom is a consequence of the item
  (`prios_out_entailed0` of the tie), and gives it back in a model with the constructors' facts and
  Cons-Fun of the injection (`ovlm0_from_text` of the tie), not from the axiom alone.

  - `Fn` (e5-ovl-fn-fn, `rule neg(I:Int) => 0 -Int I`, `rule neg(e) => e`, the overload axiom 124
    `negExp(inj x) = inj(negInt(x))`):
    `negExp_inj3`: `negExp(inj 3) = inj(-3)`, through Γ's item of the overload clause, negInt's
    equation 246 as written and the registry's graph of `_-Int_`;
    `negExp_e`: `negExp(e) = e`, from the equation 245 as written.
  - `Ct` (e5-ovl-fn-fn-ctor, `rule s(e) => e`, the overload axiom 130 `sExp(inj x) = inj(sN(x))`):
    `sExp_inj_z`: `sExp(inj z) = inj(sN(z))`, through Γ's item of the overload clause;
    `sExp_e`: `sExp(e) = e`, from the equation 271 as written.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.OvlFnFnValues

open KCore ML Faithful KoreAML

/-! ## e5-ovl-fn-fn -/

namespace Fn

kore_term kore from "f2-examples/e5-ovl-fn-fn.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fn-fn.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn.kompile.kore" module "E5-OVL-FN-FN"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The pins of the alignment, `(item, sentence index)`: the clause read from the overload axiom,
at that axiom. -/
def fnPins : List (Nat × Nat) := [(0, 124)]

/-- The text sentences of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnTextO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all fnPins
noncomputable def fnText : List AxiomDecl := fnTextO.filterMap id

/-- Γ's axiom of item 0, the clause read from the overload axiom. -/
noncomputable def ovlmAx0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
noncomputable def ovlmItem0 : P := (trAxiom [] [] ⟨0, "kernel", ovlmAx0⟩).pat

/-- The premise set's equations: each text sentence's translation, and Γ's item at position 0. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 ovlmItem0

/-- **Each of Γ's equations is the translation of its text sentence**, but item 0 (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

-- The overload axiom 124 is the sentence of position 0.
kernel_rfl fnText_at0 : fnText[0]? = some U.ax124
/-- **Position 0 holds Γ's item, the overload axiom 124 is no premise as written, and the
equations 245 (`negExp(e) = e`) and 246 (`negInt(I) = 0 -Int I`) are premises as written**
(kernel). -/
theorem premises_at : textPats[0]? = some ovlmItem0 ∧
    textPats.contains (trS U.ax124).pat = false ∧
    textPats.contains (trS U.ax245).pat = true ∧ textPats.contains (trS U.ax246).pat = true := by
  decide +kernel

/-- The premises: the function sentences as written but the overload axiom, Γ's item of the
overload clause, Γ's rule items (none) and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

def expS : Srt := 32
def eS : Sym := 385
def negExp : Sym := 386
def negInt : Sym := 387

theorem names : c.sortName expS = "Exp" ∧ c.symName eS = "Lble" ∧ c.symName negExp = "LblnegExp" ∧
    c.symName negInt = "LblnegInt" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn negExp = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn negExp = some fn := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

/-- `inj{Int,Exp}(3)` -/
def i3 : GroundTerm := .inj Srt.int expS (.dv Srt.int (.int 3))
/-- `inj{Int,Exp}(-3)` -/
def im3 : GroundTerm := .inj Srt.int expS (.dv Srt.int (.int (-3)))
/-- `e` -/
def ve : GroundTerm := .ctor eS []

theorem sorts_i3 : c.sortsOf [i3] = some fn.args := by decide +kernel
theorem sorts_e : c.sortsOf [ve] = some fn.args := by decide +kernel
theorem sorts_i3H (H : HookParams) : (cH H).sortsOf [i3] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact sorts_i3
theorem sorts_eH (H : HookParams) : (cH H).sortsOf [ve] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact sorts_e

theorem eval_inj3 (H : HookParams) : Eval (cH H) negExp [i3] (some im3) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_i3 (n := 10) (by decide +kernel)

theorem eval_e (H : HookParams) : Eval (cH H) negExp [ve] (some ve) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_e (n := 10) (by decide +kernel)

/-- **`negExp(inj 3) = inj(-3)`, derived from `Pre`**, for every H: through Γ's item of the
overload clause, then negInt's equation 246 as written and the registry's graph of `_-Int_`. -/
theorem negExp_inj3 (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) negExp [i3] ≡ den (cH H) im3) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_inj3 H) (hfnH H) (sorts_i3H H)

/-- **`negExp(e) = e`, derived from `Pre`**, for every H: from the equation 245 as written. -/
theorem negExp_e (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) negExp [ve] ≡ den (cH H) ve) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_e H) (hfnH H) (sorts_eH H)

end Fn

/-! ## e5-ovl-fn-fn-ctor -/

namespace Ct

kore_term kore from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore"
definition_of defn from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fn-fn-ctor.kompile.kore" module "E5-OVL-FN-FN-CTOR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The pins of the alignment: the clause read from the overload axiom, at that axiom. -/
def fnPins : List (Nat × Nat) := [(0, 130)]

noncomputable def fnTextO : List (Option AxiomDecl) := TiePair.fnTextMany c U.all fnPins
noncomputable def fnText : List AxiomDecl := fnTextO.filterMap id

noncomputable def ovlmAx0 : Kore.Axiom := ((TiePair.fnAxioms c)[0]?).getD ⟨[], .top KoreAML.R, []⟩
noncomputable def ovlmItem0 : P := (trAxiom [] [] ⟨0, "kernel", ovlmAx0⟩).pat

noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set 0 ovlmItem0

/-- **Each of Γ's equations is the translation of its text sentence**, but item 0 (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

-- The overload axiom 130 is the sentence of position 0.
kernel_rfl fnText_at0 : fnText[0]? = some U.ax130
/-- **Position 0 holds Γ's item, the overload axiom 130 is no premise as written, and the
equation 271 (`sExp(e) = e`) is a premise as written** (kernel). -/
theorem premises_at : textPats[0]? = some ovlmItem0 ∧
    textPats.contains (trS U.ax130).pat = false ∧ textPats.contains (trS U.ax271).pat = true := by
  decide +kernel

noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

def nS : Srt := 32
def expS : Srt := 33
def eS : Sym := 386
def sN : Sym := 387
def zS : Sym := 388
def sExp : Sym := 389

theorem names : c.sortName nS = "N" ∧ c.sortName expS = "Exp" ∧ c.symName eS = "Lble" ∧
    c.symName sN = "LblsN" ∧ c.symName zS = "Lblz" ∧ c.symName sExp = "LblsExp" := by decide +kernel

noncomputable abbrev fn : Fn := c.fns[0]'(by decide +kernel)

theorem hfn : c.lookupFn sExp = some fn := rfl
theorem hfnH (H : HookParams) : (cH H).lookupFn sExp = some fn := by rw [Semantics.lookupFn_withHooks]; rfl
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def vz : GroundTerm := .ctor zS []
/-- `inj{N,Exp}(z)` -/
def iz : GroundTerm := .inj nS expS vz
/-- `inj{N,Exp}(sN(z))` -/
def isz : GroundTerm := .inj nS expS (.ctor sN [vz])
def ve : GroundTerm := .ctor eS []

theorem sorts_iz : c.sortsOf [iz] = some fn.args := by decide +kernel
theorem sorts_e : c.sortsOf [ve] = some fn.args := by decide +kernel
theorem sorts_izH (H : HookParams) : (cH H).sortsOf [iz] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact sorts_iz
theorem sorts_eH (H : HookParams) : (cH H).sortsOf [ve] = some fn.args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact sorts_e

theorem eval_inj_z (H : HookParams) : Eval (cH H) sExp [iz] (some isz) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_iz (n := 10) (by decide +kernel)

theorem eval_e (H : HookParams) : Eval (cH H) sExp [ve] (some ve) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn sorts_e (n := 10) (by decide +kernel)

/-- **`sExp(inj z) = inj(sN(z))`, derived from `Pre`**, for every H: through Γ's item of the
overload clause. -/
theorem sExp_inj_z (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) sExp [iz] ≡ den (cH H) isz) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_inj_z H) (hfnH H) (sorts_izH H)

/-- **`sExp(e) = e`, derived from `Pre`**, for every H: from the equation 271 as written. -/
theorem sExp_e (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) sExp [ve] ≡ den (cH H) ve) :=
  TiePair.value (shapeH H) (coreOKH H) (hokH H) (eval_e H) (hfnH H) (sorts_eH H)

end Ct

end KCore.OvlFnFnValues

#check @KCore.OvlFnFnValues.Fn.shape
#check @KCore.OvlFnFnValues.Fn.fnText_at0
#check @KCore.OvlFnFnValues.Fn.premises_at
#check @KCore.OvlFnFnValues.Fn.negExp_inj3
#check @KCore.OvlFnFnValues.Fn.negExp_e
#check @KCore.OvlFnFnValues.Ct.shape
#check @KCore.OvlFnFnValues.Ct.fnText_at0
#check @KCore.OvlFnFnValues.Ct.premises_at
#check @KCore.OvlFnFnValues.Ct.sExp_inj_z
#check @KCore.OvlFnFnValues.Ct.sExp_e
#print axioms KCore.OvlFnFnValues.Fn.premises_at
#print axioms KCore.OvlFnFnValues.Fn.negExp_inj3
#print axioms KCore.OvlFnFnValues.Fn.negExp_e
#print axioms KCore.OvlFnFnValues.Ct.premises_at
#print axioms KCore.OvlFnFnValues.Ct.sExp_inj_z
#print axioms KCore.OvlFnFnValues.Ct.sExp_e
