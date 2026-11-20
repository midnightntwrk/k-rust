/-
  Values derived from the text's sentences (C7 form (a)) on the two construct fixtures whose text
  states an equation of an instance of its own sort-parametric function labelled `ite`:

  - `f2-examples/rdr-ite-two-eq.kompile.kore` (fixture rdr-ite-two-eq): `syntax {S1, S2} S2 ::=
    cast(S1) [function, symbol(ite)]`, `rule cast(a) => b`, `rule f(X) => cast(X)`. Sentence 137 is
    f's equation `f(X) = Lblite{SortFoo{}, SortFoo{}}(X)`, sentence 171 the instance's
    `Lblite{SortFoo{}, SortFoo{}}(a) = b`. `TwoEq.f_a_is_b`: f at `a` is `b`.
  - `f2-examples/rdr-ite-own-eq.kompile.kore` (fixture rdr-ite-own-eq): `syntax {S} S ::= pick(Bool,
    S, S) [function, symbol(ite)]`, `rule pick(true, X:Foo, _:Foo) => X`, `rule f(X) => pick(false,
    X, b)`. Sentence 137 is f's equation, sentence 171 the instance's `Lblite{SortFoo{}}(X0, X1, X2)
    = X1` under the premise `X0 = true`. `OwnEq.ite_true_a_b`: the instance at `(true, a, b)` is
    `a`. (f at `a` is the instance at `(false, a, b)`, of which the text states no equation.)

  Each value is derived from `Pre`: the function sentences of the text as written (`TiePair.fnTextOf`,
  the first two being 137 and 171, `fnText_index`), with the families of the reading (`TiePair.Pre`:
  ΓSig, ΓCons, ΓDomains, ΓColls, ΓFallback; the texts have no rule). Each of Γ's equations is its
  sentence's translation up to one variable's name (`shape`, `TiePair.shapeB`), Γ applying the head
  `Lblite` at the instance's sorts as the sentences do; the evaluator's result is `Eval`'s for every
  H (`TiePair.eval_withHooks`), and `TiePair.value` derives it from `Pre`. The ties of the two texts
  are test/TieRdrIteTwoEq.lean and test/TieRdrIteOwnEq.lean.

  Run from the package root: `lake env lean -j1 test/IteEqTieValues.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.IteEqTieValues

open KCore ML Faithful KoreAML

/-- The symbol named `n`, by number. -/
def symIV (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0

/-! ## rdr-ite-two-eq -/

namespace TwoEq

kore_term kore from "f2-examples/rdr-ite-two-eq.kompile.kore"
definition_of defn from "f2-examples/rdr-ite-two-eq.kompile.kore"
user_axioms U from "f2-examples/rdr-ite-two-eq.kompile.kore" module "RDR-ITE-TWO-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The first two are f's equation (137) and the instance's (171). -/
theorem fnText_index : (fnText.map (·.index)).take 2 = [137, 171] := by decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, up to one variable's name
(`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

noncomputable def aS : Sym := symIV c "Lbla"
noncomputable def bS : Sym := symIV c "Lblb"
noncomputable def fS : Sym := symIV c "Lblf"
noncomputable def aV : GroundTerm := .ctor aS []
noncomputable def bV : GroundTerm := .ctor bS []

theorem syms_named : c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧ c.symName fS = "Lblf" := by
  decide +kernel

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

theorem f_some : (c.lookupFn fS).isSome = true := by decide +kernel
noncomputable def fnF : Fn := (c.lookupFn fS).get f_some
theorem hfnF : c.lookupFn fS = some fnF := (Option.some_get f_some).symm

/-- f at `a` is `b` under every interpretation: f's clause, then the instance's. -/
theorem f_eval (H : HookParams) : Eval (cH H) fS [aV] (some bV) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnF (by decide +kernel) (n := 50) (by decide +kernel)

/-- The premises of the derivation: the function sentences as written, and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **f at `a` is `b`, derived from `Pre`, for every H**: f's sentence (137) gives `f(a) =
Lblite{SortFoo{}, SortFoo{}}(a)` and the instance's (171) gives `b`. -/
theorem f_a_is_b (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) fS [aV] ≡ den (cH H) bV) :=
  TiePair.value (shapeH H) (coreOKH H) ((Semantics.ok_withHooks c H).trans hok) (f_eval H)
    (by rw [Semantics.lookupFn_withHooks]; exact hfnF)
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)

end TwoEq

/-! ## rdr-ite-own-eq -/

namespace OwnEq

kore_term kore from "f2-examples/rdr-ite-own-eq.kompile.kore"
definition_of defn from "f2-examples/rdr-ite-own-eq.kompile.kore"
user_axioms U from "f2-examples/rdr-ite-own-eq.kompile.kore" module "RDR-ITE-OWN-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The first two are f's equation (137) and the instance's (171). -/
theorem fnText_index : (fnText.map (·.index)).take 2 = [137, 171] := by decide +kernel

noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, up to one variable's name
(`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

noncomputable def aS : Sym := symIV c "Lbla"
noncomputable def bS : Sym := symIV c "Lblb"
noncomputable def iteS : Sym := symIV c "Lblite{Foo}"
noncomputable def aV : GroundTerm := .ctor aS []
noncomputable def bV : GroundTerm := .ctor bS []
def tV : GroundTerm := .dv Srt.bool (.bool true)

theorem syms_named : c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧ c.symName iteS = "Lblite{Foo}" := by
  decide +kernel

/-- The decoder reads the instance's name as the head `Lblite` at the sort name `Foo`. -/
theorem ite_decoded : instDecode? (c.symName iteS) = some ("Lblite", ["Foo"]) := by decide +kernel

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

theorem ite_some : (c.lookupFn iteS).isSome = true := by decide +kernel
noncomputable def fnIte : Fn := (c.lookupFn iteS).get ite_some
theorem hfnIte : c.lookupFn iteS = some fnIte := (Option.some_get ite_some).symm

/-- The instance at `(true, a, b)` is `a` under every interpretation: its clause. -/
theorem ite_eval (H : HookParams) : Eval (cH H) iteS [tV, aV, bV] (some aV) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnIte (by decide +kernel) (n := 50) (by decide +kernel)

/-- The premises of the derivation: the function sentences as written, and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **The instance `Lblite{SortFoo{}}` at `(true, a, b)` is `a`, derived from `Pre`, for every H**:
the instance's sentence (171) at `X0 := true`, `X1 := a`, `X2 := b`. -/
theorem ite_true_a_b (H : HookParams) : Pre H ⊧ (TiePair.app (cH H) iteS [tV, aV, bV] ≡ den (cH H) aV) :=
  TiePair.value (shapeH H) (coreOKH H) ((Semantics.ok_withHooks c H).trans hok) (ite_eval H)
    (by rw [Semantics.lookupFn_withHooks]; exact hfnIte)
    (by rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel)

end OwnEq

end KCore.IteEqTieValues

/-- info: 'KCore.IteEqTieValues.TwoEq.f_a_is_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteEqTieValues.TwoEq.f_a_is_b

/-- info: 'KCore.IteEqTieValues.OwnEq.ite_true_a_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteEqTieValues.OwnEq.ite_true_a_b
