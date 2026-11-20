/-
  Evidence for the row `hook:KEQUAL.ite:Lblite` of test/constructs/rows.toml and two of its cases,
  on K 7.1.337 kompile's own texts (`f2-examples/NAME.kompile.kore`, each the text its fixture's
  kompile.txt hashes), for every interpretation H. Run from the package root:
  `lake env lean -j1 test/IteHookForms.lean`.

  `ite` (domains.md:2314-2316, equations 2357 and 2358) is the second argument where the first is
  `true` and the third where it is `false`, at every sort. A semantics has it at a sort S as a
  parameter `f : Bool × S × S → S` implemented by the registry's `kIte`. `iteParam_eval`: for every
  semantics with such a parameter and every H, its application to terms with values b, x, y has the
  value x or y (`EvalTerm.param`, `paramVal_ite`), when that value has sort S. The hook decides
  every point, so no H is excepted.

  - `rdr-ite-own-hook` (`syntax {S} S ::= pick(Bool, S, S) [function, symbol(ite),
    hook(KEQUAL.ite)]`, K-EQUAL not imported, `rule f(X) => pick(false, X, b)`): the declaration is
    the registry's `ite` declared again, and its instance `Lblite{Foo}` is the parameter implemented
    by `kIte`. `OwnHook.ite_value`: its application at every condition and values of Foo;
    `OwnHook.f_rhs_value`: the right side of f's clause, the reading of f's equation (axiom 137),
    at every value of X is `b`; `OwnHook.f_value`: f at `a` is `b`, through that clause. Of the
    fixtures' K 7.1.337 kompiled texts, the one other that applies `ite` at a sort in a sentence of
    its own, e2-open-linked-bool (K-EQUAL imported, `#if B #then 1 #else 0 #fi` at Int in a rule),
    is refused `openRequires`, so the reader gives it no parameter implemented by `kIte`: this text
    is where the reading gives K's `ite` a value at a sort.
  - `rdr-ite-two-eq` (`syntax {S1, S2} S2 ::= cast(S1) [function, symbol(ite)]`, `rule cast(a) =>
    b`, `rule f(X) => cast(X)`): the instance `Lblite{Foo,Foo}` is a function of the reading with
    the text's equation, not K's `ite`. The reading's values: `TwoEq.ite_value` (`Lblite{Foo,Foo}`
    at `a` is `b`) and `TwoEq.f_value` (f at `a` is `b`), for every H. Γ writes the instance as the
    text does, the head `Lblite` at the sorts `SortFoo`, `SortFoo`: `TwoEq.fn_text` (the clauses of
    f and of the instance find the text's sentences 137, whose right side applies the instance,
    and 171, the instance's own equation, by head and sort arguments), `TwoEq.tied` (Γ's equation
    items of the two are the translations of those sentences up to one variable's name,
    `TiePair.sameB`, nothing rewritten) and `TwoEq.fn_shape` (so is every equation item of Γ's
    functions against the sentence its clause finds, in order).
  The symbol numbers are the reader's for each text, found by name.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.IteHookForms

open KCore ML Faithful KoreAML

/-- The symbol named `n`, by number. -/
def symIH (c : Semantics) (n : String) : Sym :=
  ((List.range (nRegSyms + c.symNames.length)).find? fun f => c.symName f == n).getD 0

/-- **`ite` at a sort has its value at values, in every semantics and under every interpretation**:
the application of a parameter implemented by `kIte` to terms with the values `b`, `x`, `y` is `x`
where `b` is `true` and `y` where it is `false`, when that value has the parameter's result sort. -/
theorem iteParam_eval {c : Semantics} (H : HookParams) {f : Sym} {k : ParamSig}
    (hp : c.lookupParam f = some k) (hk : k.impl = some kIte) (hct : c.isCtor f = false)
    (hhk : isHook f = false) {σ : Subst} {t₀ t₁ t₂ : Term} (b : Bool) {x y : GroundTerm}
    (h₀ : EvalTerm (c.withHooks H) σ t₀ (some (bool b))) (h₁ : EvalTerm (c.withHooks H) σ t₁ (some x))
    (h₂ : EvalTerm (c.withHooks H) σ t₂ (some y))
    (hz : (c.withHooks H).sortOf (if b then x else y) = some k.sig.result) :
    EvalTerm (c.withHooks H) σ (.app f [t₀, t₁, t₂]) (some (if b then x else y)) := by
  have hpH : (c.withHooks H).lookupParam f = some k := hp
  have hpar : (c.withHooks H).isParam f = true := by simp [Semantics.isParam, hpH]
  refine EvalTerm.param hct hhk hpar (.cons h₀ (.cons h₁ (.cons h₂ .nil))) ?_
  rw [show allSome [some (bool b), some x, some y] = some [bool b, x, y] from rfl, Option.bind_some,
    paramVal_ite hpH hk b hz]

/-! ## rdr-ite-own-hook: the registry's `ite` declared again, at Foo -/

namespace OwnHook

definition_of defn from "f2-examples/rdr-ite-own-hook.kompile.kore"
user_axioms U from "f2-examples/rdr-ite-own-hook.kompile.kore" module "RDR-ITE-OWN-HOOK"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

theorem coreOK : c.coreOK = true := by decide_cheap

/-- The parameter implemented by `kIte`: the instance `Lblite{Foo}`. -/
noncomputable def kp : ParamSig := (c.params.filter (·.impl == some kIte)).headD default

theorem kp_named : c.symName kp.sig.name = "Lblite{Foo}" := by decide +kernel
theorem kp_lookup : c.lookupParam kp.sig.name = some kp := by decide +kernel
theorem kp_impl : kp.impl = some kIte := by decide +kernel
theorem kp_notCtor : c.isCtor kp.sig.name = false := by decide +kernel
theorem kp_notHook : isHook kp.sig.name = false := by decide +kernel

noncomputable def fooS : Srt := kp.sig.result
noncomputable def aS : Sym := symIH c "Lbla"
noncomputable def bS : Sym := symIH c "Lblb"
noncomputable def fS : Sym := symIH c "Lblf"
noncomputable def aV : GroundTerm := .ctor aS []
noncomputable def bV : GroundTerm := .ctor bS []

theorem syms_named : c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧ c.symName fS = "Lblf" := by
  decide +kernel

theorem kp_sig : kp.sig.args = [Srt.bool, fooS, fooS] := by decide +kernel

/-- **`Lblite{Foo}(b, x, y)` is `x` or `y`**, for every H, every condition `b` and values `x`, `y`
of Foo (domains.md:2314-2316; 2357 at `true`, 2358 at `false`). -/
theorem ite_value (H : HookParams) (b : Bool) (x y : GroundTerm) (hx : c.sortOf x = some fooS)
    (hy : c.sortOf y = some fooS) :
    EvalTerm (cH H) [(0, x), (1, y)] (.app kp.sig.name [.dv Srt.bool (.bool b), .var 0, .var 1])
      (some (if b then x else y)) :=
  iteParam_eval H kp_lookup kp_impl kp_notCtor kp_notHook b .dv .var .var
    (by rw [Cert.sortOf_withHooks_hrC c H noRaw]; cases b <;> assumption)

/-- f's one function. -/
theorem fn_some : (c.lookupFn fS).isSome = true := by decide +kernel
noncomputable def fnF : Fn := (c.lookupFn fS).get fn_some
theorem hfn : c.lookupFn fS = some fnF := (Option.some_get fn_some).symm

/-- f's equation is axiom 137 of the text, `f(X) = Lblite{Foo}(false, X, b)`: the first sentence
of Γ's function equations (f is the first function), found by head symbol. -/
theorem f_axiom : (TiePair.fnTextOf c U.all).head?.map (·.index) = some 137 ∧
    (c.allFns.head?.map (·.label)) = some fS := by decide +kernel

/-- The right side of f's clause as `kcore sem-fields` prints it (`rhs=Lblite{Foo}(dv[Bool](KCore.Lit.bool
false), V0, Lblb())`): `Lblite{Foo}(false, V0, b)`. `f_value` evaluates the clause itself. -/
noncomputable def fRhs : Term := .app kp.sig.name [.dv Srt.bool (.bool false), .var 0, .app bS []]

/-- **The right side of f's equation is `b` at every value of X**, for every H: the hook at the
condition `false` is its third argument. -/
theorem f_rhs_value (H : HookParams) (x : GroundTerm) :
    EvalTerm (cH H) [(0, x)] fRhs (some bV) := by
  unfold fRhs
  have hb : EvalTerm (cH H) [(0, x)] (.app bS []) (some bV) :=
    EvalTerm.ctor (rs := []) (show c.isCtor bS = true by decide +kernel) .nil
  have h := iteParam_eval H kp_lookup kp_impl kp_notCtor kp_notHook (σ := [(0, x)]) false
    (x := x) (y := bV) .dv (show EvalTerm (cH H) [(0, x)] (.var 0) (some x) from .var) hb
    (by rw [Cert.sortOf_withHooks_hrC c H noRaw]; show c.sortOf bV = some kp.sig.result; decide +kernel)
  simpa using h

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

/-- **f at `a` is `b`**, for every H. -/
theorem f_value (H : HookParams) : Eval (cH H) fS [aV] (some bV) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfn (by decide +kernel) (n := 50) (by decide +kernel)

end OwnHook

/-! ## rdr-ite-two-eq: `Lblite{Foo,Foo}`, a function of the reading with the text's equation -/

namespace TwoEq

kore_term kore from "f2-examples/rdr-ite-two-eq.kompile.kore"
definition_of defn from "f2-examples/rdr-ite-two-eq.kompile.kore"
user_axioms U from "f2-examples/rdr-ite-two-eq.kompile.kore" module "RDR-ITE-TWO-EQ"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- The clauses of f and of `Lblite{Foo,Foo}` are keyed by their functions' names, and the keys find
the text's sentences 137 (`f(X) = Lblite{SortFoo,SortFoo}(X)`) and 171
(`Lblite{SortFoo,SortFoo}(a) = b`): the instance's key finds the equation whose left side is the
head `Lblite` at the instance's two sorts. -/
theorem fn_text : (TiePair.clauseKeys c).take 2 = [("Lblf", 50), ("Lblite{Foo,Foo}", 50)] ∧
    ((TiePair.fnTextOf c U.all).take 2).map (·.index) = [137, 171] := by decide +kernel

/-- **Γ's equation items of f and of `Lblite{Foo,Foo}` (the first two, in `fnItems`'s order) are the
translations of the text's sentences 137 and 171**, up to one variable's name (`TiePair.sameB`;
kernel), with nothing rewritten: Γ applies the head `Lblite` at the sorts `SortFoo`, `SortFoo`, on
the right side of f's equation and at the left side of the instance's own, as the sentences do. -/
theorem tied : (((TiePair.gammaPats c).take 2).zip [(trS U.ax137).pat, (trS U.ax171).pat]).all
    (fun p => TiePair.sameB p.1 p.2) = true := by decide +kernel

/-- **Every equation item of Γ's functions is the translation of the sentence its clause finds**
(`TiePair.fnTextOf`, by head symbol at its sort arguments and priority), in `fnItems`'s order, up
to one variable's name (`TiePair.shapeB`; kernel). -/
theorem fn_shape : TiePair.shapeB (TiePair.gammaPats c)
    ((TiePair.fnTextOf c U.all).map fun ad => (trS ad).pat) = true := by decide +kernel

/-- f and `Lblite{Foo,Foo}` are the first two functions, one clause each. -/
theorem fns_first : (c.allFns.take 2).map (fun fn => (c.symName fn.label, fn.clauses.length)) =
    [("Lblf", 1), ("Lblite{Foo,Foo}", 1)] := by decide +kernel

noncomputable def aS : Sym := symIH c "Lbla"
noncomputable def bS : Sym := symIH c "Lblb"
noncomputable def fS : Sym := symIH c "Lblf"
noncomputable def iteS : Sym := symIH c "Lblite{Foo,Foo}"
noncomputable def aV : GroundTerm := .ctor aS []
noncomputable def bV : GroundTerm := .ctor bS []

theorem syms_named : c.symName aS = "Lbla" ∧ c.symName bS = "Lblb" ∧ c.symName fS = "Lblf" ∧
    c.symName iteS = "Lblite{Foo,Foo}" := by decide +kernel

theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel

theorem ite_some : (c.lookupFn iteS).isSome = true := by decide +kernel
noncomputable def fnIte : Fn := (c.lookupFn iteS).get ite_some
theorem hfnIte : c.lookupFn iteS = some fnIte := (Option.some_get ite_some).symm

theorem f_some : (c.lookupFn fS).isSome = true := by decide +kernel
noncomputable def fnF : Fn := (c.lookupFn fS).get f_some
theorem hfnF : c.lookupFn fS = some fnF := (Option.some_get f_some).symm

/-- `Lblite{Foo,Foo}` at `a` is `b` under every interpretation: the reading's clause of it. -/
theorem ite_value (H : HookParams) : Eval (cH H) iteS [aV] (some bV) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnIte (by decide +kernel) (n := 50) (by decide +kernel)

/-- f at `a` is `b` under every interpretation: the reading's clause of f, then `Lblite{Foo,Foo}`'s. -/
theorem f_value (H : HookParams) : Eval (cH H) fS [aV] (some bV) :=
  TiePair.eval_withHooks hok hsr hmr noRaw H hfnF (by decide +kernel) (n := 50) (by decide +kernel)

end TwoEq

end KCore.IteHookForms

#check @KCore.IteHookForms.iteParam_eval
#check @KCore.IteHookForms.OwnHook.ite_value
#check @KCore.IteHookForms.OwnHook.f_rhs_value
#check @KCore.IteHookForms.OwnHook.f_value
#check @KCore.IteHookForms.TwoEq.fn_text
#check @KCore.IteHookForms.TwoEq.tied
#check @KCore.IteHookForms.TwoEq.fn_shape
#check @KCore.IteHookForms.TwoEq.fns_first
#check @KCore.IteHookForms.TwoEq.ite_value
#check @KCore.IteHookForms.TwoEq.f_value
/-- info: 'KCore.IteHookForms.OwnHook.ite_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.OwnHook.ite_value
/-- info: 'KCore.IteHookForms.OwnHook.f_rhs_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.OwnHook.f_rhs_value
/-- info: 'KCore.IteHookForms.OwnHook.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.OwnHook.f_value
/-- info: 'KCore.IteHookForms.TwoEq.tied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.TwoEq.tied
/-- info: 'KCore.IteHookForms.TwoEq.fn_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.TwoEq.fn_shape
/-- info: 'KCore.IteHookForms.TwoEq.ite_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.TwoEq.ite_value
/-- info: 'KCore.IteHookForms.TwoEq.f_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.IteHookForms.TwoEq.f_value
