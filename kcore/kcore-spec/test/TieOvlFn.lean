/-
  The constructor sentences of a function-overloaded symbol against Γ's items at uncovered
  arguments (KcoreSpec/TieOvlFn.lean), kernel-checked on two texts. Run from the package root:
  `lake env lean -j1 test/TieOvlFn.lean`.

  - `Lhs`: `f2-examples/e5-ovl-fun-lhs.kompile.kore`. `capGas : Gas → Gas` overloads the function
    `capN : N → N`, N < Gas; Gas has the constructor `inf` beside it. The text states `capGas`'s
    `functional` sentence (axiom 81), its same-constructor sentence (82), the different-constructors
    sentence of `capGas` and `inf` (83), `inf`'s `functional` sentence (89) and the overload axiom
    (139, with the injection on its right side).
  - `Keep`: `f2-examples/e5-ovl-fun-keep-run.kompile.kore`. The same symbols with `capN : N → Gas`:
    the overload axiom (110) has no injection on its right side.

  On each: the three predicates accept their sentence and no other sentence of the user module
  (`*_checked`, `*_only`); `tieOvlEqB` accepts the overload axiom (`ovleq_checked`); and the
  weaker lemmas at the literal generators, for every interpretation and every interpretation of
  the hooks' parameters (`fun_weaker`, `inj_weaker`, `dist_weaker`, the last from `capGas`'s
  `functional` sentence and from `inf`'s).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieOvlFnTest

open KCore ML Faithful KoreAML

/-- Gas. -/
def gasS : Srt := 32
/-- `capGas : Gas → Gas`, the overloading symbol. -/
def capGas : Gen := .ctor ⟨392, [32], 32⟩
/-- `inf : Gas`. -/
def inf : Gen := .ctor ⟨388, [], 32⟩

namespace Lhs

definition_of defn from "f2-examples/e5-ovl-fun-lhs.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-lhs.kompile.kore" module "E5-OVL-FUN-LHS"

noncomputable abbrev c : Semantics := defn.sem

theorem names : c.sortName gasS = "Gas" ∧ c.fnOvl capGas = true ∧ c.fnOvl inf = false ∧
    (Gen.toK c capGas, Gen.toK c inf) =
      (.ctor ⟨"LblcapGas", ["Gas"], "Gas"⟩, .ctor ⟨"Lblinf", [], "Gas"⟩) := by decide +kernel

theorem fun_checked : tieOvlFnFunAtB c gasS capGas U.ax81.ax = true := by decide +kernel
theorem inj_checked : tieOvlFnInjAtB c gasS capGas U.ax82.ax = true := by decide +kernel
theorem dist_checked : tieOvlFnDistAtB c gasS capGas inf U.ax83.ax = true := by decide +kernel
theorem capGas_fun_checked : tieOvlFnFunShapeB c gasS (Gen.toK c capGas) U.ax81.ax = true := by decide +kernel
theorem inf_fun_checked : tieOvlFnFunShapeB c gasS (Gen.toK c inf) U.ax89.ax = true := by decide +kernel

theorem fun_only : (U.all.filter fun ad => tieOvlFnFunB c ad.ax).map (·.index) = [81] := by decide +kernel
theorem inj_only : (U.all.filter fun ad => tieOvlFnInjB c ad.ax).map (·.index) = [82] := by decide +kernel
theorem dist_only : (U.all.filter fun ad => tieOvlFnDistB c ad.ax).map (·.index) = [83] := by decide +kernel

/-- None of the three is a sentence Γ's constructor items entail in the form `tieConsB` reads. -/
theorem not_cons : [U.ax81, U.ax82, U.ax83].all (fun ad => !tieConsB c ad.ax) = true := by decide +kernel

/-- The overload axiom, with the injection on its right side. -/
theorem ovleq_checked : tieOvlEqB c U.ax139.ax = true := by decide +kernel

section
variable {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M)

/-- `capGas`'s `functional` sentence gives Cons-Fun at uncovered arguments. -/
theorem fun_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hs : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (covs : List (List String)) :
    I ⊧ᴵ (Cons.funUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat :=
  tieOvlFnFun_weaker fun_checked hB hA hs covs

/-- `capGas`'s same-constructor sentence, with its `functional` sentence, gives Cons-Inj at
uncovered arguments. -/
theorem inj_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax82).pat) (covs : List (List String)) :
    I ⊧ᴵ (Cons.injUncItem (c.sortName gasS) (Gen.toK c capGas) covs).pat :=
  tieOvlFnInj_weaker fun_checked inj_checked hB hA hsf hs covs

/-- The different-constructors sentence of `capGas` and `inf`, with `capGas`'s `functional`
sentence, gives Cons-Dist at uncovered arguments. -/
theorem dist_weaker (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c capGas))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax81).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax83).pat)
    (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf) ug ug').pat) ∧
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c inf) (Gen.toK c capGas) ug' ug).pat) :=
  tieOvlFnDist_weaker (.inl rfl) capGas_fun_checked dist_checked hB hA hsf hs ug ug'

/-- The same from `inf`'s `functional` sentence in place of `capGas`'s. -/
theorem dist_weaker_inf (hB : TieOvlFnBase I (c.sortName gasS)) (hA : TieOvlFnArity I (c.sortName gasS) (Gen.toK c inf))
    (hsf : I ⊧ᴵ (trAxiom [] [] U.ax89).pat) (hs : I ⊧ᴵ (trAxiom [] [] U.ax83).pat)
    (ug ug' : Option (List (List String))) :
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c capGas) (Gen.toK c inf) ug ug').pat) ∧
    (I ⊧ᴵ (Cons.distUncItem (c.sortName gasS) (Gen.toK c inf) (Gen.toK c capGas) ug' ug).pat) :=
  tieOvlFnDist_weaker (.inr rfl) inf_fun_checked dist_checked hB hA hsf hs ug ug'

end

/-- Γ holds the three items at every interpretation of the hooks' parameters. -/
theorem items (H : HookParams) :
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.funUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) ((ovlArgsOf (c.withHooks H) capGas).getD [])).pat) ∧
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.injUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) ((ovlArgsOf (c.withHooks H) capGas).getD [])).pat) ∧
    ((∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.distUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) capGas) (Gen.toK (c.withHooks H) inf) (ovlArgsOf (c.withHooks H) capGas)
      (ovlArgsOf (c.withHooks H) inf)).pat) ∨
    (∃ it ∈ consItemsK (c.withHooks H), it.pat = (Cons.distUncItem ((c.withHooks H).sortName gasS)
      (Gen.toK (c.withHooks H) inf) (Gen.toK (c.withHooks H) capGas) (ovlArgsOf (c.withHooks H) inf)
      (ovlArgsOf (c.withHooks H) capGas)).pat)) :=
  ⟨tieOvlFnFun_item_withHooks fun_checked H, tieOvlFnInj_item_withHooks inj_checked H,
    tieOvlFnDist_item_withHooks dist_checked H⟩

/-- The overloads the items name: `capGas` is covered at the lifts of N. -/
theorem covs : ovlArgsOf c capGas = some [["N"]] ∧ ovlArgsOf c inf = none := by decide +kernel

end Lhs

namespace Keep

definition_of defn from "f2-examples/e5-ovl-fun-keep-run.kompile.kore"
user_axioms U from "f2-examples/e5-ovl-fun-keep-run.kompile.kore" module "E5-OVL-FUN-KEEP-RUN"

noncomputable abbrev c : Semantics := defn.sem

theorem names : c.sortName gasS = "Gas" ∧ c.fnOvl capGas = true ∧ c.fnOvl inf = false ∧
    (Gen.toK c capGas, Gen.toK c inf) =
      (.ctor ⟨"LblcapGas", ["Gas"], "Gas"⟩, .ctor ⟨"Lblinf", [], "Gas"⟩) := by decide +kernel

theorem fun_checked : tieOvlFnFunAtB c gasS capGas U.ax58.ax = true := by decide +kernel
theorem inj_checked : tieOvlFnInjAtB c gasS capGas U.ax59.ax = true := by decide +kernel
theorem dist_checked : tieOvlFnDistAtB c gasS capGas inf U.ax60.ax = true := by decide +kernel

theorem fun_only : (U.all.filter fun ad => tieOvlFnFunB c ad.ax).map (·.index) = [58] := by decide +kernel
theorem inj_only : (U.all.filter fun ad => tieOvlFnInjB c ad.ax).map (·.index) = [59] := by decide +kernel
theorem dist_only : (U.all.filter fun ad => tieOvlFnDistB c ad.ax).map (·.index) = [60] := by decide +kernel

/-- The overload axiom in the result-keeping form: no injection on its right side. -/
theorem ovleq_checked : tieOvlEqB c U.ax110.ax = true := by decide +kernel

/-- The predicates at every interpretation of the hooks' parameters. -/
theorem checked_withHooks (H : HookParams) : tieOvlFnFunB (c.withHooks H) U.ax58.ax = true ∧
    tieOvlFnInjB (c.withHooks H) U.ax59.ax = true ∧ tieOvlFnDistB (c.withHooks H) U.ax60.ax = true :=
  ⟨(tieOvlFnFunB_withHooks c H _).trans (by decide +kernel), (tieOvlFnInjB_withHooks c H _).trans (by decide +kernel),
    (tieOvlFnDistB_withHooks c H _).trans (by decide +kernel)⟩

end Keep

end KCore.TieOvlFnTest

#print axioms KCore.Faithful.tieOvlFnFun_at
#print axioms KCore.Faithful.tieOvlFnInj_at
#print axioms KCore.Faithful.tieOvlFnDist_at
#print axioms KCore.Faithful.tieOvlFnFun_weaker
#print axioms KCore.Faithful.tieOvlFnInj_weaker
#print axioms KCore.Faithful.tieOvlFnDist_weaker
#print axioms KCore.Faithful.tieOvlFnBase_of_Γ
#print axioms KCore.Faithful.tieOvlFnFunB_withHooks
#print axioms KCore.Faithful.tieOvlFnInjB_withHooks
#print axioms KCore.Faithful.tieOvlFnDistB_withHooks
#print axioms KCore.Faithful.tieOvlFnFun_item_withHooks
#print axioms KCore.Faithful.tieOvlFnInj_item_withHooks
#print axioms KCore.Faithful.tieOvlFnDist_item_withHooks
#print axioms KCore.TieOvlFnTest.Lhs.fun_checked
#print axioms KCore.TieOvlFnTest.Lhs.fun_only
#print axioms KCore.TieOvlFnTest.Lhs.inj_only
#print axioms KCore.TieOvlFnTest.Lhs.dist_only
#print axioms KCore.TieOvlFnTest.Lhs.not_cons
#print axioms KCore.TieOvlFnTest.Lhs.ovleq_checked
#print axioms KCore.TieOvlFnTest.Lhs.fun_weaker
#print axioms KCore.TieOvlFnTest.Lhs.inj_weaker
#print axioms KCore.TieOvlFnTest.Lhs.dist_weaker
#print axioms KCore.TieOvlFnTest.Lhs.dist_weaker_inf
#print axioms KCore.TieOvlFnTest.Lhs.items
#print axioms KCore.TieOvlFnTest.Lhs.covs
#print axioms KCore.TieOvlFnTest.Keep.fun_only
#print axioms KCore.TieOvlFnTest.Keep.inj_only
#print axioms KCore.TieOvlFnTest.Keep.dist_only
#print axioms KCore.TieOvlFnTest.Keep.ovleq_checked
#print axioms KCore.TieOvlFnTest.Keep.checked_withHooks
