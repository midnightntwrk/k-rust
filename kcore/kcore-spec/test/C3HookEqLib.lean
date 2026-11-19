/-
  C3 `hook x equation`, the case of a library symbol: a user's equation of `_+Int_` (hook INT.add),
  on fixture c3-hook-eq-lib, `rule X +Int 0 => X` in a module importing INT, without
  `simplification`.
  The text is `f2-examples/c3-hook-eq-lib.kompile.kore`: the kompiled text that
  `test/constructs/fixtures/c3-hook-eq-lib/kompile.txt` records, with its paths restored.
  Run from the package root: `lake env lean -j1 test/C3HookEqLib.lean`. Every statement is on the
  literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`.

  kompile writes the rule as an equation in the function form, `\implies{R}(\and{R}(\top{R}(),
  \and{R}(X0 ∈ VarX, \and{R}(X1 ∈ 0, \top{R}()))), \equals{SortInt{}, R}(_+Int_(X0, X1),
  \and{SortInt{}}(VarX, \top{SortInt{}}())))` (axiom `lemAx`). It states the value of `_+Int_`, a
  symbol whose value the registry gives, at every element of Int: the reader leaves it out of Γ
  (`Parse.regLemmaEqn`), and the account lists it owed at values (`user lemma at values`).

  - `lem_text`: the sentence is `fnPlusZero`'s pattern, over the one sort variable `R`.
  - `lem_regLemma`: the reader takes the sentence for a user's equation of a symbol whose value the
    registry gives (`Parse.regLemmaEqn` at the module's scan).
  - `lem_ev`: **the sentence holds at values, for every H** (`EntailsAtValues`, the direction of
    the class `user lemma at values`): at an integer x, `_+Int_` at x and 0 is x + 0 = x
    (`LibEv.FnEqn.entailed_reg`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.C3HookEqLib

open KCore ML Faithful KoreAML LibEv

kore_term kore from "f2-examples/c3-hook-eq-lib.kompile.kore"
definition_of defn from "f2-examples/c3-hook-eq-lib.kompile.kore"
user_axioms U from "f2-examples/c3-hook-eq-lib.kompile.kore" module "C3-HOOK-EQ-LIB"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOK_c : c.shapesOK = true := by decide_cheap
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := shapesOK_c

/-- The user's equation. -/
noncomputable abbrev lemAx : AxiomDecl := U.ax154

/-- `X +Int 0 => X` in the function form: `_+Int_` at the argument variables `X0`, `X1`, matched
by the patterns `VarX` and `0`, has the value of `VarX`. -/
def fnPlusZero : FnEqn :=
  ⟨[("VarX", Srt.int)], intAdd, [(Srt.int, .var 0, none), (Srt.int, intT 0, none)], Srt.int, none, .var 0⟩

theorem fnPlusZero_holds {c : Semantics} (hs : c.shapesOK = true) : fnPlusZero.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarX") rfl
  obtain ⟨h1, -, h2, -, -⟩ := hm
  rw [fq_val_var] at h1
  have h1' : σ.lookup 1 = some (int x) := h1.symm.trans hx
  have h2' : σ.lookup 2 = some (int 0) := by
    have h := h2.symm
    simp only [fnPlusZero, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, val, intT, dv_int] at h
    exact h
  fq_eval [fnPlusZero, h1', h2', hx, hv_intAdd, Int.add_zero]

/-- **The sentence is `fnPlusZero`'s pattern**, over the one sort variable `R`, and translated
without the text's declarations. -/
theorem lem_text : lemAx.ax.pattern = fnPlusZero.patR ∧ lemAx.ax.sortVars = [Rv] ∧
    fnPlusZero.regular = true ∧ fnPlusZero.typed c = true ∧
    (trAxiom kore.symbolDecls kore.aliasNames lemAx).pat = (trAxiom [] [] lemAx).pat := by
  decide +kernel

kernel_rfl typed_wh : ∀ H : HookParams, fnPlusZero.typed (cH H) = fnPlusZero.typed c

/-- The reader takes the sentence for a user's equation of a symbol whose value the registry gives:
it leaves it out of Γ, owed. -/
theorem lem_regLemma : (Parse.rawEqn? lemAx.ax).any
    (Parse.regLemmaEqn (Parse.scan ((kore.modules.getLast?.map (·.sentences)).getD []))) = true := by
  decide +kernel

/-- **`X +Int 0 = X` holds at values, for every H**: in every model of Γ, at every valuation that
sends `X`, `X0`, `X1` to values. -/
theorem lem_ev (H : HookParams) : EntailsAtValues (cH H) lemAx (trAxiom [] [] lemAx).pat :=
  FnEqn.entailed_reg (coreOKH H) fnPlusZero lem_text.2.2.1 ((typed_wh H).trans lem_text.2.2.2.1)
    (fnPlusZero_holds (shapesOKH H)) lemAx lem_text.1 lem_text.2.1

end KCore.C3HookEqLib

#print axioms KCore.C3HookEqLib.lem_text
#print axioms KCore.C3HookEqLib.lem_regLemma
#print axioms KCore.C3HookEqLib.lem_ev
