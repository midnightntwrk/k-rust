/-
  The function equations of the fixture e2-clause-rhs-empty tied to its sentences (C14), for every
  interpretation H: `rule f() => g(Y:Empty) [unboundVariables(Y)]` (`syntax Empty`, no production;
  `T ::= g(Empty)`, `T ::= f() [function]`). The text is `f2-examples/rhsempty.kompile.kore`, the
  kompiled text of `test/constructs/fixtures/e2-clause-rhs-empty` (equal to it after
  `kfix.stripped`); its sentence 207 is `f() = g(Y)`, Y free, so universal over Empty. Run from the
  package root: `lake env lean -j1 test/TieClauseRhsEmpty.lean`. Every statement is on the literal
  `defn`; nothing reads `Parse.parse` or `emit`.

  - Function equations (`fnText`: `f`'s sentence 207, then the sort predicates'): each of Γ's items
    is the translation of its sentence (`shape`), so Γ entails each (`fns_entailed`) and each item
    is a consequence of its sentence (`fns_from_text`).
  The text has no rule. The clause over Empty leaves Y open, so the definition reads a confined sort
  and its theory is `Γc = Γ ∪ Γcl`; the statements here are over Γ, and what Γ entails `Γc` entails.
  What the text determines of `f()` (nothing: C7 form (c)) is test/TieClauseRhsEmptyC.lean's.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsEmpty

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rhsempty.kompile.kore"
definition_of defn from "f2-examples/rhsempty.kompile.kore"
user_axioms U from "f2-examples/rhsempty.kompile.kore" module "E2-CLAUSE-RHS-EMPTY"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem readsConfined_c : c.readsConfined = true := by decide +kernel

/-! ## The function equations -/

/-- The text sentences of Γ's equations, in `fnItems`'s order: `f`'s (207, `f() => g(Y)`), then the
sort predicates' (`TiePair.fnTextOf`). -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

theorem fnText_index : fnText.map (·.index) = [207, 227, 235, 234, 233, 232, 239, 238, 241, 240, 237, 236,
    214, 213, 226, 225, 222, 221, 224, 223, 229, 228, 231, 230, 218, 217, 220, 219, 243, 242, 216, 215] := by
  decide +kernel

/-- `f() => g(Y)` (207) is the first. -/
theorem fnText_at0 : fnText[0]? = some U.ax207 := by kernel_rfl

/-- The translations of the text's sentences, in that order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence**, pattern for pattern or with
one variable renamed (`TiePair.sameB`; kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat :=
  fun ad had => TiePair.entailed (shapeH H) _ (List.mem_map_of_mem had)

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
  unfold textPats at ht
  rw [List.getElem?_map] at ht
  cases hf : fnText[j]? with
  | none => rw [hf] at ht; cases ht
  | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

end KCore.TieClauseRhsEmpty

#check @KCore.TieClauseRhsEmpty.fns_entailed
#print axioms KCore.TieClauseRhsEmpty.shape
#print axioms KCore.TieClauseRhsEmpty.fns_entailed
#print axioms KCore.TieClauseRhsEmpty.fns_from_text
