/-
  The collection laws of `_List_` in the kompiled text of construct fixture base
  (`f2-examples/base.kompile.kore`, `test/constructs/fixtures/base`), each entailed by
  `Γ (c.withHooks H)` at values for every interpretation H, from the library's statement of the class
  (`InertEv.listLaw_ev`). Run from the package root: `lake env lean -j1 test/InertBaseLaws.lean`.
  Every statement is on the literal `defn`; nothing reads `Parse.parse` or `emit`.

  - `laws_text`: axioms 38, 39, 40 of the user module BASE (`//@ 128` to `//@ 130` of the fixture's
    kore.txt) are the associativity, the right unit and the left unit of `_List_`, over the one sort
    variable `R`; `laws_class`: the reader leaves each inert, class `collectionLaw`.
  - `law38`, `law39`, `law40`, `list_laws_base`: each is entailed at values, for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.InertBaseLaws

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/base.kompile.kore"
definition_of defn from "f2-examples/base.kompile.kore"
user_axioms U from "f2-examples/base.kompile.kore" module "BASE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem shapesOKH (H : HookParams) : (cH H).shapesOK = true := (by decide +kernel : c.shapesOK = true)

/-- The three sentences are the laws of `_List_`, over the sort variable `R`. -/
theorem laws_text :
    U.ax38.ax.pattern = InertEv.listAssoc.patR ∧ U.ax39.ax.pattern = InertEv.listUnitRight.patR ∧
    U.ax40.ax.pattern = InertEv.listUnitLeft.patR ∧
    [U.ax38, U.ax39, U.ax40].all (fun ad => ad.ax.sortVars == [Rv]) = true := by
  decide +kernel

/-- The reader's class of the three sentences. -/
theorem laws_class : [U.ax38, U.ax39, U.ax40].map (fun ad => Parse.classifyShape (.axiom ad.ax)) =
    [.inert .collectionLaw, .inert .collectionLaw, .inert .collectionLaw] := by decide +kernel

theorem law38 (H : HookParams) : EntailsAtValues (cH H) U.ax38 (trS U.ax38).pat := by
  rw [(by decide +kernel : (trS U.ax38).pat = (trAxiom [] [] U.ax38).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inl rfl) U.ax38 laws_text.1 (by decide +kernel)

theorem law39 (H : HookParams) : EntailsAtValues (cH H) U.ax39 (trS U.ax39).pat := by
  rw [(by decide +kernel : (trS U.ax39).pat = (trAxiom [] [] U.ax39).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inr (Or.inl rfl)) U.ax39 laws_text.2.1
    (by decide +kernel)

theorem law40 (H : HookParams) : EntailsAtValues (cH H) U.ax40 (trS U.ax40).pat := by
  rw [(by decide +kernel : (trS U.ax40).pat = (trAxiom [] [] U.ax40).pat)]
  exact InertEv.listLaw_ev (coreOKH H) (shapesOKH H) (Or.inr (Or.inr rfl)) U.ax40 laws_text.2.2.1
    (by decide +kernel)

/-- **The three laws of `_List_` in base are entailed at values**, for every H. -/
theorem list_laws_base (H : HookParams) :
    ∀ ad ∈ [U.ax38, U.ax39, U.ax40], EntailsAtValues (cH H) ad (trS ad).pat := by
  intro ad had
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl
  · exact law38 H
  · exact law39 H
  · exact law40 H

end KCore.InertBaseLaws

#check @KCore.InertBaseLaws.list_laws_base
#print axioms KCore.InertBaseLaws.laws_text
#print axioms KCore.InertBaseLaws.laws_class
#print axioms KCore.InertBaseLaws.list_laws_base
