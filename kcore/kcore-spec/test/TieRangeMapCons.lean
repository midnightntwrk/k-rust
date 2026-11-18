/-
  The constructor sentences of the fixture e6-rangemap's text (`f2-examples/e6rm.kompile.kore`) and
  the account of the sentences tied by test/TieRangeMap.lean and here, for every interpretation H.
  Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean -j1 test/TieRangeMapCons.lean`.

  - Constructor sentences (`consText`: `functional` of a constructor, `subsort`, no confusion, the
    ones Γ's constructor items entail): entailed by Γ (`cons_entailed`, direction E).
  - `account`: the function equations (test/TieRangeMap.lean's `fnText`), the constructor
    sentences and the rule sentence (182) are sentences of the user module, each once and none in
    two classes, with the sizes of the classes and of the rest.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRangeMapCons

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6rm.kompile.kore"
definition_of defn from "f2-examples/e6rm.kompile.kore"
user_axioms U from "f2-examples/e6rm.kompile.kore" module "E6-RANGEMAP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- The indices of the text sentences of Γ's equations (test/TieRangeMap.lean's `fnText_index`):
`m`'s, then the sort predicates'. -/
def fnIdx : List Nat := [274, 253, 261, 260, 259, 258, 265, 264, 269, 268, 267, 266, 271, 270, 263, 262, 242, 241,
  252, 251, 248, 247, 250, 249, 255, 254, 257, 256, 244, 243, 246, 245]

/-- The index of the rule sentence (test/TieRangeMap.lean's `ruleText`). -/
def ruleIdx : List Nat := [182]

/-! ## The constructor sentences -/

/-- The indices of the user module's constructor sentences that Γ's constructor items entail
(`tieConsB`, `cons_tie`): `functional` of a constructor, `subsort`, no confusion. -/
def consIdx : List Nat := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25, 26, 27, 28, 29, 30, 31, 35,
  36, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 99, 100, 102, 103, 128, 129, 133, 134]
noncomputable def consText : List AxiomDecl := U.all.filter fun ad => consIdx.contains ad.index
theorem cons_tie : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

/-- None of them reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_tie ad had)) ad.index ad.module hI

/-! ## The account -/

def tiedIdx : List Nat := fnIdx ++ consIdx ++ ruleIdx

/-- **The account**: the function equations, the constructor sentences and the rule sentence are
sentences of the user module, each once and none in two classes; the sizes of the classes and of the
rest (the declarations' and interpreted symbols' sentences, test/TieRangeMapDecls.lean; library
sentences, collection laws, no junk, the projections and initializers: not tied here). -/
theorem account : tiedIdx.Nodup ∧ tiedIdx.all (fun i => (U.all.map (·.index)).contains i) = true ∧
    (U.all.map (·.index)).Nodup ∧
    (fnIdx.length, consIdx.length, ruleIdx.length, U.all.length - tiedIdx.length) = (32, 44, 1, 216) := by
  decide +kernel

end KCore.TieRangeMapCons

#check @KCore.TieRangeMapCons.cons_entailed
#print axioms KCore.TieRangeMapCons.cons_tie
#print axioms KCore.TieRangeMapCons.cons_entailed
#print axioms KCore.TieRangeMapCons.account
