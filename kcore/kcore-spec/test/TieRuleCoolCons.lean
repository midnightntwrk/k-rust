/-
  The constructor sentences of `f2-examples/rulecool.kompile.kore` (fixture e2-rule): the
  `functional` sentences of the constructors, the `subsort` sentences and the no-confusion
  sentences of one and of two constructors, the classes of test/TieRuleCoolText.lean's account,
  entailed by Γ for every interpretation H (`cons_entailed`), and by `Γc` (`cons_entailed_c`).
  Run from the package root: `lake env lean -j1 test/TieRuleCoolCons.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieRuleCoolCons

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/rulecool.kompile.kore"
definition_of defn from "f2-examples/rulecool.kompile.kore"
user_axioms U from "f2-examples/rulecool.kompile.kore" module "E2-RULE"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- `Γc` holds every premise of Γ. -/
theorem Γ_sub_Γc (c : Semantics) {φ : P} (h : Γ c φ) : Γc c φ := Or.inl h

/-- What Γ entails, `Γc` entails. -/
theorem entails_c {c : Semantics} {ψ : P} (h : Γ c ⊧ ψ) : Γc c ⊧ ψ :=
  fun hI => h fun φ hφ => hI φ (Γ_sub_Γc c hφ)

/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/

/-- The sentences of the four classes (test/TieRuleCoolText.lean's `classes`: constructor functional,
subsort, injectivity, distinctness), in text order. -/
def consIdx : List Nat :=
  [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 26, 27, 28, 29, 30, 31, 32,
      80, 81, 82, 83, 85, 86, 87, 88, 89, 113, 114]

/-- The sentences, in text order. -/
noncomputable def consText : List AxiomDecl := U.all.filter fun ad => consIdx.contains ad.index

theorem consText_length : consText.length = 37 := by decide +kernel

/-- Each of the 37 is a constructor sentence Γ's constructor items entail (`tieConsB`): for a
constructor sort and generators of it, the sentence has the form of the generator's `functional`
or `subsort` sentence, or of a no-confusion sentence, and `consItemsK c` holds the items it follows
from (Cons-Fun; Cons-Fun and Cons-Inj; two Cons-Fun and Cons-Dist). -/
theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel

/-- None of the 37 reads a declaration or an alias: its translation with the text's declarations
is its translation with none. -/
theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by
  decide +kernel

/-- **E for the constructor sentences**: Γ entails each of the 37, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  exact tieCons_entailed (c := cH H) (a := ad.ax)
    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI

theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=
  fun ad had => entails_c (cons_entailed H ad had)
end KCore.TieRuleCoolCons

#print axioms KCore.TieRuleCoolCons.cons_checked
#print axioms KCore.TieRuleCoolCons.cons_entailed
#print axioms KCore.TieRuleCoolCons.cons_entailed_c
