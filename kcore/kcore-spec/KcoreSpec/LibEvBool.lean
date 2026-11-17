/-
  KCore, checked layer: equations of the builtin library's BOOL lemmas (the `simplification` rules
  of domains.md 1142 to 1168 in K 7.1.337), entailed at values in every semantics meeting `coreOK`
  whose Bool values are literals (`shapesOK`), for every interpretation: none of them reaches a
  silent point.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`. A rule written with `_` has the variable `_Gen0` in the text.
  - `bAndTrue` (1142): `B andBool true => B`.
  - `bAndFalse` (1144): `_ andBool false => false`.
  - `bAndThenTrue` (1147): `K andThenBool true => K`.
  - `bAndThenFalse` (1149): `_ andThenBool false => false`.
  - `bXorFalse` (1152): `B xorBool false => B`.
  - `bOrTrue` (1156): `_ orBool true => true`.
  - `bOrFalse` (1158): `B orBool false => B`.
  - `bOrElseTrue` (1161): `_ orElseBool true => true`.
  - `bOrElseFalse` (1163): `K orElseBool false => K`.
  - `bImpliesTrue` (1167): `_ impliesBool true => true`.
  - `bImpliesFalse` (1168): `B impliesBool false => notBool B`.
-/
import KcoreSpec.LibEv
import KcoreSpec.LazySound

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The Bool literal `b` as a term. -/
def boolT (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- A substitution of values of the variables' sorts gives a Bool variable a Bool literal. -/
theorem bool_at {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.bool)) : ∃ b : Bool, σ.lookup i = some (bool b) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨b, rfl⟩ := shape_bool hs hsv
  exact ⟨b, hv⟩

section
variable {c : Semantics}

theorem hvb_and (a b : Bool) : c.hv boolAnd [bool a, bool b] = some (bool (a && b)) := hv_of_value rfl
theorem hvb_andThen (a b : Bool) : c.hv boolAndThen [bool a, bool b] = some (bool (a && b)) := hv_of_value rfl
theorem hvb_or (a b : Bool) : c.hv boolOr [bool a, bool b] = some (bool (a || b)) := hv_of_value rfl
theorem hvb_orElse (a b : Bool) : c.hv boolOrElse [bool a, bool b] = some (bool (a || b)) := hv_of_value rfl
theorem hvb_xor (a b : Bool) : c.hv boolXor [bool a, bool b] = some (bool (a != b)) := hv_of_value rfl
theorem hvb_implies (a b : Bool) : c.hv boolImplies [bool a, bool b] = some (bool (!a || b)) := hv_of_value rfl
theorem hvb_not (a : Bool) : c.hv boolNot [bool a] = some (bool !a) := hv_of_value rfl

theorem dv_bool (b : Bool) : GroundTerm.dv Srt.bool (.bool b) = bool b := rfl

end

/-- An equation over one Bool variable holds where its sides are equal at `true` and at `false`. -/
local macro "bool1_holds " hs:term:max X:ident n0:str : tactic => `(tactic| (
  intro σ hσ _
  obtain ⟨b, hb⟩ := bool_at $hs hσ 0 (n := $n0) rfl
  simp only [$X:ident, boolT, val, valList, allSome, hb, Option.bind_some, Option.map_some, dv_bool, hvb_and,
    hvb_andThen, hvb_or, hvb_orElse, hvb_xor, hvb_implies, hvb_not]
  cases b <;> rfl))

/-! ## 1142: `B andBool true => B` -/

def bAndTrue : Eqn :=
  ⟨[("VarB", Srt.bool)], Srt.bool, none, .app boolAnd [.var 0, boolT true], .var 0⟩

theorem bAndTrue_holds {c : Semantics} (hs : c.shapesOK = true) : bAndTrue.Holds c := by
  bool1_holds hs bAndTrue "VarB"

theorem bAndTrue_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bAndTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bAndTrue (by decide) (by rfl) (bAndTrue_holds hs) ad hp hsv

/-! ## 1144: `_ andBool false => false` -/

def bAndFalse : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.bool)], Srt.bool, none, .app boolAnd [.var 0, boolT false], boolT false⟩

theorem bAndFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bAndFalse.Holds c := by
  bool1_holds hs bAndFalse "Var'Unds'Gen0"

theorem bAndFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bAndFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bAndFalse (by decide) (by rfl) (bAndFalse_holds hs) ad hp hsv

/-! ## 1147: `K andThenBool true => K` -/

def bAndThenTrue : Eqn :=
  ⟨[("VarK", Srt.bool)], Srt.bool, none, .app boolAndThen [.var 0, boolT true], .var 0⟩

theorem bAndThenTrue_holds {c : Semantics} (hs : c.shapesOK = true) : bAndThenTrue.Holds c := by
  bool1_holds hs bAndThenTrue "VarK"

theorem bAndThenTrue_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bAndThenTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bAndThenTrue (by decide) (by rfl) (bAndThenTrue_holds hs) ad hp hsv

/-! ## 1149: `_ andThenBool false => false` -/

def bAndThenFalse : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.bool)], Srt.bool, none, .app boolAndThen [.var 0, boolT false], boolT false⟩

theorem bAndThenFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bAndThenFalse.Holds c := by
  bool1_holds hs bAndThenFalse "Var'Unds'Gen0"

theorem bAndThenFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bAndThenFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bAndThenFalse (by decide) (by rfl) (bAndThenFalse_holds hs) ad hp hsv

/-! ## 1152: `B xorBool false => B` -/

def bXorFalse : Eqn :=
  ⟨[("VarB", Srt.bool)], Srt.bool, none, .app boolXor [.var 0, boolT false], .var 0⟩

theorem bXorFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bXorFalse.Holds c := by
  bool1_holds hs bXorFalse "VarB"

theorem bXorFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bXorFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bXorFalse (by decide) (by rfl) (bXorFalse_holds hs) ad hp hsv

/-! ## 1156: `_ orBool true => true` -/

def bOrTrue : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.bool)], Srt.bool, none, .app boolOr [.var 0, boolT true], boolT true⟩

theorem bOrTrue_holds {c : Semantics} (hs : c.shapesOK = true) : bOrTrue.Holds c := by
  bool1_holds hs bOrTrue "Var'Unds'Gen0"

theorem bOrTrue_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bOrTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bOrTrue (by decide) (by rfl) (bOrTrue_holds hs) ad hp hsv

/-! ## 1158: `B orBool false => B` -/

def bOrFalse : Eqn :=
  ⟨[("VarB", Srt.bool)], Srt.bool, none, .app boolOr [.var 0, boolT false], .var 0⟩

theorem bOrFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bOrFalse.Holds c := by
  bool1_holds hs bOrFalse "VarB"

theorem bOrFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bOrFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bOrFalse (by decide) (by rfl) (bOrFalse_holds hs) ad hp hsv

/-! ## 1161: `_ orElseBool true => true` -/

def bOrElseTrue : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.bool)], Srt.bool, none, .app boolOrElse [.var 0, boolT true], boolT true⟩

theorem bOrElseTrue_holds {c : Semantics} (hs : c.shapesOK = true) : bOrElseTrue.Holds c := by
  bool1_holds hs bOrElseTrue "Var'Unds'Gen0"

theorem bOrElseTrue_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bOrElseTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bOrElseTrue (by decide) (by rfl) (bOrElseTrue_holds hs) ad hp hsv

/-! ## 1163: `K orElseBool false => K` -/

def bOrElseFalse : Eqn :=
  ⟨[("VarK", Srt.bool)], Srt.bool, none, .app boolOrElse [.var 0, boolT false], .var 0⟩

theorem bOrElseFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bOrElseFalse.Holds c := by
  bool1_holds hs bOrElseFalse "VarK"

theorem bOrElseFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bOrElseFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bOrElseFalse (by decide) (by rfl) (bOrElseFalse_holds hs) ad hp hsv

/-! ## 1167: `_ impliesBool true => true` -/

def bImpliesTrue : Eqn :=
  ⟨[("Var'Unds'Gen0", Srt.bool)], Srt.bool, none, .app boolImplies [.var 0, boolT true], boolT true⟩

theorem bImpliesTrue_holds {c : Semantics} (hs : c.shapesOK = true) : bImpliesTrue.Holds c := by
  bool1_holds hs bImpliesTrue "Var'Unds'Gen0"

theorem bImpliesTrue_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bImpliesTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bImpliesTrue (by decide) (by rfl) (bImpliesTrue_holds hs) ad hp hsv

/-! ## 1168: `B impliesBool false => notBool B` -/

def bImpliesFalse : Eqn :=
  ⟨[("VarB", Srt.bool)], Srt.bool, none, .app boolImplies [.var 0, boolT false], .app boolNot [.var 0]⟩

theorem bImpliesFalse_holds {c : Semantics} (hs : c.shapesOK = true) : bImpliesFalse.Holds c := by
  bool1_holds hs bImpliesFalse "VarB"

theorem bImpliesFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = bImpliesFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h bImpliesFalse (by decide) (by rfl) (bImpliesFalse_holds hs) ad hp hsv

end LibEv

end KCore
