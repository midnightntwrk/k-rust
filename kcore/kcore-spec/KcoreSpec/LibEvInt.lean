/-
  KCore, checked layer: equations of the builtin library's INT lemmas, entailed at values in every
  semantics meeting `coreOK` whose Int and Bool values are literals (`shapesOK`), for every
  interpretation: none of them reaches a silent point.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`. The line numbers are those of domains.md in K 7.1.337.
  - `addZero` (1373): `I +Int 0 => I`.
  - `subZero` (1374): `I -Int 0 => I`.
  - `addComm` (1415): `I +Int B => B +Int I`.
  - `subAsAdd` (1416): `A -Int I => A +Int (0 -Int I)`.
  - `tmodSmall` (1377): `X %Int N => X requires 0 <=Int X andBool X <Int N`.
  - `shlZero`, `zeroShl`, `shrZero`, `zeroShr` (1380 to 1383): `X <<Int 0 => X`,
    `0 <<Int Y => 0 requires 0 <=Int Y`, and the same for `>>Int`: off a negative shift the shifts
    have their value, and the `requires` keeps the second pair off it.
-/
import KcoreSpec.LibEv
import KcoreSpec.LazySound

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The Int literal `n` as a term. -/
def intT (n : Int) : Term := .dv Srt.int (.int n)

/-- A substitution of values of the variables' sorts gives an Int variable an Int literal. -/
theorem int_at {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.int)) : ∃ x : Int, σ.lookup i = some (int x) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨x, rfl⟩ := shape_int hs hsv
  exact ⟨x, hv⟩

section
variable {c : Semantics}

theorem hv_intAdd (x y : Int) : c.hv intAdd [int x, int y] = some (int (x + y)) := hv_of_value rfl
theorem hv_intSub (x y : Int) : c.hv intSub [int x, int y] = some (int (x - y)) := hv_of_value rfl
theorem hv_intLe (x y : Int) : c.hv intLe [int x, int y] = some (bool (decide (x ≤ y))) := hv_of_value rfl
theorem hv_intLt (x y : Int) : c.hv intLt [int x, int y] = some (bool (decide (x < y))) := hv_of_value rfl
theorem hv_boolAnd (a b : Bool) : c.hv boolAnd [bool a, bool b] = some (bool (a && b)) := hv_of_value rfl
theorem hv_intTMod {x y : Int} (hy : y ≠ 0) : c.hv intTMod [int x, int y] = some (int (x.tmod y)) :=
  hv_of_value (by
    show hook intTMod [int x, int y] = some (some (int (x.tmod y)))
    have : hook intTMod [int x, int y] = some (nonzero y (x.tmod y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])

theorem dv_int (n : Int) : GroundTerm.dv Srt.int (.int n) = int n := rfl

end

/-! ## 1373: `I +Int 0 => I` -/

def addZero : Eqn :=
  ⟨[("VarI", Srt.int)], Srt.int, none, .app intAdd [.var 0, intT 0], .var 0⟩

theorem addZero_holds {c : Semantics} (hs : c.shapesOK = true) : addZero.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  simp only [addZero, intT, val, valList, allSome, hx, Option.bind_some, Option.map_some, dv_int,
    hv_intAdd, Int.add_zero]

theorem addZero_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addZero.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addZero (by decide) (by rfl) (addZero_holds hs) ad hp hsv

/-! ## 1374: `I -Int 0 => I` -/

def subZero : Eqn :=
  ⟨[("VarI", Srt.int)], Srt.int, none, .app intSub [.var 0, intT 0], .var 0⟩

theorem subZero_holds {c : Semantics} (hs : c.shapesOK = true) : subZero.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  simp only [subZero, intT, val, valList, allSome, hx, Option.bind_some, Option.map_some, dv_int,
    hv_intSub, Int.sub_zero]

theorem subZero_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subZero.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subZero (by decide) (by rfl) (subZero_holds hs) ad hp hsv

/-! ## 1415: `I +Int B => B +Int I` -/

def addComm : Eqn :=
  ⟨[("VarI", Srt.int), ("VarB", Srt.int)], Srt.int, none, .app intAdd [.var 0, .var 1], .app intAdd [.var 1, .var 0]⟩

theorem addComm_holds {c : Semantics} (hs : c.shapesOK = true) : addComm.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarB") rfl
  simp only [addComm, val, valList, allSome, hx, hy, Option.bind_some, Option.map_some, hv_intAdd,
    Int.add_comm]

theorem addComm_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addComm.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addComm (by decide) (by rfl) (addComm_holds hs) ad hp hsv

/-! ## 1416: `A -Int I => A +Int (0 -Int I)` -/

def subAsAdd : Eqn :=
  ⟨[("VarA", Srt.int), ("VarI", Srt.int)], Srt.int, none, .app intSub [.var 0, .var 1],
    .app intAdd [.var 0, .app intSub [intT 0, .var 1]]⟩

theorem subAsAdd_holds {c : Semantics} (hs : c.shapesOK = true) : subAsAdd.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarA") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI") rfl
  simp only [subAsAdd, intT, val, valList, allSome, hx, hy, Option.bind_some, Option.map_some, dv_int,
    hv_intAdd, hv_intSub]
  congr 2
  omega

theorem subAsAdd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subAsAdd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subAsAdd (by decide) (by rfl) (subAsAdd_holds hs) ad hp hsv

/-! ## 1377: `X %Int N => X requires 0 <=Int X andBool X <Int N` -/

def tmodSmall : Eqn :=
  ⟨[("VarX", Srt.int), ("VarN", Srt.int)], Srt.int,
    some (.app boolAnd [.app intLe [intT 0, .var 0], .app intLt [.var 0, .var 1]]),
    .app intTMod [.var 0, .var 1], .var 0⟩

theorem tmodSmall_holds {c : Semantics} (hs : c.shapesOK = true) : tmodSmall.Holds c := by
  intro σ hσ hreq
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarX") rfl
  obtain ⟨n, hn⟩ := int_at hs hσ 1 (n := "VarN") rfl
  have hq := hreq _ rfl
  simp only [intT, val, valList, allSome, hx, hn, Option.bind_some, Option.map_some, dv_int,
    hv_intLe, hv_intLt, hv_boolAnd, Option.some.injEq] at hq
  have hb : (decide (0 ≤ x) && decide (x < n)) = true := by
    unfold bool at hq
    injection hq with _ hq
    injection hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [tmodSmall, val, valList, allSome, hx, hn, Option.bind_some, Option.map_some]
  rw [hv_intTMod (by omega), Int.tmod_eq_of_lt hb.1 hb.2]

theorem tmodSmall_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = tmodSmall.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h tmodSmall (by decide) (by rfl) (tmodSmall_holds hs) ad hp hsv

/-! ## 1418 to 1426: sums and differences of three terms regrouped -/

/-- An equation over three Int variables whose sides are sums and differences holds where the
two sides are equal integers. -/
local macro "int3_holds " hs:term:max X:ident n0:str n1:str n2:str : tactic => `(tactic| (
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at $hs hσ 0 (n := $n0) rfl
  obtain ⟨y, hy⟩ := int_at $hs hσ 1 (n := $n1) rfl
  obtain ⟨z, hz⟩ := int_at $hs hσ 2 (n := $n2) rfl
  simp only [$X:ident, val, valList, allSome, hx, hy, hz, Option.bind_some, Option.map_some, hv_intAdd,
    hv_intSub]
  exact congrArg (fun w => some (int w)) (by omega)))

/-- 1418: `(A +Int I2) +Int I3 => A +Int (I2 +Int I3)`. -/
def addAssoc : Eqn :=
  ⟨[("VarA", Srt.int), ("VarI2", Srt.int), ("VarI3", Srt.int)], Srt.int, none,
    .app intAdd [.app intAdd [.var 0, .var 1], .var 2], .app intAdd [.var 0, .app intAdd [.var 1, .var 2]]⟩

theorem addAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : addAssoc.Holds c := by
  int3_holds hs addAssoc "VarA" "VarI2" "VarI3"

theorem addAssoc_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addAssoc.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addAssoc (by decide) (by rfl) (addAssoc_holds hs) ad hp hsv

/-- 1419: `I1 +Int (B +Int I3) => B +Int (I1 +Int I3)`. -/
def addLeftComm : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarB", Srt.int), ("VarI3", Srt.int)], Srt.int, none,
    .app intAdd [.var 0, .app intAdd [.var 1, .var 2]], .app intAdd [.var 1, .app intAdd [.var 0, .var 2]]⟩

theorem addLeftComm_holds {c : Semantics} (hs : c.shapesOK = true) : addLeftComm.Holds c := by
  int3_holds hs addLeftComm "VarI1" "VarB" "VarI3"

theorem addLeftComm_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addLeftComm.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addLeftComm (by decide) (by rfl) (addLeftComm_holds hs) ad hp hsv

/-- 1420: `I1 -Int (B +Int I3) => (I1 -Int I3) -Int B`. -/
def subAddSwap : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarB", Srt.int), ("VarI3", Srt.int)], Srt.int, none,
    .app intSub [.var 0, .app intAdd [.var 1, .var 2]], .app intSub [.app intSub [.var 0, .var 2], .var 1]⟩

theorem subAddSwap_holds {c : Semantics} (hs : c.shapesOK = true) : subAddSwap.Holds c := by
  int3_holds hs subAddSwap "VarI1" "VarB" "VarI3"

theorem subAddSwap_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subAddSwap.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subAddSwap (by decide) (by rfl) (subAddSwap_holds hs) ad hp hsv

/-- 1421: `I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C`. -/
def addAssocRev : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int), ("VarC", Srt.int)], Srt.int, none,
    .app intAdd [.var 0, .app intAdd [.var 1, .var 2]], .app intAdd [.app intAdd [.var 0, .var 1], .var 2]⟩

theorem addAssocRev_holds {c : Semantics} (hs : c.shapesOK = true) : addAssocRev.Holds c := by
  int3_holds hs addAssocRev "VarI1" "VarI2" "VarC"

theorem addAssocRev_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addAssocRev.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addAssocRev (by decide) (by rfl) (addAssocRev_holds hs) ad hp hsv

/-- 1422: `I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C`. -/
def addSubAssoc : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int), ("VarC", Srt.int)], Srt.int, none,
    .app intAdd [.var 0, .app intSub [.var 1, .var 2]], .app intSub [.app intAdd [.var 0, .var 1], .var 2]⟩

theorem addSubAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : addSubAssoc.Holds c := by
  int3_holds hs addSubAssoc "VarI1" "VarI2" "VarC"

theorem addSubAssoc_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = addSubAssoc.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h addSubAssoc (by decide) (by rfl) (addSubAssoc_holds hs) ad hp hsv

/-- 1423: `(I1 -Int B) +Int I3 => (I1 +Int I3) -Int B`. -/
def subAddComm : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarB", Srt.int), ("VarI3", Srt.int)], Srt.int, none,
    .app intAdd [.app intSub [.var 0, .var 1], .var 2], .app intSub [.app intAdd [.var 0, .var 2], .var 1]⟩

theorem subAddComm_holds {c : Semantics} (hs : c.shapesOK = true) : subAddComm.Holds c := by
  int3_holds hs subAddComm "VarI1" "VarB" "VarI3"

theorem subAddComm_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subAddComm.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subAddComm (by decide) (by rfl) (subAddComm_holds hs) ad hp hsv

/-- 1424: `I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C`. -/
def subAddAssoc : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int), ("VarC", Srt.int)], Srt.int, none,
    .app intSub [.var 0, .app intAdd [.var 1, .var 2]], .app intSub [.app intSub [.var 0, .var 1], .var 2]⟩

theorem subAddAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : subAddAssoc.Holds c := by
  int3_holds hs subAddAssoc "VarI1" "VarI2" "VarC"

theorem subAddAssoc_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subAddAssoc.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subAddAssoc (by decide) (by rfl) (subAddAssoc_holds hs) ad hp hsv

/-- 1425: `I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C`. -/
def subSubAssoc : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int), ("VarC", Srt.int)], Srt.int, none,
    .app intSub [.var 0, .app intSub [.var 1, .var 2]], .app intAdd [.app intSub [.var 0, .var 1], .var 2]⟩

theorem subSubAssoc_holds {c : Semantics} (hs : c.shapesOK = true) : subSubAssoc.Holds c := by
  int3_holds hs subSubAssoc "VarI1" "VarI2" "VarC"

theorem subSubAssoc_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subSubAssoc.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subSubAssoc (by decide) (by rfl) (subSubAssoc_holds hs) ad hp hsv

/-- 1426: `(C -Int I2) -Int I3 => C -Int (I2 +Int I3)`. -/
def subSubAdd : Eqn :=
  ⟨[("VarC", Srt.int), ("VarI2", Srt.int), ("VarI3", Srt.int)], Srt.int, none,
    .app intSub [.app intSub [.var 0, .var 1], .var 2], .app intSub [.var 0, .app intAdd [.var 1, .var 2]]⟩

theorem subSubAdd_holds {c : Semantics} (hs : c.shapesOK = true) : subSubAdd.Holds c := by
  int3_holds hs subSubAdd "VarC" "VarI2" "VarI3"

theorem subSubAdd_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = subSubAdd.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h subSubAdd (by decide) (by rfl) (subSubAdd_holds hs) ad hp hsv

/-! ## 1376: `X modInt N => X requires 0 <=Int X andBool X <Int N` -/

theorem hv_intEMod {c : Semantics} {x y : Int} (hy : y ≠ 0) : c.hv intEMod [int x, int y] = some (int (x.emod y)) :=
  hv_of_value (by
    show hook intEMod [int x, int y] = some (some (int (x.emod y)))
    have : hook intEMod [int x, int y] = some (nonzero y (x.emod y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])

theorem hv_intNe {c : Semantics} (x y : Int) : c.hv intNe [int x, int y] = some (bool (decide (x ≠ y))) :=
  hv_of_value rfl

theorem hv_intAbs {c : Semantics} (x : Int) : c.hv intAbs [int x] = some (int x.natAbs) := hv_of_value rfl

def emodSmall : Eqn :=
  ⟨[("VarX", Srt.int), ("VarN", Srt.int)], Srt.int,
    some (.app boolAnd [.app intLe [intT 0, .var 0], .app intLt [.var 0, .var 1]]),
    .app intEMod [.var 0, .var 1], .var 0⟩

theorem emodSmall_holds {c : Semantics} (hs : c.shapesOK = true) : emodSmall.Holds c := by
  intro σ hσ hreq
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarX") rfl
  obtain ⟨n, hn⟩ := int_at hs hσ 1 (n := "VarN") rfl
  have hq := hreq _ rfl
  simp only [intT, val, valList, allSome, hx, hn, Option.bind_some, Option.map_some, dv_int,
    hv_intLe, hv_intLt, hv_boolAnd, Option.some.injEq] at hq
  have hb : (decide (0 ≤ x) && decide (x < n)) = true := by
    unfold bool at hq
    injection hq with _ hq
    injection hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [emodSmall, val, valList, allSome, hx, hn, Option.bind_some, Option.map_some]
  rw [hv_intEMod (by omega)]
  show some (int (x % n)) = _
  rw [Int.emod_eq_of_lt hb.1 hb.2]

theorem emodSmall_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = emodSmall.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h emodSmall (by decide) (by rfl) (emodSmall_holds hs) ad hp hsv

/-! ## 1445: `I1 modInt I2 => ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2) requires I2 =/=Int 0` -/

def emodAsTmod : Eqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], Srt.int,
    some (.app intNe [.var 1, intT 0]),
    .app intEMod [.var 0, .var 1],
    .app intTMod [.app intAdd [.app intTMod [.var 0, .app intAbs [.var 1]], .app intAbs [.var 1]],
      .app intAbs [.var 1]]⟩

/-- The Euclidean remainder by a nonzero `y` is the truncated remainder by `|y|`, moved into
`[0, |y|)` by adding `|y|` and taking the truncated remainder again. -/
theorem emod_as_tmod (x : Int) {y : Int} (hy : y ≠ 0) :
    x.emod y = ((x.tmod y.natAbs) + y.natAbs).tmod y.natAbs := by
  have ha : (0 : Int) < y.natAbs := by omega
  have h2 := Int.lt_tmod_of_pos x ha
  have h3 : x % (y.natAbs : Int) = x % y := by
    rcases Int.le_total 0 y with h | h
    · rw [Int.natAbs_of_nonneg h]
    · rw [Int.ofNat_natAbs_of_nonpos h, Int.emod_neg]
  rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.add_emod_right, Int.tmod_def, Int.sub_emod, Int.mul_emod_right,
    Int.sub_zero, Int.emod_emod_of_dvd _ (Int.dvd_refl _), h3]
  rfl

theorem emodAsTmod_holds {c : Semantics} (hs : c.shapesOK = true) : emodAsTmod.Holds c := by
  intro σ hσ hreq
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI1") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI2") rfl
  have hq := hreq _ rfl
  simp only [intT, val, valList, allSome, hy, Option.bind_some, Option.map_some, dv_int,
    hv_intNe, Option.some.injEq] at hq
  have hb : decide (y ≠ 0) = true := by
    unfold bool at hq
    injection hq with _ hq
    injection hq
  have hy0 : y ≠ 0 := of_decide_eq_true hb
  have ha : (y.natAbs : Int) ≠ 0 := by omega
  simp only [emodAsTmod, val, valList, allSome, hx, hy, Option.bind_some, Option.map_some, hv_intAbs,
    hv_intTMod ha, hv_intAdd, hv_intEMod hy0]
  rw [emod_as_tmod x hy0]

theorem emodAsTmod_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = emodAsTmod.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h emodAsTmod (by decide) (by rfl) (emodAsTmod_holds hs) ad hp hsv

/-! ## 1380 to 1383: the shifts at a zero operand -/

theorem hv_intShl {c : Semantics} {x n : Int} (hn : 0 ≤ n) :
    c.hv intShl [int x, int n] = some (int (x * 2 ^ n.toNat)) :=
  hv_of_value (by
    show hook intShl [int x, int n] = some (some (int (x * 2 ^ n.toNat)))
    have : hook intShl [int x, int n] = some (if n < 0 then none else some (int (x * 2 ^ n.toNat))) := rfl
    rw [this]; simp only [show ¬ n < 0 by omega, ↓reduceIte])

theorem hv_intShr {c : Semantics} {x n : Int} (hn : 0 ≤ n) :
    c.hv intShr [int x, int n] = some (int (x.fdiv (2 ^ n.toNat))) :=
  hv_of_value (by
    show hook intShr [int x, int n] = some (some (int (x.fdiv (2 ^ n.toNat))))
    have : hook intShr [int x, int n] = some (if n < 0 then none else some (int (x.fdiv (2 ^ n.toNat)))) := rfl
    rw [this]; simp only [show ¬ n < 0 by omega, ↓reduceIte])

/-- 1380: `X <<Int 0 => X`. -/
def shlZero : Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app intShl [.var 0, intT 0], .var 0⟩

/-- 1382: `X >>Int 0 => X`. -/
def shrZero : Eqn :=
  ⟨[("VarX", Srt.int)], Srt.int, none, .app intShr [.var 0, intT 0], .var 0⟩

/-- 1381: `0 <<Int Y => 0 requires 0 <=Int Y`. -/
def zeroShl : Eqn :=
  ⟨[("VarY", Srt.int)], Srt.int, some (.app intLe [intT 0, .var 0]), .app intShl [intT 0, .var 0], intT 0⟩

/-- 1383: `0 >>Int Y => 0 requires 0 <=Int Y`. -/
def zeroShr : Eqn :=
  ⟨[("VarY", Srt.int)], Srt.int, some (.app intLe [intT 0, .var 0]), .app intShr [intT 0, .var 0], intT 0⟩

theorem shlZero_holds {c : Semantics} (hs : c.shapesOK = true) : shlZero.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarX") rfl
  simp only [shlZero, intT, val, valList, allSome, hx, Option.bind_some, Option.map_some, dv_int]
  rw [hv_intShl (Int.le_refl 0)]
  simp

theorem shrZero_holds {c : Semantics} (hs : c.shapesOK = true) : shrZero.Holds c := by
  intro σ hσ _
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarX") rfl
  simp only [shrZero, intT, val, valList, allSome, hx, Option.bind_some, Option.map_some, dv_int]
  rw [hv_intShr (Int.le_refl 0)]
  simp

/-- The `requires` `0 <=Int Y` at a value of `Y`. -/
theorem le0_of_req {c : Semantics} {σ : Subst} {y : Int} (hy : σ.lookup 0 = some (int y))
    (hq : val c σ (.app intLe [intT 0, .var 0]) = some (bool true)) : 0 ≤ y := by
  simp only [intT, val, valList, allSome, hy, Option.bind_some, Option.map_some, dv_int, hv_intLe,
    Option.some.injEq] at hq
  have hb : decide (0 ≤ y) = true := by
    unfold bool at hq
    injection hq with _ hq
    injection hq
  exact of_decide_eq_true hb

theorem zeroShl_holds {c : Semantics} (hs : c.shapesOK = true) : zeroShl.Holds c := by
  intro σ hσ hreq
  obtain ⟨y, hy⟩ := int_at hs hσ 0 (n := "VarY") rfl
  have h0 := le0_of_req hy (hreq _ rfl)
  simp only [zeroShl, intT, val, valList, allSome, hy, Option.bind_some, Option.map_some, dv_int]
  rw [hv_intShl h0]
  simp

theorem zeroShr_holds {c : Semantics} (hs : c.shapesOK = true) : zeroShr.Holds c := by
  intro σ hσ hreq
  obtain ⟨y, hy⟩ := int_at hs hσ 0 (n := "VarY") rfl
  have h0 := le0_of_req hy (hreq _ rfl)
  simp only [zeroShr, intT, val, valList, allSome, hy, Option.bind_some, Option.map_some, dv_int]
  rw [hv_intShr h0]
  simp

theorem shlZero_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = shlZero.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h shlZero (by decide) (by rfl) (shlZero_holds hs) ad hp hsv

theorem shrZero_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = shrZero.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h shrZero (by decide) (by rfl) (shrZero_holds hs) ad hp hsv

theorem zeroShl_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = zeroShl.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h zeroShl (by decide) (by rfl) (zeroShl_holds hs) ad hp hsv

theorem zeroShr_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = zeroShr.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  Eqn.entailed_reg h zeroShr (by decide) (by rfl) (zeroShr_holds hs) ad hp hsv

end LibEv

end KCore
