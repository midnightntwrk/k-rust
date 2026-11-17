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

end LibEv

end KCore
