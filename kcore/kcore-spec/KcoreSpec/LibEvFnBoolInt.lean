/-
  KCore, checked layer: the equations of BOOL and INT in the function form (`LibEv.FnEqn`) over
  interpreted hooked symbols, entailed at values in every semantics meeting `coreOK` whose Int and
  Bool values are literals (`shapesOK`), for every interpretation: none reaches a silent point.
  With `KcoreSpec/LibEvFnLib.lean`'s four these are every such equation of domains.md 1138 to 1170
  and 1438 to 1457 (K 7.1.337) whose symbols are interpreted.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`.
  - `fnBLit f name b r`: `f(b, V) => V` (`r = none`) or `f(b, V) => r'` (`r = some r'`), for a
    Bool symbol `f` and a Bool literal `b`; its instances
    `fnAndTrue` (1141), `fnAndThenTrue` (1146), `fnXorFalse` (1151), `fnOrTrue` (1155),
    `fnOrFalse` (1157), `fnOrElseTrue` (1160), `fnOrElseFalse` (1162), `fnImpliesTrue` (1165),
    `fnImpliesFalse` (1166).
  - `fnAndThenFalse` (1148): `false #as _Gen1 andThenBool _Gen0 => _Gen1`.
  - `fnNotTrue` (1138), `fnNotFalse` (1139): `notBool true => false`, `notBool false => true`.
  - `fnXorSame` (1153): `B xorBool B => false`.
  - `fnNeBool` (1170): `B1 =/=Bool B2 => notBool (B1 ==Bool B2)`.
  - `fnDivInt` (1442): `I1 divInt I2 => (I1 -Int (I1 modInt I2)) /Int I2 requires I2 =/=Int 0`.
  - `fnFreshInt` (1457): `freshInt(I) => I`.
-/
import KcoreSpec.LibEvFnLib

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

section
variable {c : Semantics}

theorem fhv_boolAndThen (a b : Bool) : c.hv boolAndThen [bool a, bool b] = some (bool (a && b)) := hv_of_value rfl
theorem fhv_boolOr (a b : Bool) : c.hv boolOr [bool a, bool b] = some (bool (a || b)) := hv_of_value rfl
theorem fhv_boolOrElse (a b : Bool) : c.hv boolOrElse [bool a, bool b] = some (bool (a || b)) := hv_of_value rfl
theorem fhv_boolXor (a b : Bool) : c.hv boolXor [bool a, bool b] = some (bool (a != b)) := hv_of_value rfl
theorem fhv_boolImplies (a b : Bool) : c.hv boolImplies [bool a, bool b] = some (bool (!a || b)) := hv_of_value rfl
theorem fhv_boolEq (a b : Bool) : c.hv boolEq [bool a, bool b] = some (bool (a == b)) := hv_of_value rfl
theorem fhv_boolNe (a b : Bool) : c.hv boolNe [bool a, bool b] = some (bool (a != b)) := hv_of_value rfl
theorem fhv_freshInt (x : Int) : c.hv freshInt [int x] = some (int x) := hv_of_value rfl
theorem fhv_intEDiv {x y : Int} (hy : y ≠ 0) : c.hv intEDiv [int x, int y] = some (int (x.ediv y)) :=
  hv_of_value (by
    show hook intEDiv [int x, int y] = some (some (int (x.ediv y)))
    have : hook intEDiv [int x, int y] = some (nonzero y (x.ediv y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])
theorem fhv_intEMod {x y : Int} (hy : y ≠ 0) : c.hv intEMod [int x, int y] = some (int (x.emod y)) :=
  hv_of_value (by
    show hook intEMod [int x, int y] = some (some (int (x.emod y)))
    have : hook intEMod [int x, int y] = some (nonzero y (x.emod y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])
theorem fhv_intTDiv {x y : Int} (hy : y ≠ 0) : c.hv intTDiv [int x, int y] = some (int (x.tdiv y)) :=
  hv_of_value (by
    show hook intTDiv [int x, int y] = some (some (int (x.tdiv y)))
    have : hook intTDiv [int x, int y] = some (nonzero y (x.tdiv y)) := rfl
    rw [this, nonzero]; simp only [hy, ↓reduceIte])

end

/-! ## `f(b, V) => V` and `f(b, V) => r` -/

/-- `f(b, V) => V` (`r = none`) or `f(b, V) => r'` (`r = some r'`), the variable named `name`. -/
def fnBLit (f : Sym) (name : String) (b : Bool) (r : Option Bool) : FnEqn :=
  ⟨[(name, Srt.bool)], f, [(Srt.bool, fqB b, none), (Srt.bool, .var 0, none)], Srt.bool, none,
    match r with
    | none => .var 0
    | some r' => fqB r'⟩

theorem fnBLit_holds {c : Semantics} (hs : c.shapesOK = true) {f : Sym} {op : Bool → Bool → Bool}
    (hf : ∀ a b, c.hv f [bool a, bool b] = some (bool (op a b))) (name : String) (b : Bool) (r : Option Bool)
    (hop : ∀ x, op b x = r.getD x) : (fnBLit f name b r).Holds c := by
  intro σ hσ _ hm
  obtain ⟨y, hy⟩ := fq_bool_at hs hσ 0 (n := name) rfl
  obtain ⟨h1, -, h2, -⟩ := hm
  rw [fq_val_var] at h2
  have h1' : σ.lookup 1 = some (bool b) := h1.symm
  have h2' : σ.lookup 2 = some (bool y) := h2.symm.trans hy
  cases r with
  | none => fq_eval [fnBLit, h1', h2', hy, hf, hop, Option.getD_none]
  | some r' => fq_eval [fnBLit, h1', h2', hy, hf, hop, Option.getD_some]

theorem fnBLit_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) {f : Sym}
    {op : Bool → Bool → Bool} (hf : ∀ a b, c.hv f [bool a, bool b] = some (bool (op a b))) (name : String)
    (b : Bool) (r : Option Bool) (hop : ∀ x, op b x = r.getD x) (hr : (fnBLit f name b r).regular = true)
    (ht : (fnBLit f name b r).typed c = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = (fnBLit f name b r).patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h _ hr ht (fnBLit_holds hs hf name b r hop) ad hp hsv

/-- 1141: `true andBool B => B`. -/
def fnAndTrue : FnEqn := fnBLit boolAnd "VarB" true none
/-- 1146: `true andThenBool K => K`. -/
def fnAndThenTrue : FnEqn := fnBLit boolAndThen "VarK" true none
/-- 1151: `false xorBool B => B`. -/
def fnXorFalse : FnEqn := fnBLit boolXor "VarB" false none
/-- 1155: `true orBool _ => true`. -/
def fnOrTrue : FnEqn := fnBLit boolOr "Var'Unds'Gen0" true (some true)
/-- 1157: `false orBool B => B`. -/
def fnOrFalse : FnEqn := fnBLit boolOr "VarB" false none
/-- 1160: `true orElseBool _ => true`. -/
def fnOrElseTrue : FnEqn := fnBLit boolOrElse "Var'Unds'Gen0" true (some true)
/-- 1162: `false orElseBool K => K`. -/
def fnOrElseFalse : FnEqn := fnBLit boolOrElse "VarK" false none
/-- 1165: `true impliesBool B => B`. -/
def fnImpliesTrue : FnEqn := fnBLit boolImplies "VarB" true none
/-- 1166: `false impliesBool _ => true`. -/
def fnImpliesFalse : FnEqn := fnBLit boolImplies "Var'Unds'Gen0" false (some true)

section
variable {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
  (hsv : ad.ax.sortVars = [KoreAML.Rv])
include h hs hsv

theorem fnAndTrue_ev (hp : ad.ax.pattern = fnAndTrue.patR) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolAnd _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnAndThenTrue_ev (hp : ad.ax.pattern = fnAndThenTrue.patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolAndThen _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnXorFalse_ev (hp : ad.ax.pattern = fnXorFalse.patR) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolXor _ _ _ (by decide) (by decide) (by rfl) ad hp hsv
theorem fnOrTrue_ev (hp : ad.ax.pattern = fnOrTrue.patR) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolOr _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnOrFalse_ev (hp : ad.ax.pattern = fnOrFalse.patR) : EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolOr _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnOrElseTrue_ev (hp : ad.ax.pattern = fnOrElseTrue.patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolOrElse _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnOrElseFalse_ev (hp : ad.ax.pattern = fnOrElseFalse.patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolOrElse _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnImpliesTrue_ev (hp : ad.ax.pattern = fnImpliesTrue.patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolImplies _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv
theorem fnImpliesFalse_ev (hp : ad.ax.pattern = fnImpliesFalse.patR) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  fnBLit_ev h hs fhv_boolImplies _ _ _ (fun _ => rfl) (by decide) (by rfl) ad hp hsv

end

/-! ## 1148: `false #as _Gen1 andThenBool _Gen0 => _Gen1` -/

def fnAndThenFalse : FnEqn := fnBAs boolAndThen

theorem fnAndThenFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnAndThenFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnAndThenFalse (by decide) (by rfl) (fnBAs_holds hs fhv_boolAndThen (fun _ => rfl)) ad hp hsv

/-! ## 1138, 1139: `notBool true => false`, `notBool false => true` -/

/-- `notBool b => !b`. -/
def fnNot (b : Bool) : FnEqn := ⟨[], boolNot, [(Srt.bool, fqB b, none)], Srt.bool, none, fqB !b⟩

def fnNotTrue : FnEqn := fnNot true
def fnNotFalse : FnEqn := fnNot false

theorem fnNot_holds {c : Semantics} (b : Bool) : (fnNot b).Holds c := by
  intro σ _ _ hm
  obtain ⟨h0, -, -⟩ := hm
  have h0' : σ.lookup 0 = some (bool b) := h0.symm
  fq_eval [fnNot, h0', fhv_boolNot]

theorem fnNotTrue_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNotTrue.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNotTrue (by decide) (by rfl) (fnNot_holds true) ad hp hsv

theorem fnNotFalse_ev {c : Semantics} (h : c.coreOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNotFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNotFalse (by decide) (by rfl) (fnNot_holds false) ad hp hsv

/-! ## 1153: `B xorBool B => false` -/

def fnXorSame : FnEqn :=
  ⟨[("VarB", Srt.bool)], boolXor, [(Srt.bool, .var 0, none), (Srt.bool, .var 0, none)], Srt.bool, none, fqB false⟩

theorem fnXorSame_holds {c : Semantics} (hs : c.shapesOK = true) : fnXorSame.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := fq_bool_at hs hσ 0 (n := "VarB") rfl
  obtain ⟨h1, -, h2, -⟩ := hm
  rw [fq_val_var] at h1 h2
  have h1' : σ.lookup 1 = some (bool x) := h1.symm.trans hx
  have h2' : σ.lookup 2 = some (bool x) := h2.symm.trans hx
  fq_eval [fnXorSame, h1', h2', fhv_boolXor]
  simp

theorem fnXorSame_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnXorSame.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnXorSame (by decide) (by rfl) (fnXorSame_holds hs) ad hp hsv

/-! ## 1170: `B1 =/=Bool B2 => notBool (B1 ==Bool B2)` -/

def fnNeBool : FnEqn :=
  ⟨[("VarB1", Srt.bool), ("VarB2", Srt.bool)], boolNe, [(Srt.bool, .var 0, none), (Srt.bool, .var 1, none)],
    Srt.bool, none, .app boolNot [.app boolEq [.var 0, .var 1]]⟩

theorem fnNeBool_holds {c : Semantics} (hs : c.shapesOK = true) : fnNeBool.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := fq_bool_at hs hσ 0 (n := "VarB1") rfl
  obtain ⟨y, hy⟩ := fq_bool_at hs hσ 1 (n := "VarB2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (bool x) := h2.symm.trans hx
  have h3' : σ.lookup 3 = some (bool y) := h3.symm.trans hy
  fq_eval [fnNeBool, h2', h3', hx, hy, fhv_boolNe, fhv_boolEq, fhv_boolNot]
  cases x <;> cases y <;> rfl

theorem fnNeBool_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeBool.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeBool (by decide) (by rfl) (fnNeBool_holds hs) ad hp hsv

/-! ## 1442: `I1 divInt I2 => (I1 -Int (I1 modInt I2)) /Int I2 requires I2 =/=Int 0` -/

/-- The Euclidean quotient by a nonzero `y` is the truncated quotient of `x` less its Euclidean
remainder: that difference is a multiple of `y`. -/
theorem fq_ediv_as_tdiv (x : Int) {y : Int} (hy : y ≠ 0) : x.ediv y = (x - x.emod y).tdiv y := by
  have h1 : x - x.emod y = y * x.ediv y := by
    have := Int.emod_add_mul_ediv x y
    change x.emod y + y * x.ediv y = x at this
    omega
  rw [h1, Int.mul_tdiv_cancel_left _ hy]

def fnDivInt : FnEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], intEDiv, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.int,
    some (.app intNe [.var 1, intT 0]),
    .app intTDiv [.app intSub [.var 0, .app intEMod [.var 0, .var 1]], .var 1]⟩

theorem fnDivInt_holds {c : Semantics} (hs : c.shapesOK = true) : fnDivInt.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI1") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (int x) := h2.symm.trans hx
  have h3' : σ.lookup 3 = some (int y) := h3.symm.trans hy
  have hq := hreq _ rfl
  simp only [intT, val, valList, allSome, hy, Option.bind_some, Option.map_some, dv_int, fhv_intNe,
    Option.some.injEq] at hq
  have hb : y ≠ 0 := of_decide_eq_true (fq_bool_inj hq)
  fq_eval [fnDivInt, h2', h3', hx, hy, fhv_intEDiv hb, fhv_intEMod hb, hv_intSub, fhv_intTDiv hb]
  rw [fq_ediv_as_tdiv x hb]

theorem fnDivInt_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnDivInt.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnDivInt (by decide) (by rfl) (fnDivInt_holds hs) ad hp hsv

/-! ## 1457: `freshInt(I) => I` -/

def fnFreshInt : FnEqn := ⟨[("VarI", Srt.int)], freshInt, [(Srt.int, .var 0, none)], Srt.int, none, .var 0⟩

theorem fnFreshInt_holds {c : Semantics} (hs : c.shapesOK = true) : fnFreshInt.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI") rfl
  obtain ⟨h1, -, -⟩ := hm
  rw [fq_val_var] at h1
  have h1' : σ.lookup 1 = some (int x) := h1.symm.trans hx
  fq_eval [fnFreshInt, h1', hx, fhv_freshInt]

theorem fnFreshInt_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnFreshInt.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnFreshInt (by decide) (by rfl) (fnFreshInt_holds hs) ad hp hsv

end LibEv

end KCore
