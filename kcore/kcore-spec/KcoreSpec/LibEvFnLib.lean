/-
  KCore, checked layer: equations of the builtin library in the function form (`LibEv.FnEqn`),
  entailed at values in every semantics meeting `coreOK` whose Int and Bool values are literals
  (`shapesOK`), for every interpretation: none of them reaches a silent point.

  Each is stated once, over the registry's names: `X_ev` takes any axiom declaration of a text
  whose pattern is `X.patR`. The line numbers are those of domains.md in K 7.1.337.
  - `fnNeInt` (1453): `I1 =/=Int I2 => notBool (I1 ==Int I2)`.
  - `fnMinLt` (1450): `minInt(I1, I2) => I1 requires I1 <Int I2`.
  - `fnMinGe` (1451): `minInt(I1, I2) => I2 requires I1 >=Int I2`.
  - `fnAndFalse` (1143): `false #as _Gen1 andBool _Gen0 => _Gen1`, an instance of `fnBAs`: a Bool
    symbol at the literal `false #as _Gen1` and any second argument is `_Gen1`.
-/
import KcoreSpec.LibEvFn
import KcoreSpec.LibEvInt

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- The Bool literal `b` as a term. -/
def fqB (b : Bool) : Term := .dv Srt.bool (.bool b)

/-- A substitution of values of the variables' sorts gives a Bool variable a Bool literal. -/
theorem fq_bool_at {c : Semantics} (hs : c.shapesOK = true) {vars : Vars} {σ : Subst}
    (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
    (i : Nat) {n : String} (hi : vars[i]? = some (n, Srt.bool)) : ∃ x : Bool, σ.lookup i = some (bool x) := by
  obtain ⟨v, hv, hsv⟩ := hσ i _ hi
  obtain ⟨x, rfl⟩ := shape_bool hs hsv
  exact ⟨x, hv⟩

theorem fq_bool_inj {a b : Bool} (h : bool a = bool b) : a = b := by
  unfold bool at h
  injection h with _ h
  injection h

theorem fq_int_inj {a b : Int} (h : int a = int b) : a = b := by
  unfold int at h
  injection h with _ h
  injection h

section
variable {c : Semantics}

theorem fhv_intEq (x y : Int) : c.hv intEq [int x, int y] = some (bool (decide (x = y))) := hv_of_value rfl
theorem fhv_intNe (x y : Int) : c.hv intNe [int x, int y] = some (bool (decide (x ≠ y))) := hv_of_value rfl
theorem fhv_intGe (x y : Int) : c.hv intGe [int x, int y] = some (bool (decide (x ≥ y))) := hv_of_value rfl
theorem fhv_intMin (x y : Int) : c.hv intMin [int x, int y] = some (int (min x y)) := hv_of_value rfl
theorem fhv_boolNot (a : Bool) : c.hv boolNot [bool a] = some (bool !a) := hv_of_value rfl
theorem fhv_boolAnd (a b : Bool) : c.hv boolAnd [bool a, bool b] = some (bool (a && b)) := hv_of_value rfl

theorem fq_dv_bool (b : Bool) : GroundTerm.dv Srt.bool (.bool b) = bool b := rfl

end

/-- Evaluates a function-form equation's sides at a substitution, given the values of its
variables as rewriting facts. -/
syntax "fq_eval" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| fq_eval [$ls,*]) => `(tactic| simp only [FnEqn.lhs, FnEqn.xTerms, val, valList, allSome,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, Option.bind_some, Option.map_some, fqB, intT,
      dv_int, fq_dv_bool, $ls,*])

/-! ## 1453: `I1 =/=Int I2 => notBool (I1 ==Int I2)` -/

def fnNeInt : FnEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], intNe, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.bool,
    none, .app boolNot [.app intEq [.var 0, .var 1]]⟩

theorem fnNeInt_holds {c : Semantics} (hs : c.shapesOK = true) : fnNeInt.Holds c := by
  intro σ hσ _ hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI1") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (int x) := h2.symm.trans hx
  have h3' : σ.lookup 3 = some (int y) := h3.symm.trans hy
  fq_eval [fnNeInt, h2', h3', hx, hy, fhv_intNe, fhv_intEq, fhv_boolNot]
  simp

theorem fnNeInt_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnNeInt.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnNeInt (by decide) (by rfl) (fnNeInt_holds hs) ad hp hsv

/-! ## 1450, 1451: `minInt(I1, I2) => I1 requires I1 <Int I2`, `=> I2 requires I1 >=Int I2` -/

def fnMinLt : FnEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], intMin, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.int,
    some (.app intLt [.var 0, .var 1]), .var 0⟩

def fnMinGe : FnEqn :=
  ⟨[("VarI1", Srt.int), ("VarI2", Srt.int)], intMin, [(Srt.int, .var 0, none), (Srt.int, .var 1, none)], Srt.int,
    some (.app intGe [.var 0, .var 1]), .var 1⟩

theorem fnMinLt_holds {c : Semantics} (hs : c.shapesOK = true) : fnMinLt.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI1") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (int x) := h2.symm.trans hx
  have h3' : σ.lookup 3 = some (int y) := h3.symm.trans hy
  have hq := hreq _ rfl
  simp only [val, valList, allSome, hx, hy, Option.bind_some, Option.map_some, hv_intLt, Option.some.injEq] at hq
  have hb : x < y := of_decide_eq_true (fq_bool_inj hq)
  fq_eval [fnMinLt, h2', h3', hx, hy, fhv_intMin]
  have : min x y = x := by omega
  rw [this]

theorem fnMinGe_holds {c : Semantics} (hs : c.shapesOK = true) : fnMinGe.Holds c := by
  intro σ hσ hreq hm
  obtain ⟨x, hx⟩ := int_at hs hσ 0 (n := "VarI1") rfl
  obtain ⟨y, hy⟩ := int_at hs hσ 1 (n := "VarI2") rfl
  obtain ⟨h2, -, h3, -⟩ := hm
  rw [fq_val_var] at h2 h3
  have h2' : σ.lookup 2 = some (int x) := h2.symm.trans hx
  have h3' : σ.lookup 3 = some (int y) := h3.symm.trans hy
  have hq := hreq _ rfl
  simp only [val, valList, allSome, hx, hy, Option.bind_some, Option.map_some, fhv_intGe, Option.some.injEq] at hq
  have hb : x ≥ y := of_decide_eq_true (fq_bool_inj hq)
  fq_eval [fnMinGe, h2', h3', hx, hy, fhv_intMin]
  have : min x y = y := by omega
  rw [this]

theorem fnMinLt_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnMinLt.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnMinLt (by decide) (by rfl) (fnMinLt_holds hs) ad hp hsv

theorem fnMinGe_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnMinGe.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnMinGe (by decide) (by rfl) (fnMinGe_holds hs) ad hp hsv

/-! ## `false #as _Gen1 f _Gen0 => _Gen1`, for a Bool symbol `f` that is `false` at `false` -/

/-- `f(false #as _Gen1, _Gen0) => _Gen1`. -/
def fnBAs (f : Sym) : FnEqn :=
  ⟨[("Var'Unds'Gen1", Srt.bool), ("Var'Unds'Gen0", Srt.bool)], f,
    [(Srt.bool, fqB false, some 0), (Srt.bool, .var 1, none)], Srt.bool, none, .var 0⟩

theorem fnBAs_holds {c : Semantics} (hs : c.shapesOK = true) {f : Sym} {op : Bool → Bool → Bool}
    (hf : ∀ a b, c.hv f [bool a, bool b] = some (bool (op a b))) (hop : ∀ x, op false x = false) :
    (fnBAs f).Holds c := by
  intro σ hσ _ hm
  obtain ⟨y, hy⟩ := fq_bool_at hs hσ 1 (n := "Var'Unds'Gen0") rfl
  obtain ⟨h2, has, h3, -⟩ := hm
  rw [fq_val_var] at h3
  have h2' : σ.lookup 2 = some (bool false) := h2.symm
  have h0 : σ.lookup 0 = some (bool false) := (has 0 rfl).trans h2'
  have h3' : σ.lookup 3 = some (bool y) := h3.symm.trans hy
  fq_eval [fnBAs, h2', h3', h0, hf, hop]

/-- 1143: `false #as _Gen1 andBool _Gen0 => _Gen1`. -/
def fnAndFalse : FnEqn := fnBAs boolAnd

theorem fnAndFalse_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnAndFalse.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_reg h fnAndFalse (by decide) (by rfl) (fnBAs_holds hs fhv_boolAnd (fun _ => rfl)) ad hp hsv

end LibEv

end KCore
